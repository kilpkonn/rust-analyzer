use hir_ty::db::HirDatabase;
use itertools::Itertools;
use rustc_hash::FxHashSet;

use crate::{
    Adt, AssocItem, Enum, GenericParam, HasVisibility, Impl, Module, ModuleDef, ScopeDef, Type,
    Variant,
};

use crate::term_search::{TypeInhabitant, TypeTransformation, TypeTree};

use super::{LookupTable, NewTypesKey, MAX_VARIATIONS};

/// Trivial tactic
///
/// Attempts to fulfill the goal by trying items in scope
/// Also works as a starting point to move all items in scope to lookup table
pub(super) fn trivial<'a>(
    db: &'a dyn HirDatabase,
    defs: &'a FxHashSet<ScopeDef>,
    lookup: &'a mut LookupTable,
    goal: &'a Type,
) -> impl Iterator<Item = TypeTree> + 'a {
    defs.iter().filter_map(|def| {
        let tt = match def {
            ScopeDef::ModuleDef(ModuleDef::Const(it)) => {
                Some(TypeTree::TypeInhabitant(TypeInhabitant::Const(*it)))
            }
            ScopeDef::ModuleDef(ModuleDef::Static(it)) => {
                Some(TypeTree::TypeInhabitant(TypeInhabitant::Static(*it)))
            }
            ScopeDef::GenericParam(GenericParam::ConstParam(it)) => {
                Some(TypeTree::TypeInhabitant(TypeInhabitant::ConstParam(*it)))
            }
            ScopeDef::Local(it) => {
                let borrowck = db.borrowck(it.parent).ok()?;

                let invalid = borrowck.iter().any(|b| {
                    b.partially_moved.iter().any(|moved| {
                        Some(&moved.local) == b.mir_body.binding_locals.get(it.binding_id)
                    })
                });

                if invalid {
                    return None;
                }

                Some(TypeTree::TypeInhabitant(TypeInhabitant::Local(*it)))
            }
            _ => None,
        }?;

        lookup.mark_exhausted(*def);

        let ty = tt.ty(db);
        lookup.insert(ty.clone(), std::iter::once(tt.clone()));

        ty.could_unify_with_normalized(db, goal).then(|| tt)
    })
}

/// Type constructor tactic
///
/// Attempts different type constructors for enums and structs in scope
///
/// # Arguments
/// * `db` - HIR database
/// * `module` - Module where the term search target location
/// * `defs` - Set of items in scope at term search target location
/// * `lookup` - Lookup table for types
/// * `goal` - Term search target type
pub(super) fn type_constructor<'a>(
    db: &'a dyn HirDatabase,
    module: &'a Module,
    defs: &'a FxHashSet<ScopeDef>,
    lookup: &'a mut LookupTable,
    goal: &'a Type,
) -> impl Iterator<Item = TypeTree> + 'a {
    fn variant_helper(
        db: &dyn HirDatabase,
        lookup: &mut LookupTable,
        parent_enum: Enum,
        variant: Variant,
        goal: &Type,
    ) -> Vec<(Type, Vec<TypeTree>)> {
        let generics = db.generic_params(variant.parent.id.into());
        let generic_params = lookup
            .iter_types()
            .collect::<Vec<_>>() // Force take ownership
            .into_iter()
            .permutations(generics.type_or_consts.len());

        generic_params
            .filter_map(|generics| {
                let enum_ty = parent_enum.ty_with_generics(db, &generics);

                if !generics.is_empty() && !enum_ty.could_unify_with_normalized(db, goal) {
                    return None;
                }

                // Early exit if some param cannot be filled from lookup
                let param_trees: Vec<Vec<TypeTree>> = variant
                    .fields(db)
                    .into_iter()
                    .map(|field| lookup.find(db, &field.ty_with_generics(db, &generics)))
                    .collect::<Option<_>>()?;

                // Note that we need special case for 0 param constructors because of multi cartesian
                // product
                let variant_trees: Vec<TypeTree> = if param_trees.is_empty() {
                    vec![TypeTree::TypeTransformation {
                        func: TypeTransformation::Variant { variant, generics: generics.clone() },
                        params: Vec::new(),
                    }]
                } else {
                    param_trees
                        .into_iter()
                        .multi_cartesian_product()
                        .take(MAX_VARIATIONS)
                        .map(|params| TypeTree::TypeTransformation {
                            func: TypeTransformation::Variant {
                                variant,
                                generics: generics.clone(),
                            },
                            params,
                        })
                        .collect()
                };
                lookup.insert(enum_ty.clone(), variant_trees.iter().cloned());

                Some((enum_ty, variant_trees))
            })
            .collect()
    }
    defs.iter()
        .filter_map(|def| match def {
            ScopeDef::ModuleDef(ModuleDef::Variant(it)) => {
                let variant_trees = variant_helper(db, lookup, it.parent_enum(db), *it, goal);
                if variant_trees.is_empty() {
                    return None;
                }
                lookup.mark_fulfilled(ScopeDef::ModuleDef(ModuleDef::Variant(*it)));
                Some(variant_trees)
            }
            ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Enum(enum_))) => {
                let trees: Vec<(Type, Vec<TypeTree>)> = enum_
                    .variants(db)
                    .into_iter()
                    .flat_map(|it| variant_helper(db, lookup, enum_.clone(), it, goal))
                    .collect();

                if !trees.is_empty() {
                    lookup.mark_fulfilled(ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Enum(*enum_))));
                }

                Some(trees)
            }
            ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Struct(it))) => {
                let generics = db.generic_params(it.id.into());
                let generic_params = lookup
                    .iter_types()
                    .collect::<Vec<_>>() // Force take ownership
                    .into_iter()
                    .permutations(generics.type_or_consts.len());

                let trees = generic_params
                    .filter_map(|generics| {
                        let struct_ty = it.ty_with_generics(db, &generics);
                        if !generics.is_empty() && !struct_ty.could_unify_with_normalized(db, goal)
                        {
                            return None;
                        }
                        let fileds = it.fields(db);
                        // Check if all fields are visible, otherwise we cannot fill them
                        if fileds.iter().any(|it| !it.is_visible_from(db, *module)) {
                            return None;
                        }

                        // Early exit if some param cannot be filled from lookup
                        let param_trees: Vec<Vec<TypeTree>> = fileds
                            .into_iter()
                            .map(|field| lookup.find(db, &field.ty(db)))
                            .collect::<Option<_>>()?;

                        // Note that we need special case for 0 param constructors because of multi cartesian
                        // product
                        let struct_trees: Vec<TypeTree> = if param_trees.is_empty() {
                            vec![TypeTree::TypeTransformation {
                                func: TypeTransformation::Struct { strukt: *it, generics },
                                params: Vec::new(),
                            }]
                        } else {
                            param_trees
                                .into_iter()
                                .multi_cartesian_product()
                                .take(MAX_VARIATIONS)
                                .map(|params| TypeTree::TypeTransformation {
                                    func: TypeTransformation::Struct {
                                        strukt: *it,
                                        generics: generics.clone(),
                                    },
                                    params,
                                })
                                .collect()
                        };

                        lookup
                            .mark_fulfilled(ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Struct(*it))));
                        lookup.insert(struct_ty.clone(), struct_trees.iter().cloned());

                        Some((struct_ty, struct_trees))
                    })
                    .collect();
                Some(trees)
            }
            _ => None,
        })
        .flatten()
        .filter_map(|(ty, trees)| ty.could_unify_with_normalized(db, goal).then(|| trees))
        .flatten()
}

/// Free function tactic
///
/// Attempts to call different functions in scope with parameters from lookup table
///
/// # Arguments
/// * `db` - HIR database
/// * `module` - Module where the term search target location
/// * `defs` - Set of items in scope at term search target location
/// * `lookup` - Lookup table for types
/// * `goal` - Term search target type
pub(super) fn free_function<'a>(
    db: &'a dyn HirDatabase,
    module: &'a Module,
    defs: &'a FxHashSet<ScopeDef>,
    lookup: &'a mut LookupTable,
    goal: &'a Type,
) -> impl Iterator<Item = TypeTree> + 'a {
    defs.iter()
        .filter_map(|def| match def {
            ScopeDef::ModuleDef(ModuleDef::Function(it)) => {
                // Filter out private and unsafe functions
                if !it.is_visible_from(db, *module)
                    || it.is_unsafe_to_call(db)
                    || it.is_unstable(db)
                {
                    return None;
                }

                // Early exit if some param cannot be filled from lookup
                let param_trees: Vec<Vec<TypeTree>> = it
                    .params_without_self(db)
                    .into_iter()
                    .map(|field| lookup.find(db, &field.ty()))
                    .collect::<Option<_>>()?;

                // Note that we need special case for 0 param constructors because of multi cartesian
                // product
                let fn_trees: Vec<TypeTree> = if param_trees.is_empty() {
                    vec![TypeTree::TypeTransformation {
                        func: TypeTransformation::Function(*it),
                        params: Vec::new(),
                    }]
                } else {
                    param_trees
                        .into_iter()
                        .multi_cartesian_product()
                        .take(MAX_VARIATIONS)
                        .map(|params| TypeTree::TypeTransformation {
                            func: TypeTransformation::Function(*it),
                            params,
                        })
                        .collect()
                };

                let ret_ty = it.ret_type(db);
                lookup.mark_fulfilled(ScopeDef::ModuleDef(ModuleDef::Function(*it)));
                lookup.insert(ret_ty.clone(), fn_trees.iter().cloned());
                Some((ret_ty, fn_trees))
            }
            _ => None,
        })
        .filter_map(|(ty, trees)| ty.could_unify_with_normalized(db, goal).then(|| trees))
        .flatten()
}

/// Impl method tactic
///
/// Attempts to to call methods on types from lookup table.
/// This includes both functions from direct impl blocks as well as functions from traits.
///
/// # Arguments
/// * `db` - HIR database
/// * `module` - Module where the term search target location
/// * `defs` - Set of items in scope at term search target location
/// * `lookup` - Lookup table for types
/// * `goal` - Term search target type
pub(super) fn impl_method<'a>(
    db: &'a dyn HirDatabase,
    module: &'a Module,
    _defs: &'a FxHashSet<ScopeDef>,
    lookup: &'a mut LookupTable,
    goal: &'a Type,
) -> impl Iterator<Item = TypeTree> + 'a {
    lookup
        .new_types(NewTypesKey::ImplMethod)
        .into_iter()
        .flat_map(|ty| {
            Impl::all_for_type(db, ty.clone()).into_iter().map(move |imp| (ty.clone(), imp))
        })
        .flat_map(|(ty, imp)| imp.items(db).into_iter().map(move |item| (ty.clone(), item)))
        .filter_map(|(ty, it)| match it {
            AssocItem::Function(f) => Some((ty, f)),
            _ => None,
        })
        .filter_map(|(ty, it)| {
            // Filter out private and unsafe functions
            if !it.is_visible_from(db, *module) || it.is_unsafe_to_call(db) || it.is_unstable(db) {
                return None;
            }

            // Ignore functions without self param
            if !it.has_self_param(db) {
                return None;
            }

            let ret_ty = it.ret_type(db);
            // Ignore functions that do not change the type
            if ty.could_unify_with_normalized(db, &ret_ty) {
                return None;
            }

            let self_ty = it.self_param(db).expect("No self param").ty(db);

            // Ignore functions that have different self type
            if !self_ty.autoderef(db).any(|s_ty| ty.could_unify_with_normalized(db, &s_ty)) {
                return None;
            }

            let target_type_trees = lookup.find(db, &ty).expect("Type not in lookup");

            // Early exit if some param cannot be filled from lookup
            let param_trees: Vec<Vec<TypeTree>> = it
                .params_without_self(db)
                .into_iter()
                .map(|field| lookup.find(db, &field.ty()))
                .collect::<Option<_>>()?;

            let fn_trees: Vec<TypeTree> = std::iter::once(target_type_trees)
                .chain(param_trees.into_iter())
                .multi_cartesian_product()
                .take(MAX_VARIATIONS)
                .map(|params| TypeTree::TypeTransformation {
                    func: TypeTransformation::Function(it),
                    params,
                })
                .collect();

            lookup.insert(ret_ty.clone(), fn_trees.iter().cloned());
            Some((ret_ty, fn_trees))
        })
        .filter_map(|(ty, trees)| ty.could_unify_with_normalized(db, goal).then(|| trees))
        .flatten()
}

/// Struct projection tactic
///
/// Attempts different struct fields
///
/// # Arguments
/// * `db` - HIR database
/// * `module` - Module where the term search target location
/// * `defs` - Set of items in scope at term search target location
/// * `lookup` - Lookup table for types
/// * `goal` - Term search target type
pub(super) fn struct_projection<'a>(
    db: &'a dyn HirDatabase,
    module: &'a Module,
    _defs: &'a FxHashSet<ScopeDef>,
    lookup: &'a mut LookupTable,
    goal: &'a Type,
) -> impl Iterator<Item = TypeTree> + 'a {
    lookup
        .new_types(NewTypesKey::StructProjection)
        .into_iter()
        .map(|ty| (ty.clone(), lookup.find(db, &ty).expect("TypeTree not in lookup")))
        .flat_map(move |(ty, targets)| {
            let module = module.clone();
            ty.fields(db).into_iter().filter_map(move |(field, filed_ty)| {
                if !field.is_visible_from(db, module) {
                    return None;
                }
                let trees =
                    targets.clone().into_iter().map(move |target| TypeTree::TypeTransformation {
                        func: TypeTransformation::Field(field),
                        params: vec![target],
                    });
                Some((filed_ty, trees))
            })
        })
        .filter_map(|(ty, trees)| ty.could_unify_with_normalized(db, goal).then(|| trees))
        .flatten()
}
