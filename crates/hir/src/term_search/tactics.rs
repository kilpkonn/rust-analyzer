use hir_ty::db::HirDatabase;
use itertools::Itertools;
use rustc_hash::FxHashSet;

use crate::{
    Adt, AssocItem, GenericParam, HasVisibility, Impl, Module, ModuleDef, ScopeDef, Type, Variant,
};

use crate::term_search::{TypeInhabitant, TypeTransformation, TypeTree};

use super::{LookupTable, MAX_VARIATIONS};

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
    defs.iter()
        .filter_map(|def| match def {
            ScopeDef::ModuleDef(ModuleDef::Const(it)) => {
                Some(TypeTree::TypeInhabitant(TypeInhabitant::Const(*it)))
            }
            ScopeDef::ModuleDef(ModuleDef::Static(it)) => {
                Some(TypeTree::TypeInhabitant(TypeInhabitant::Static(*it)))
            }
            ScopeDef::GenericParam(GenericParam::ConstParam(it)) => {
                Some(TypeTree::TypeInhabitant(TypeInhabitant::ConstParam(*it)))
            }
            ScopeDef::Local(it) => Some(TypeTree::TypeInhabitant(TypeInhabitant::Local(*it))),
            ScopeDef::ImplSelfType(it) => {
                Some(TypeTree::TypeInhabitant(TypeInhabitant::SelfParam(*it)))
            }
            _ => None,
        })
        .filter_map(|it| {
            let ty = it.ty(db);
            lookup.insert(db, ty.clone(), std::iter::once(it.clone()));

            ty.could_unify_with_normalized(db, goal).then(|| it)
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
        enum_ty: Type,
        variant: Variant,
    ) -> Vec<TypeTree> {
        let param_trees: Option<Vec<Vec<TypeTree>>> =
            variant.fields(db).into_iter().map(|field| lookup.find(db, &field.ty(db))).collect();

        // Check if all fields can be completed from lookup table
        let param_trees = match param_trees {
            Some(it) => it,
            None => return Vec::new(),
        };

        // Note that we need special case for 0 param constructors because of multi cartesian
        // product
        let variant_trees: Vec<TypeTree> = if param_trees.is_empty() {
            vec![TypeTree::TypeTransformation {
                func: TypeTransformation::Variant(variant),
                params: Vec::new(),
            }]
        } else {
            param_trees
                .into_iter()
                .multi_cartesian_product()
                .take(MAX_VARIATIONS)
                .map(|params| TypeTree::TypeTransformation {
                    func: TypeTransformation::Variant(variant),
                    params,
                })
                .collect()
        };

        lookup.insert(db, enum_ty.clone(), variant_trees.iter().cloned());
        variant_trees
    }

    defs.iter()
        .filter_map(|def| match def {
            ScopeDef::ModuleDef(ModuleDef::Variant(it)) => {
                let enum_ty = it.parent_enum(db).ty(db);

                let variant_trees = variant_helper(db, lookup, enum_ty.clone(), *it);
                Some((enum_ty, variant_trees))
            }
            ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Enum(it))) => {
                let enum_ty = it.ty(db);

                let trees = it
                    .variants(db)
                    .into_iter()
                    .flat_map(|it| variant_helper(db, lookup, enum_ty.clone(), it))
                    .collect();

                Some((enum_ty, trees))
            }
            ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Struct(it))) => {
                let struct_ty = it.ty(db);
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
                        func: TypeTransformation::Struct(*it),
                        params: Vec::new(),
                    }]
                } else {
                    param_trees
                        .into_iter()
                        .multi_cartesian_product()
                        .take(MAX_VARIATIONS)
                        .map(|params| TypeTree::TypeTransformation {
                            func: TypeTransformation::Struct(*it),
                            params,
                        })
                        .collect()
                };

                lookup.insert(db, struct_ty.clone(), struct_trees.iter().cloned());
                Some((struct_ty, struct_trees))
            }
            _ => None,
        })
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
                if !it.is_visible_from(db, *module) || it.is_unsafe_to_call(db) {
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
                lookup.insert(db, ret_ty.clone(), fn_trees.iter().cloned());
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
        .new_types()
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
            if !it.is_visible_from(db, *module) || it.is_unsafe_to_call(db) {
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

            let ret_ty = it.ret_type(db);
            lookup.insert(db, ret_ty.clone(), fn_trees.iter().cloned());
            Some((ret_ty, fn_trees))
        })
        .filter_map(|(ty, trees)| ty.could_unify_with_normalized(db, goal).then(|| trees))
        .flatten()
}
