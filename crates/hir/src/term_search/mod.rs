use std::iter;

use hir_ty::db::HirDatabase;
use itertools::Itertools;
use rustc_hash::FxHashSet;

use crate::{Adt, AssocItem, GenericParam, Impl, ModuleDef, ScopeDef, Type};

pub mod type_tree;
pub use type_tree::{TypeInhabitant, TypeTransformation, TypeTree};

pub fn term_search(
    goal: &Type,
    defs: &FxHashSet<ScopeDef>,
    db: &dyn HirDatabase,
) -> Vec<(u32, TypeTree)> {
    dfs_term_search(goal, defs, db, 1)
}

fn dfs_search_assoc_item(
    tt: &TypeTree,
    goal: &Type,
    defs: &FxHashSet<ScopeDef>,
    db: &dyn HirDatabase,
    depth: u32,
) -> Vec<(u32, TypeTree)> {
    if depth == 0 {
        return Vec::new();
    }

    Impl::all_for_type(db, tt.ty(db))
        .into_iter()
        .flat_map(|imp| {
            imp.items(db)
                .into_iter()
                .filter_map(|it| match it {
                    AssocItem::Function(f) => Some(f),
                    _ => None,
                })
                .flat_map(move |func| {
                    let param_trees: Vec<Vec<(u32, TypeTree)>> =
                        iter::once(vec![(depth, tt.clone())])
                            .chain(func.params_without_self(db).into_iter().map(|param| {
                                let tts =
                                    dfs_term_search(param.ty(), defs, db, depth.saturating_sub(1));
                                let max = tts.iter().map(|(d, _)| *d).max().unwrap_or(0);
                                tts.into_iter().filter(|(d, _)| *d >= max).collect()
                            }))
                            .collect();

                    // let mut new_tts: Vec<(u32, TypeTree)> = param_trees
                    //     .into_iter()
                    //     .multi_cartesian_product()
                    //     .map(|params| {
                    //         (
                    //             params.iter().map(|(d, _)| *d).min().unwrap_or(0),
                    //             TypeTree::TypeTransformation {
                    //                 func: TypeTransformation::Function(func),
                    //                 params: params.into_iter().map(|(_, p)| p).collect(),
                    //             },
                    //         )
                    //     })
                    //     .collect();
                    let mut new_tts = build_permutations(
                        param_trees.into_iter(),
                        TypeTransformation::Function(func),
                    );

                    let rec_res: Vec<(u32, TypeTree)> = new_tts
                        .iter()
                        .flat_map(|(d, new_tt)| {
                            dfs_search_assoc_item(&new_tt, goal, defs, db, d.saturating_sub(1))
                                .into_iter()
                        })
                        .collect();

                    new_tts.extend(rec_res);
                    Some(new_tts)
                })
        })
        .flatten()
        .unique()
        .filter(|(_, tt)| tt.ty(db).could_unify_with_normalized(db, goal))
        .collect()
}

fn dfs_term_search(
    goal: &Type,
    defs: &FxHashSet<ScopeDef>,
    db: &dyn HirDatabase,
    depth: u32,
) -> Vec<(u32, TypeTree)> {
    if depth == 0 {
        return Vec::new();
    }

    let mut res = Vec::new();

    for def in defs {
        match def {
            ScopeDef::ModuleDef(ModuleDef::Const(it)) => {
                let tt = TypeTree::TypeInhabitant(TypeInhabitant::Const(*it));
                if it.ty(db).could_unify_with_normalized(db, goal) {
                    res.push((depth, tt));
                } else {
                    res.extend(dfs_search_assoc_item(&tt, goal, defs, db, depth.saturating_sub(1)));
                    res.extend(matching_struct_fields(db, &tt, goal, depth))
                }
            }
            ScopeDef::ModuleDef(ModuleDef::Static(it)) => {
                let tt = TypeTree::TypeInhabitant(TypeInhabitant::Static(*it));
                if it.ty(db).could_unify_with_normalized(db, goal) {
                    res.push((depth, tt));
                } else {
                    res.extend(dfs_search_assoc_item(&tt, goal, defs, db, depth.saturating_sub(1)));
                    res.extend(matching_struct_fields(db, &tt, goal, depth))
                }
            }
            ScopeDef::GenericParam(GenericParam::ConstParam(it)) => {
                if it.ty(db).could_unify_with_normalized(db, goal) {
                    res.push((depth, TypeTree::TypeInhabitant(TypeInhabitant::ConstParam(*it))));
                } else {
                    res.extend(dfs_search_assoc_item(
                        &TypeTree::TypeInhabitant(TypeInhabitant::ConstParam(*it)),
                        goal,
                        defs,
                        db,
                        depth.saturating_sub(1),
                    ));
                }
            }
            ScopeDef::Local(it) => {
                let tt = TypeTree::TypeInhabitant(TypeInhabitant::Local(*it));
                if it.ty(db).could_unify_with_normalized(db, goal) {
                    res.push((depth, tt));
                } else {
                    res.extend(dfs_search_assoc_item(&tt, goal, defs, db, depth.saturating_sub(1)));
                    res.extend(matching_struct_fields(db, &tt, goal, depth))
                }
            }
            ScopeDef::ImplSelfType(it) => {
                let tt = TypeTree::TypeInhabitant(TypeInhabitant::SelfParam(*it));
                if it.self_ty(db).could_unify_with_normalized(db, goal) {
                    res.push((depth, tt));
                } else {
                    // res.extend(dfs_search_assoc_item(&tt, goal, defs, db, depth.saturating_sub(1)));
                    // res.extend(matching_struct_fields(db, &tt, goal, depth))
                }
            }
            ScopeDef::ModuleDef(ModuleDef::Function(it)) => {
                if it.ret_type(db).could_unify_with_normalized(db, goal) {
                    let param_trees = it.assoc_fn_params(db).into_iter().map(|param| {
                        dfs_term_search(param.ty(), defs, db, depth.saturating_sub(1))
                    });
                    res.extend(build_permutations(param_trees, TypeTransformation::Function(*it)));
                }
            }
            ScopeDef::ModuleDef(ModuleDef::Variant(it)) => {
                if it.parent_enum(db).ty(db).could_unify_with_normalized(db, goal) {
                    let param_trees = it.fields(db).into_iter().map(|field| {
                        dfs_term_search(&field.ty(db), defs, db, depth.saturating_sub(1))
                    });
                    res.extend(build_permutations(param_trees, TypeTransformation::Variant(*it)));
                }
            }
            ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Enum(it))) => {
                for variant in it.variants(db) {
                    if it.ty(db).could_unify_with_normalized(db, goal) {
                        let param_trees = variant.fields(db).into_iter().map(|field| {
                            dfs_term_search(&field.ty(db), defs, db, depth.saturating_sub(1))
                        });

                        res.extend(build_permutations(
                            param_trees,
                            TypeTransformation::Variant(variant),
                        ));
                    }
                }
            }
            ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Struct(it))) => {
                if it.ty(db).could_unify_with_normalized(db, goal) {
                    let param_trees = it.fields(db).into_iter().map(|strukt| {
                        dfs_term_search(&strukt.ty(db), defs, db, depth.saturating_sub(1))
                    });
                    res.extend(build_permutations(param_trees, TypeTransformation::Struct(*it)));
                }
            }
            _ => (),
        }
    }
    res.into_iter().unique().collect()
}

fn matching_struct_fields(
    db: &dyn HirDatabase,
    tt: &TypeTree,
    goal: &Type,
    depth: u32,
) -> Vec<(u32, TypeTree)> {
    tt.ty(db)
        .fields(db)
        .into_iter()
        .filter(|(_, ty)| ty.could_unify_with_normalized(db, goal))
        .map(|(field, _)| {
            (
                depth,
                TypeTree::TypeTransformation {
                    func: TypeTransformation::Field(field),
                    params: vec![tt.clone()],
                },
            )
        })
        .collect()
}

fn build_permutations(
    param_trees: impl Iterator<Item = Vec<(u32, TypeTree)>>,
    tt: TypeTransformation,
) -> Vec<(u32, TypeTree)> {
    // Extra case for transformations with 0 params
    let (param_trees, count_tree) = param_trees.tee();
    if count_tree.count() == 0 {
        return vec![(0, TypeTree::TypeTransformation { func: tt.clone(), params: Vec::new() })];
    }

    let mut max_depth = 0;
    param_trees
        .multi_cartesian_product()
        .filter_map(move |params| {
            let depth = params.iter().map(|(d, _)| *d).min().unwrap_or(0);
            if depth < max_depth {
                return None;
            }
            max_depth = depth;
            Some((
                depth,
                TypeTree::TypeTransformation {
                    func: tt.clone(),
                    params: params.into_iter().map(|(_, p)| p).collect(),
                },
            ))
        })
        .filter(|(d, _)| *d >= max_depth)
        .collect()
}
