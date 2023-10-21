use hir_ty::db::HirDatabase;
use rustc_hash::FxHashSet;

use crate::{GenericParam, ModuleDef, ScopeDef, Type};

use crate::term_search::{TypeInhabitant, TypeTree};

/// # Trivial tactic
///
/// Attempts to fulfill the goal by trying items in scope
pub(super) fn trivial<'a>(
    goal: &'a Type,
    defs: &'a FxHashSet<ScopeDef>,
    db: &'a dyn HirDatabase,
) -> impl Iterator<Item = TypeTree> + 'a {
    defs.iter().filter_map(|def| match def {
        ScopeDef::ModuleDef(ModuleDef::Const(it)) => {
            match it.ty(db).could_unify_with_normalized(db, goal) {
                true => Some(TypeTree::TypeInhabitant(TypeInhabitant::Const(*it))),
                false => None,
            }
        }
        ScopeDef::ModuleDef(ModuleDef::Static(it)) => {
            match it.ty(db).could_unify_with_normalized(db, goal) {
                true => Some(TypeTree::TypeInhabitant(TypeInhabitant::Static(*it))),
                false => None,
            }
        }
        ScopeDef::GenericParam(GenericParam::ConstParam(it)) => {
            match it.ty(db).could_unify_with_normalized(db, goal) {
                true => Some(TypeTree::TypeInhabitant(TypeInhabitant::ConstParam(*it))),
                false => None,
            }
        }
        ScopeDef::Local(it) => match it.ty(db).could_unify_with_normalized(db, goal) {
            true => Some(TypeTree::TypeInhabitant(TypeInhabitant::Local(*it))),
            false => None,
        },
        ScopeDef::ImplSelfType(it) => match it.self_ty(db).could_unify_with_normalized(db, goal) {
            true => Some(TypeTree::TypeInhabitant(TypeInhabitant::SelfParam(*it))),
            false => None,
        },
        _ => None,
    })
}
