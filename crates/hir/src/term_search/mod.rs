use hir_ty::db::HirDatabase;
use rustc_hash::FxHashSet;

use crate::{Module, ScopeDef, Type};

pub mod type_tree;
pub use type_tree::{TypeInhabitant, TypeTransformation, TypeTree};

mod tactics;

/// Lookup table for term search
///
/// Structure is (Type, TypeTrees) where `TypeTrees` is a `Vec<TypeTree>` that all unify with the
/// type give in Type.
struct LookupTable(Vec<(Type, Vec<TypeTree>)>);

// TODO: Add tracking for new types
// TODO: Figure out how to avoid duplicates
impl LookupTable {
    pub fn new() -> Self {
        LookupTable(Vec::new())
    }

    // pub fn exists(&self, db: &dyn HirDatabase, ty: &Type) -> bool {
    //     self.0.iter().any(|it| it.0.could_unify_with_normalized(db, ty))
    // }

    pub fn find(&self, db: &dyn HirDatabase, ty: &Type) -> Option<Vec<TypeTree>> {
        self.0
            .iter()
            .find(|(t, _)| t.could_unify_with_normalized(db, ty))
            .map(|(_, tts)| tts)
            .cloned()
    }

    pub fn insert(&mut self, db: &dyn HirDatabase, ty: Type, trees: Vec<TypeTree>) {
        match self.0.iter().position(|it| it.0.could_unify_with_normalized(db, &ty)) {
            Some(pos) => self.0[pos].1.extend(trees),
            None => self.0.push((ty, trees)),
        }
    }

    pub fn types(&self) -> Vec<Type> {
        self.0.iter().map(|(ty, _)| ty.clone()).collect()
    }
}

pub fn term_search(
    db: &dyn HirDatabase,
    module: Module,
    defs: &FxHashSet<ScopeDef>,
    goal: &Type,
) -> Vec<TypeTree> {
    let mut lookup = LookupTable::new();

    // Try trivial tactic first, also populates lookup table
    let mut solutions: Vec<TypeTree> = tactics::trivial(db, defs, &mut lookup, goal).collect();
    let mut solution_found = !solutions.is_empty();

    for _ in 0..10 {
        solutions.extend(tactics::type_constructor(db, &module, defs, &mut lookup, goal));
        solutions.extend(tactics::free_function(db, &module, defs, &mut lookup, goal));
        solutions.extend(tactics::impl_method(db, &module, defs, &mut lookup, goal));

        if solution_found {
            break;
        }

        solution_found = !solutions.is_empty();
    }

    solutions
}
