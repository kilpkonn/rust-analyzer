use hir_ty::db::HirDatabase;
use rustc_hash::FxHashSet;

use crate::{Module, ScopeDef, Type};

pub mod type_tree;
pub use type_tree::{TypeInhabitant, TypeTransformation, TypeTree};

mod tactics;

const MAX_VARIATIONS: usize = 10;

/// Lookup table for term search
struct LookupTable {
    // Use FxHashMap instead? not sure how to correctly hash Type tho
    data: Vec<(Type, FxHashSet<TypeTree>)>,
    new_types: Vec<Type>,
}

impl LookupTable {
    pub fn new() -> Self {
        LookupTable { data: Default::default(), new_types: Vec::new() }
    }

    pub fn find(&self, db: &dyn HirDatabase, ty: &Type) -> Option<Vec<TypeTree>> {
        self.data
            .iter()
            .find(|(t, _)| t.could_unify_with_normalized(db, ty))
            .map(|(_, tts)| tts.iter().cloned().collect())
    }

    pub fn insert(
        &mut self,
        db: &dyn HirDatabase,
        ty: Type,
        trees: impl Iterator<Item = TypeTree>,
    ) {
        match self.data.iter().position(|it| it.0.could_unify_with_normalized(db, &ty)) {
            Some(pos) => self.data[pos].1.extend(trees.take(MAX_VARIATIONS)),
            None => {
                self.data.push((ty.clone(), trees.take(MAX_VARIATIONS).collect()));
                self.new_types.push(ty);
            }
        }
    }

    pub fn new_types(&mut self) -> Vec<Type> {
        std::mem::take(&mut self.new_types)
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

    for _ in 0..2 {
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
