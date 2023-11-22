use hir_ty::db::HirDatabase;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{Module, ScopeDef, Semantics, Type};

pub mod type_tree;
pub use type_tree::{TypeInhabitant, TypeTransformation, TypeTree};

mod tactics;

const MAX_VARIATIONS: usize = 10;

#[derive(Debug, Hash, PartialEq, Eq)]
enum NewTypesKey {
    ImplMethod,
    StructProjection,
}

/// Lookup table for term search
#[derive(Default, Debug)]
struct LookupTable {
    data: FxHashMap<Type, FxHashSet<TypeTree>>,
    new_types: FxHashMap<NewTypesKey, Vec<Type>>,
    exhausted_scopedefs: FxHashSet<ScopeDef>,
    round_scopedef_hits: FxHashSet<ScopeDef>,
    scopedef_hits: FxHashMap<ScopeDef, u32>,
}

impl LookupTable {
    pub fn new() -> Self {
        let mut res: Self = Default::default();
        res.new_types.insert(NewTypesKey::ImplMethod, Vec::new());
        res.new_types.insert(NewTypesKey::StructProjection, Vec::new());
        res
    }

    pub fn find(&self, db: &dyn HirDatabase, ty: &Type) -> Option<Vec<TypeTree>> {
        self.data
            .iter()
            .find(|(t, _)| t.could_unify_with_normalized(db, ty))
            .map(|(_, tts)| tts.iter().cloned().collect())
    }

    pub fn insert(&mut self, ty: Type, trees: impl Iterator<Item = TypeTree>) {
        match self.data.get_mut(&ty) {
            Some(it) => it.extend(trees.take(MAX_VARIATIONS)),
            None => {
                self.data.insert(ty.clone(), trees.take(MAX_VARIATIONS).collect());
                for it in self.new_types.values_mut() {
                    it.push(ty.clone());
                }
            }
        }
    }

    pub fn iter_types(&self) -> impl Iterator<Item = Type> + '_ {
        self.data.keys().cloned()
    }

    pub fn new_types(&mut self, key: NewTypesKey) -> Vec<Type> {
        match self.new_types.get_mut(&key) {
            Some(it) => std::mem::take(it),
            None => Vec::new(),
        }
    }

    pub fn mark_exhausted(&mut self, def: ScopeDef) {
        self.exhausted_scopedefs.insert(def);
    }

    pub fn mark_fulfilled(&mut self, def: ScopeDef) {
        self.round_scopedef_hits.insert(def);
    }

    pub fn new_round(&mut self) {
        for def in &self.round_scopedef_hits {
            let hits = self.scopedef_hits.entry(*def).and_modify(|n| *n += 1).or_insert(0);
            const MAX_ROUNDS_AFTER_HIT: u32 = 2;
            if *hits > MAX_ROUNDS_AFTER_HIT {
                self.exhausted_scopedefs.insert(*def);
            }
        }
        self.round_scopedef_hits.clear();
    }

    pub fn exhausted_scopedefs(&self) -> &FxHashSet<ScopeDef> {
        &self.exhausted_scopedefs
    }
}

pub fn term_search<DB: HirDatabase>(
    sema: &Semantics<'_, DB>,
    module: Module,
    mut defs: FxHashSet<ScopeDef>,
    goal: &Type,
) -> Vec<TypeTree> {
    let mut lookup = LookupTable::new();

    // Try trivial tactic first, also populates lookup table
    let mut solutions: Vec<TypeTree> =
        tactics::trivial(sema.db, &defs, &mut lookup, goal).collect();
    let mut solution_found = !solutions.is_empty();

    for _ in 0..5 {
        lookup.new_round();

        solutions.extend(tactics::type_constructor(sema.db, &module, &defs, &mut lookup, goal));
        solutions.extend(tactics::free_function(sema.db, &module, &defs, &mut lookup, goal));
        solutions.extend(tactics::impl_method(sema.db, &module, &defs, &mut lookup, goal));
        solutions.extend(tactics::struct_projection(sema.db, &module, &defs, &mut lookup, goal));

        if solution_found {
            break;
        }

        solution_found = !solutions.is_empty();

        for def in lookup.exhausted_scopedefs() {
            defs.remove(def);
        }
    }

    solutions.into_iter().unique().collect()
}