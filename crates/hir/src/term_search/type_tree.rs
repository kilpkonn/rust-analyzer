use hir_ty::db::HirDatabase;
use itertools::Itertools;
use rustc_hash::FxHashSet;

use crate::{
    Const, ConstParam, Field, Function, Impl, Local, Module, ModuleDef, ScopeDef, Semantics,
    Static, Struct, StructKind, Type, Variant,
};

fn gen_module_prefix(
    mut module: Module,
    items_in_scope: &FxHashSet<ScopeDef>,
    db: &dyn HirDatabase,
) -> String {
    let mut prefix = String::new();
    while !items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Module(module))) {
        match module.name(db) {
            Some(m) => prefix = format!("{}::{}", m.display(db.upcast()).to_string(), prefix),
            None => (),
        };
        match module.parent(db) {
            Some(m) => module = m,
            None => break,
        };
    }
    prefix
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum TypeInhabitant {
    Const(Const),
    Static(Static),
    Local(Local),
    ConstParam(ConstParam),
    SelfParam(Impl),
}

impl TypeInhabitant {
    fn gen_source_code<DB: HirDatabase>(
        &self,
        items_in_scope: &FxHashSet<ScopeDef>,
        sema: &Semantics<'_, DB>,
    ) -> String {
        let db = sema.db;
        let (name, module) = match self {
            TypeInhabitant::Const(it) => {
                let name = match it.name(db) {
                    Some(it) => it.display(db).to_string(),
                    None => String::from("_"),
                };
                (name, it.module(db))
            }
            TypeInhabitant::Static(it) => (it.name(db).display(db).to_string(), it.module(db)),
            TypeInhabitant::Local(it) => return it.name(db).display(db).to_string(),
            TypeInhabitant::ConstParam(it) => return it.name(db).display(db).to_string(),
            TypeInhabitant::SelfParam(_) => return String::from("self"),
        };
        let prefix = gen_module_prefix(module, items_in_scope, db);
        format!("{}{}", prefix, name)
    }

    fn ty(&self, db: &dyn HirDatabase) -> Type {
        match self {
            TypeInhabitant::Const(it) => it.ty(db),
            TypeInhabitant::Static(it) => it.ty(db),
            TypeInhabitant::Local(it) => it.ty(db),
            TypeInhabitant::ConstParam(it) => it.ty(db),
            TypeInhabitant::SelfParam(it) => it.self_ty(db),
        }
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum TypeTransformation {
    Function(Function),
    Variant(Variant),
    Struct(Struct),
    Field(Field),
}

impl TypeTransformation {
    fn ret_ty(&self, db: &dyn HirDatabase) -> Type {
        match self {
            Self::Function(it) => it.ret_type(db),
            Self::Variant(it) => it.parent_enum(db).ty(db),
            Self::Struct(it) => it.ty(db),
            Self::Field(it) => it.ty(db),
        }
    }
    fn gen_source_code<DB: HirDatabase>(
        &self,
        params: &[TypeTree],
        items_in_scope: &FxHashSet<ScopeDef>,
        sema: &Semantics<'_, DB>,
    ) -> String {
        let db = sema.db;
        match self {
            Self::Function(it) => {
                if it.has_self_param(db) {
                    let target = params
                        .first()
                        .expect("no self param")
                        .gen_source_code(items_in_scope, sema);
                    let args = params
                        .iter()
                        .skip(1)
                        .map(|f| f.gen_source_code(items_in_scope, sema))
                        .join(", ");
                    format!("{}.{}({})", target, it.name(db).display(db).to_string(), args)
                } else {
                    let args =
                        params.iter().map(|f| f.gen_source_code(items_in_scope, sema)).join(", ");
                    let sig = format!("{}({})", it.name(db).display(db).to_string(), args);
                    format!("{}{}", gen_module_prefix(it.module(db), items_in_scope, db), sig)
                }
            }
            Self::Variant(variant) => {
                let inner = match variant.kind(db) {
                    StructKind::Tuple => {
                        let args = params
                            .iter()
                            .map(|f| f.gen_source_code(items_in_scope, sema))
                            .join(", ");
                        format!("{}({})", variant.name(db).display(db).to_string(), args)
                    }
                    StructKind::Record => {
                        let fields = variant.fields(db);
                        let args = params
                            .iter()
                            .zip(fields.iter())
                            .map(|(a, f)| {
                                format!(
                                    "{}: {}",
                                    f.name(db).display(db).to_string(),
                                    a.gen_source_code(items_in_scope, sema)
                                )
                            })
                            .join(", ");
                        format!("{} {{ {} }}", variant.name(db).display(db).to_string(), args)
                    }
                    StructKind::Unit => variant.name(db).display(db).to_string(),
                };
                if items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Variant(*variant))) {
                    inner
                } else {
                    let sig = format!(
                        "{}::{}",
                        variant.parent_enum(db).name(db).display(db).to_string(),
                        inner,
                    );
                    format!("{}{}", gen_module_prefix(variant.module(db), items_in_scope, db), sig)
                }
            }
            Self::Struct(it) => {
                let fields = it.fields(db);
                let args = params
                    .iter()
                    .zip(fields.iter())
                    .map(|(a, f)| {
                        format!(
                            "{}: {}",
                            f.name(db).display(db).to_string(),
                            a.gen_source_code(items_in_scope, sema)
                        )
                    })
                    .join(", ");
                let sig = format!("{} {{ {} }}", it.name(db).display(db).to_string(), args);
                format!("{}{}", gen_module_prefix(it.module(db), items_in_scope, db), sig)
            }
            Self::Field(it) => {
                let strukt = params
                    .first()
                    .expect("No params for struct field")
                    .gen_source_code(items_in_scope, sema);
                let field = it.name(db).display(db).to_string();
                format!("{strukt}.{field}")
            }
        }
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum TypeTree {
    /// Leaf node
    TypeInhabitant(TypeInhabitant),
    /// Node with children
    TypeTransformation { func: TypeTransformation, params: Vec<TypeTree> },
}

impl TypeTree {
    pub fn gen_source_code<DB: HirDatabase>(
        &self,
        items_in_scope: &FxHashSet<ScopeDef>,
        sema: &Semantics<'_, DB>,
    ) -> String {
        match self {
            TypeTree::TypeInhabitant(it) => it.gen_source_code(items_in_scope, sema),
            TypeTree::TypeTransformation { func, params } => {
                func.gen_source_code(&params, items_in_scope, sema)
            }
        }
    }

    pub fn ty(&self, db: &dyn HirDatabase) -> Type {
        match self {
            TypeTree::TypeInhabitant(it) => it.ty(db),
            TypeTree::TypeTransformation { func, .. } => func.ret_ty(db),
        }
    }
}
