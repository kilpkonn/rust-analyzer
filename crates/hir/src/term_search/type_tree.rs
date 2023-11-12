use hir_ty::{db::HirDatabase, display::HirDisplay};
use itertools::Itertools;
use rustc_hash::FxHashSet;

use crate::{
    Adt, Const, ConstParam, Field, Function, Local, Module, ModuleDef, ScopeDef, Semantics, Static,
    Struct, StructKind, Type, Variant,
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
                if items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Const(*it))) {
                    return name;
                }
                (name, it.module(db))
            }
            TypeInhabitant::Static(it) => {
                let name = it.name(db).display(db).to_string();
                if items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Static(*it))) {
                    return name;
                }
                (name, it.module(db))
            }
            TypeInhabitant::Local(it) => return it.name(db).display(db).to_string(),
            TypeInhabitant::ConstParam(it) => return it.name(db).display(db).to_string(),
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
        }
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum TypeTransformation {
    Function(Function),
    Variant { variant: Variant, generics: Vec<Type> },
    Struct { strukt: Struct, generics: Vec<Type> },
    Field(Field),
}

impl TypeTransformation {
    fn ret_ty(&self, db: &dyn HirDatabase) -> Type {
        match self {
            Self::Function(it) => it.ret_type(db),
            Self::Variant { variant, generics } => {
                variant.parent_enum(db).ty_with_generics(db, generics)
            }
            Self::Struct { strukt, generics } => strukt.ty_with_generics(db, generics),
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
                    if items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Function(*it))) {
                        return sig;
                    }
                    format!("{}{}", gen_module_prefix(it.module(db), items_in_scope, db), sig)
                }
            }
            Self::Variant { variant, generics } => {
                let generics_str = if generics.is_empty() {
                    String::new()
                } else {
                    let generics = generics.iter().map(|it| it.display(db)).join(", ");
                    format!("::<{generics}>")
                };
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
                    format!("{inner}{generics_str}")
                } else {
                    let parent_enum = variant.parent_enum(db);
                    let sig = format!(
                        "{}{}::{}",
                        parent_enum.name(db).display(db).to_string(),
                        generics_str,
                        inner,
                    );
                    if items_in_scope
                        .contains(&ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Enum(parent_enum))))
                    {
                        return sig;
                    }
                    format!("{}{}", gen_module_prefix(variant.module(db), items_in_scope, db), sig)
                }
            }
            Self::Struct { strukt, generics } => {
                let generics_str = if generics.is_empty() {
                    String::new()
                } else {
                    let generics = generics.iter().map(|it| it.display(db)).join(", ");
                    format!("<{generics}>")
                };

                let fields = strukt.fields(db);
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
                let sig = format!(
                    "{}{} {{ {} }}",
                    strukt.name(db).display(db).to_string(),
                    generics_str,
                    args
                );
                if items_in_scope
                    .contains(&ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Struct(*strukt))))
                {
                    return sig;
                }

                format!("{}{}", gen_module_prefix(strukt.module(db), items_in_scope, db), sig)
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
