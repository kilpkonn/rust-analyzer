use hir_ty::{db::HirDatabase, display::HirDisplay};
use itertools::Itertools;
use rustc_hash::FxHashSet;

use crate::{
    Adt, AsAssocItem, Const, ConstParam, Field, Function, Local, Module, ModuleDef, ScopeDef,
    Semantics, Static, Struct, StructKind, Trait, Type, Variant,
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
    Function { func: Function, generics: Vec<Type> },
    Variant { variant: Variant, generics: Vec<Type> },
    Struct { strukt: Struct, generics: Vec<Type> },
    Field(Field),
}

impl TypeTransformation {
    fn ret_ty(&self, db: &dyn HirDatabase, params: &[TypeTree]) -> Type {
        match self {
            Self::Function { func, generics } => match func.has_self_param(db) {
                true => func.ret_type_with_generics(
                    db,
                    params[0].ty(db).type_arguments().chain(generics.iter().cloned()),
                ),
                false => func.ret_type_with_generics(db, generics.iter().cloned()),
            },
            Self::Variant { variant, generics } => {
                variant.parent_enum(db).ty_with_generics(db, generics.iter().cloned())
            }
            Self::Struct { strukt, generics } => {
                strukt.ty_with_generics(db, generics.iter().cloned())
            }
            Self::Field(it) => it.ty_with_generics(db, params[0].ty(db).type_arguments()),
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
            Self::Function { func, .. } => {
                if func.has_self_param(db) {
                    let target = params
                        .first()
                        .expect("no self param")
                        .gen_source_code(items_in_scope, sema);
                    let args = params
                        .iter()
                        .skip(1)
                        .map(|f| f.gen_source_code(items_in_scope, sema))
                        .join(", ");
                    format!("{}.{}({})", target, func.name(db).display(db).to_string(), args)
                } else {
                    let args =
                        params.iter().map(|f| f.gen_source_code(items_in_scope, sema)).join(", ");
                    let sig = format!("{}({})", func.name(db).display(db).to_string(), args);
                    if items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Function(*func))) {
                        return sig;
                    }
                    format!("{}{}", gen_module_prefix(func.module(db), items_in_scope, db), sig)
                }
            }
            Self::Variant { variant, generics } => {
                let inner = match variant.kind(db) {
                    StructKind::Tuple => {
                        let args = params
                            .iter()
                            .map(|f| f.gen_source_code(items_in_scope, sema))
                            .join(", ");
                        let name = variant.name(db).display(db).to_string();
                        format!("{name}({args})")
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
                        let name = variant.name(db).display(db).to_string();
                        format!("{name} {{ {args} }}")
                    }
                    StructKind::Unit => match generics.is_empty() {
                        true => variant.name(db).display(db).to_string(),
                        false => {
                            let name = variant.name(db).display(db).to_string();
                            let generics = generics.iter().map(|it| it.display(db)).join(", ");
                            format!("{name}::<{generics}>")
                        }
                    },
                };
                if items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Variant(*variant))) {
                    inner
                } else {
                    let parent_enum = variant.parent_enum(db);
                    let name = parent_enum.name(db).display(db).to_string();
                    let sig = format!("{name}::{inner}",);
                    if items_in_scope
                        .contains(&ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Enum(parent_enum))))
                    {
                        return sig;
                    }
                    let prefix = gen_module_prefix(variant.module(db), items_in_scope, db);
                    format!("{prefix}{sig}")
                }
            }
            Self::Struct { strukt, generics } => {
                let sig = match strukt.kind(db) {
                    StructKind::Tuple => {
                        let name = strukt.name(db).display(db).to_string();
                        let args = params
                            .iter()
                            .map(|a| a.gen_source_code(items_in_scope, sema))
                            .join(", ");
                        format!("{name}({args})")
                    }
                    StructKind::Record => {
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
                        let name = strukt.name(db).display(db).to_string();
                        format!("{name} {{ {args} }}")
                    }
                    StructKind::Unit => match generics.is_empty() {
                        true => strukt.name(db).display(db).to_string(),
                        false => {
                            let name = strukt.name(db).display(db).to_string();
                            let generics = generics.iter().map(|it| it.display(db)).join(", ");
                            format!("{name}::<{generics}>")
                        }
                    },
                };

                if items_in_scope
                    .contains(&ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Struct(*strukt))))
                {
                    return sig;
                }

                let prefix = gen_module_prefix(strukt.module(db), items_in_scope, db);
                format!("{prefix}{sig}")
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
            TypeTree::TypeTransformation { func, params } => func.ret_ty(db, params),
        }
    }

    pub fn traits_used(&self, db: &dyn HirDatabase) -> Vec<Trait> {
        let mut res = Vec::new();

        match self {
            TypeTree::TypeTransformation {
                func: TypeTransformation::Function { func, .. },
                params,
            } => {
                res.extend(params.iter().flat_map(|it| it.traits_used(db)));
                if let Some(it) = func.as_assoc_item(db) {
                    if let Some(it) = it.containing_trait_or_trait_impl(db) {
                        res.push(it);
                    }
                }
            }
            _ => (),
        }

        res
    }
}
