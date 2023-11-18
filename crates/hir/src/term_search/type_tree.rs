use hir_ty::{db::HirDatabase, display::HirDisplay};
use itertools::Itertools;
use rustc_hash::FxHashSet;

use crate::{
    Adt, AsAssocItem, Const, ConstParam, Field, Function, Local, Module, ModuleDef, ScopeDef,
    SemanticsScope, Static, Struct, StructKind, Trait, Type, Variant,
};

fn gen_module_prefix(db: &dyn HirDatabase, module: &Module, def: &ModuleDef) -> String {
    let path = module.find_use_path(db.upcast(), *def, true);
    path.map(|it| it.display(db.upcast()).to_string()).unwrap_or(String::new())
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum TypeInhabitant {
    Const(Const),
    Static(Static),
    Local(Local),
    ConstParam(ConstParam),
}

impl TypeInhabitant {
    fn gen_source_code(&self, sema_scope: &SemanticsScope<'_>) -> String {
        let db = sema_scope.db;
        let def = match self {
            TypeInhabitant::Const(it) => ModuleDef::Const(*it),
            TypeInhabitant::Static(it) => ModuleDef::Static(*it),
            TypeInhabitant::Local(it) => return it.name(db).display(db.upcast()).to_string(),
            TypeInhabitant::ConstParam(it) => return it.name(db).display(db.upcast()).to_string(),
        };
        gen_module_prefix(db, &sema_scope.module(), &def)
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
    fn gen_source_code(
        &self,
        params: &[TypeTree],
        items_in_scope: &FxHashSet<ScopeDef>,
        sema_scope: &SemanticsScope<'_>,
    ) -> String {
        let db = sema_scope.db;
        match self {
            Self::Function { func, .. } => {
                if let Some(self_param) = func.self_param(db) {
                    let func_name = func.name(db).display(db.upcast()).to_string();
                    let target = params
                        .first()
                        .expect("no self param")
                        .gen_source_code(items_in_scope, sema_scope);
                    let args = params
                        .iter()
                        .skip(1)
                        .map(|f| f.gen_source_code(items_in_scope, sema_scope))
                        .join(", ");

                    match func.as_assoc_item(db).unwrap().containing_trait_or_trait_impl(db) {
                        Some(trait_) => {
                            let trait_name = gen_module_prefix(
                                db,
                                &sema_scope.module(),
                                &ModuleDef::Trait(trait_),
                            );
                            let target = match self_param.access(db) {
                                crate::Access::Shared => format!("&{target}"),
                                crate::Access::Exclusive => format!("&mut {target}"),
                                crate::Access::Owned => target,
                            };
                            match args.is_empty() {
                                true => format!("{trait_name}::{func_name}({target})",),
                                false => format!("{trait_name}::{func_name}({target}, {args})",),
                            }
                        }
                        None => format!("{target}.{func_name}({args})"),
                    }
                } else {
                    let args = params
                        .iter()
                        .map(|f| f.gen_source_code(items_in_scope, sema_scope))
                        .join(", ");
                    let sig =
                        format!("{}({})", func.name(db).display(db.upcast()).to_string(), args);
                    if items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Function(*func))) {
                        return sig;
                    }
                    format!(
                        "{}{}",
                        gen_module_prefix(db, &sema_scope.module(), &ModuleDef::Function(*func)),
                        sig
                    )
                }
            }
            Self::Variant { variant, generics } => {
                let inner = match variant.kind(db) {
                    StructKind::Tuple => {
                        let args = params
                            .iter()
                            .map(|f| f.gen_source_code(items_in_scope, sema_scope))
                            .join(", ");
                        format!("({args})")
                    }
                    StructKind::Record => {
                        let fields = variant.fields(db);
                        let args = params
                            .iter()
                            .zip(fields.iter())
                            .map(|(a, f)| {
                                format!(
                                    "{}: {}",
                                    f.name(db).display(db.upcast()).to_string(),
                                    a.gen_source_code(items_in_scope, sema_scope)
                                )
                            })
                            .join(", ");
                        format!("{{ {args} }}")
                    }
                    StructKind::Unit => match generics.is_empty() {
                        true => String::new(),
                        false => {
                            let generics = generics.iter().map(|it| it.display(db)).join(", ");
                            format!("::<{generics}>")
                        }
                    },
                };

                let prefix =
                    gen_module_prefix(db, &sema_scope.module(), &ModuleDef::Variant(*variant));
                format!("{prefix}{inner}")
            }
            Self::Struct { strukt, generics } => {
                let inner = match strukt.kind(db) {
                    StructKind::Tuple => {
                        let args = params
                            .iter()
                            .map(|a| a.gen_source_code(items_in_scope, sema_scope))
                            .join(", ");
                        format!("({args})")
                    }
                    StructKind::Record => {
                        let fields = strukt.fields(db);
                        let args = params
                            .iter()
                            .zip(fields.iter())
                            .map(|(a, f)| {
                                format!(
                                    "{}: {}",
                                    f.name(db).display(db.upcast()).to_string(),
                                    a.gen_source_code(items_in_scope, sema_scope)
                                )
                            })
                            .join(", ");
                        format!(" {{ {args} }}")
                    }
                    StructKind::Unit => match generics.is_empty() {
                        true => String::new(),
                        false => {
                            let generics = generics.iter().map(|it| it.display(db)).join(", ");
                            format!("::<{generics}>")
                        }
                    },
                };

                let prefix = gen_module_prefix(
                    db,
                    &sema_scope.module(),
                    &ModuleDef::Adt(Adt::Struct(*strukt)),
                );
                format!("{prefix}{inner}")
            }
            Self::Field(it) => {
                let strukt = params
                    .first()
                    .expect("No params for struct field")
                    .gen_source_code(items_in_scope, sema_scope);
                let field = it.name(db).display(db.upcast()).to_string();
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
    pub fn gen_source_code(
        &self,
        items_in_scope: &FxHashSet<ScopeDef>,
        sema_scope: &SemanticsScope<'_>,
    ) -> String {
        match self {
            TypeTree::TypeInhabitant(it) => it.gen_source_code(sema_scope),
            TypeTree::TypeTransformation { func, params } => {
                func.gen_source_code(&params, items_in_scope, sema_scope)
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
