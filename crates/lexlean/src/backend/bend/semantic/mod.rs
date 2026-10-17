//! Language 2.2: semantic modules lowered to Bend 2 (SPEC.md §18.11).
//!
//! A semantic module is closed, first-order data whose every type is
//! explicit, so this lowering needs no inference engine: types are read
//! off the declarations, and every argument Bend cannot infer (an erased
//! type argument, an equation's type) is computed from them.
//!
//! Disclosed lowering decisions:
//!
//! - **Datatypes.** A structure, class or inductive is a Bend `type` whose
//!   constructors are qualified by the type's name, since Bend constructor
//!   names are module-global; a structure's projection `T.f` is a def that
//!   matches its one constructor, exactly as Lean's projection reduces.
//! - **Kinds.** Values are `Data` unless they hold a function, so a value
//!   may be used as often as Lean uses it; a `Prop` lowers to a Bend type
//!   of kind `Data` when it is built from equations (`Sem.le`, `{a == b}`
//!   and pairs of those), so a hypothesis may be reused too.
//! - **Recursion.** A structurally recursive definition takes its
//!   decreasing parameter first, as Bend's termination check requires, and
//!   every call passes its arguments in that order.
//! - **Proofs.** Every proof is an explicit term (`proof.rs`), checked by
//!   Bend; a goal the lowering cannot discharge is refused with `LLB6008`
//!   rather than emitted with a guess.

pub mod closure;
pub mod mutual;
pub mod names;
pub mod normal;
pub mod proof;

use std::collections::{BTreeMap, BTreeSet};

use crate::backend::bend::engine::{fail, module_alias};
use crate::backend::bend::prelude::PRELUDE_ALIAS;
use crate::backend::bend::syntax::{
    print_items, BTerm, Body, Item, Name, Param, Pattern, Quantity, Stmt, Tail,
};
use crate::backend::{EmitSource, Emitter};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{
    MemberRef, SemanticBranch, SemanticDeclaration, SemanticModule, SemanticParameter,
    SemanticPrimitive, SemanticTerm, SemanticType,
};
use crate::link::CheckedModule;

/// The embedded semantic support module.
pub const SUPPORT_PATH: &str = "language/bend-prelude/Semantic.bend";

/// Where a build publishes the support module.
pub const SUPPORT_BUILD_PATH: &str = "modules/LexLeanSemantic.bend";

/// The alias generated modules import the support module under.
pub const SUPPORT_ALIAS: &str = "S";

/// The support module's bytes as published: its import of the prelude names
/// the prelude's build path, which differs from its source name.
///
/// # Errors
///
/// An internal diagnostic when the module is not embedded.
pub fn support_artifact() -> Result<(&'static str, Vec<u8>), Diagnostic> {
    let bytes = crate::embedded::FILES
        .iter()
        .find(|(path, _)| *path == SUPPORT_PATH)
        .map(|(_, bytes)| *bytes)
        .ok_or_else(|| fail("the semantic support module is not embedded"))?;
    let text =
        std::str::from_utf8(bytes).map_err(|_| fail("the semantic support module is not UTF-8"))?;
    let published = text.replace(
        "import ./LexLean.bend as L\n",
        "import ./LexLeanPrelude.bend as L\n",
    );
    Ok((SUPPORT_BUILD_PATH, published.into_bytes()))
}

/// Every semantic module of a project, by source module name.
pub struct SemanticProject<'a> {
    units: BTreeMap<String, Unit<'a>>,
}

struct Unit<'a> {
    generated: String,
    declarations: BTreeMap<String, &'a SemanticDeclaration>,
    /// The declarations in source order.
    order: Vec<&'a SemanticDeclaration>,
}

impl<'a> SemanticProject<'a> {
    /// Index every semantic module's lowered declarations.
    #[must_use]
    pub fn new(modules: &'a BTreeMap<String, CheckedModule>) -> Self {
        let mut units = BTreeMap::new();
        for (name, checked) in modules {
            let Some(semantic) = &checked.document.semantic else {
                continue;
            };
            let order = semantic.lowered_declarations();
            let declarations = order
                .iter()
                .map(|declaration| (declaration.name().to_owned(), *declaration))
                .collect();
            units.insert(
                name.clone(),
                Unit {
                    generated: checked.document.lean_module.clone(),
                    declarations,
                    order,
                },
            );
        }
        Self { units }
    }
}

/// The ordered parameters of a callable as Bend takes them: the positions
/// of the semantic parameters, decreasing parameter first.
fn bend_order(declaration: &SemanticDeclaration) -> Vec<usize> {
    match declaration {
        SemanticDeclaration::Definition {
            parameters,
            recursive_argument: Some(argument),
            termination: None,
            ..
        } => {
            let first = parameters
                .iter()
                .position(|parameter| &parameter.name == argument)
                .unwrap_or(0);
            std::iter::once(first)
                .chain((0..parameters.len()).filter(|index| *index != first))
                .collect()
        }
        SemanticDeclaration::Definition { parameters, .. }
        | SemanticDeclaration::Theorem { parameters, .. } => (0..parameters.len()).collect(),
        _ => Vec::new(),
    }
}

/// The typed locals of a scope, with each local's Bend spelling.
#[derive(Clone, Default)]
pub struct Scope {
    locals: BTreeMap<String, (String, SemanticType)>,
    /// The locals a `let` binds: Bend matches only on a parameter or a
    /// pattern variable, so these are never a match scrutinee.
    lets: BTreeSet<String>,
    /// The function parameters in scope, each split into its code and its
    /// environment (see `closure`).
    closures: BTreeMap<String, closure::Closure>,
}

impl Scope {
    fn with(&self, name: &str, ty: SemanticType) -> Result<Self, Diagnostic> {
        let mut next = self.clone();
        next.locals
            .insert(name.to_owned(), (names::local(name)?, ty));
        next.lets.remove(name);
        next.closures.remove(name);
        Ok(next)
    }

    fn with_let(&self, name: &str, ty: SemanticType) -> Result<Self, Diagnostic> {
        let mut next = self.with(name, ty)?;
        next.lets.insert(name.to_owned());
        Ok(next)
    }

    /// Whether `term` is a local Bend can match on.
    fn matchable(&self, term: &SemanticTerm) -> bool {
        matches!(term, SemanticTerm::Var { name }
            if self.locals.contains_key(name) && !self.lets.contains(name))
    }

    fn get(&self, name: &str) -> Result<&(String, SemanticType), Diagnostic> {
        self.locals
            .get(name)
            .ok_or_else(|| fail(format!("the local `{name}` is unbound")))
    }
}

/// The hole a rewrite motive marks, as a semantic variable no source can
/// name (semantic names begin with a letter).
pub const HOLE: &str = "\u{0}hole";

/// The lowering of one semantic module.
pub struct Lower<'p, 'a> {
    project: &'p SemanticProject<'a>,
    module: String,
    imports: BTreeSet<String>,
    /// Whether the module names the prelude.
    pub uses_prelude: bool,
    /// Whether the module names the support module.
    pub uses_support: bool,
    aux: Vec<Item>,
    fresh: usize,
    /// The type parameters in scope, by name.
    type_parameters: BTreeSet<String>,
    /// The mutual groups already lowered, by key.
    mutual_done: BTreeSet<String>,
}

fn synthetic(text: impl Into<String>) -> Name {
    Name::synthetic(text)
}

fn call(head: impl Into<String>, args: Vec<BTerm>) -> BTerm {
    BTerm::Call(synthetic(head), args)
}

fn var(text: impl Into<String>) -> BTerm {
    BTerm::Name(synthetic(text))
}

fn here() -> EmitSource {
    EmitSource::Synthetic(crate::backend::bend::syntax::SYNTAX_ORIGIN.to_owned())
}

fn substitute_type(ty: &SemanticType, map: &BTreeMap<String, SemanticType>) -> SemanticType {
    let go = |t: &SemanticType| Box::new(substitute_type(t, map));
    match ty {
        SemanticType::Parameter { name } => map.get(name).cloned().unwrap_or_else(|| ty.clone()),
        SemanticType::Option { value } => SemanticType::Option { value: go(value) },
        SemanticType::Result { ok, error } => SemanticType::Result {
            ok: go(ok),
            error: go(error),
        },
        SemanticType::List { element } => SemanticType::List {
            element: go(element),
        },
        SemanticType::Named { member, arguments } => SemanticType::Named {
            member: member.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_type(argument, map))
                .collect(),
        },
        SemanticType::Product { left, right } => SemanticType::Product {
            left: go(left),
            right: go(right),
        },
        SemanticType::Function { parameters, result } => SemanticType::Function {
            parameters: parameters
                .iter()
                .map(|parameter| substitute_type(parameter, map))
                .collect(),
            result: go(result),
        },
        SemanticType::Map { key, value } => SemanticType::Map {
            key: go(key),
            value: go(value),
        },
        SemanticType::Set { element } => SemanticType::Set {
            element: go(element),
        },
        other => other.clone(),
    }
}

/// Qualify a type read from module `module`'s declarations so it names the
/// same members from any other module.
fn qualify(ty: &SemanticType, module: &str) -> SemanticType {
    let go = |t: &SemanticType| Box::new(qualify(t, module));
    match ty {
        SemanticType::Named { member, arguments } => SemanticType::Named {
            member: MemberRef {
                module: Some(member.module.clone().unwrap_or_else(|| module.to_owned())),
                name: member.name.clone(),
            },
            arguments: arguments.iter().map(|a| qualify(a, module)).collect(),
        },
        SemanticType::Option { value } => SemanticType::Option { value: go(value) },
        SemanticType::Result { ok, error } => SemanticType::Result {
            ok: go(ok),
            error: go(error),
        },
        SemanticType::List { element } => SemanticType::List {
            element: go(element),
        },
        SemanticType::Product { left, right } => SemanticType::Product {
            left: go(left),
            right: go(right),
        },
        SemanticType::Function { parameters, result } => SemanticType::Function {
            parameters: parameters.iter().map(|p| qualify(p, module)).collect(),
            result: go(result),
        },
        SemanticType::Map { key, value } => SemanticType::Map {
            key: go(key),
            value: go(value),
        },
        SemanticType::Set { element } => SemanticType::Set {
            element: go(element),
        },
        other => other.clone(),
    }
}

impl<'p, 'a> Lower<'p, 'a> {
    /// A lowering for source module `module`.
    #[must_use]
    pub fn new(project: &'p SemanticProject<'a>, module: &str) -> Self {
        Self {
            project,
            module: module.to_owned(),
            imports: BTreeSet::new(),
            uses_prelude: false,
            uses_support: false,
            aux: Vec::new(),
            fresh: 0,
            type_parameters: BTreeSet::new(),
            mutual_done: BTreeSet::new(),
        }
    }

    fn prelude(&mut self, name: &str) -> String {
        self.uses_prelude = true;
        format!("{PRELUDE_ALIAS}.{name}")
    }

    fn support(&mut self, name: &str) -> String {
        self.uses_support = true;
        format!("{SUPPORT_ALIAS}.Sem.{name}")
    }

    fn fresh(&mut self, stem: &str) -> String {
        self.fresh += 1;
        format!("ll_{stem}{}", self.fresh)
    }

    /// The source module a member lives in.
    fn home(&self, member: &MemberRef) -> String {
        member.module.clone().unwrap_or_else(|| self.module.clone())
    }

    /// The declaration a member names.
    fn declaration(&self, member: &MemberRef) -> Result<&'a SemanticDeclaration, Diagnostic> {
        let home = self.home(member);
        let unit = self
            .project
            .units
            .get(&home)
            .ok_or_else(|| fail(format!("the module `{home}` has no semantic lowering")))?;
        unit.declarations
            .get(&member.name)
            .copied()
            .ok_or_else(|| fail(format!("`{}` is not declared in `{home}`", member.name)))
    }

    /// The Bend spelling of the module-level name `name` of `home`.
    fn spell(&mut self, home: &str, name: &str) -> Result<String, Diagnostic> {
        let spelled = names::global(name)?;
        if home == self.module {
            return Ok(spelled);
        }
        let unit = self
            .project
            .units
            .get(home)
            .ok_or_else(|| fail(format!("the module `{home}` has no semantic lowering")))?;
        self.imports.insert(home.to_owned());
        Ok(format!("{}.{spelled}", module_alias(&unit.generated)))
    }

    fn member(&mut self, member: &MemberRef) -> Result<String, Diagnostic> {
        let home = self.home(member);
        self.spell(&home, &member.name)
    }

    /// Imports this module needs, as `(source module, generated name)`.
    #[must_use]
    pub fn imports(&self) -> Vec<(String, String)> {
        self.imports
            .iter()
            .filter_map(|module| {
                self.project
                    .units
                    .get(module)
                    .map(|unit| (module.clone(), unit.generated.clone()))
            })
            .collect()
    }

    // ------------------------------------------------------------------
    // Types
    // ------------------------------------------------------------------

    /// Whether values of a type are `Data`: everything but functions and
    /// records that hold one.
    fn is_data(&self, ty: &SemanticType) -> bool {
        self.data_type(ty, &mut BTreeSet::new())
    }

    fn data_type(&self, ty: &SemanticType, seen: &mut BTreeSet<(String, String)>) -> bool {
        match ty {
            SemanticType::Function { .. } | SemanticType::Prop | SemanticType::Type => false,
            SemanticType::Option { value } => self.data_type(value, seen),
            SemanticType::Result { ok, error } => {
                self.data_type(ok, seen) && self.data_type(error, seen)
            }
            SemanticType::List { element } | SemanticType::Set { element } => {
                self.data_type(element, seen)
            }
            SemanticType::Product { left, right } => {
                self.data_type(left, seen) && self.data_type(right, seen)
            }
            SemanticType::Map { key, value } => {
                self.data_type(key, seen) && self.data_type(value, seen)
            }
            SemanticType::Named { member, arguments } => {
                if !arguments
                    .iter()
                    .all(|argument| self.data_type(argument, seen))
                {
                    return false;
                }
                let key = (self.home(member), member.name.clone());
                if !seen.insert(key) {
                    return true;
                }
                let home = self.home(member);
                match self.declaration(member) {
                    Ok(SemanticDeclaration::Structure { fields, .. })
                    | Ok(SemanticDeclaration::Class { fields, .. }) => fields
                        .iter()
                        .all(|field| self.data_type(&qualify(&field.r#type, &home), seen)),
                    Ok(SemanticDeclaration::Inductive { constructors, .. }) => {
                        constructors.iter().all(|constructor| {
                            constructor
                                .fields
                                .iter()
                                .all(|field| self.data_type(&qualify(field, &home), seen))
                        })
                    }
                    _ => true,
                }
            }
            _ => true,
        }
    }

    /// The Bend type of a semantic type.
    ///
    /// # Errors
    ///
    /// `LLB6008` for a type with no Bend representation.
    pub fn ty(&mut self, ty: &SemanticType) -> Result<BTerm, Diagnostic> {
        Ok(match ty {
            SemanticType::Type => BTerm::Kind("Data"),
            SemanticType::Prop => BTerm::Kind("Type"),
            SemanticType::Parameter { name } => var(names::local(name)?),
            SemanticType::Nat => var("Nat"),
            SemanticType::Bool => var("Bool"),
            SemanticType::Unit => var("Unit"),
            SemanticType::String => var("String"),
            SemanticType::Ordering => var("Cmp"),
            SemanticType::Int => var(self.prelude("Lean.Int")),
            SemanticType::Option { value } => BTerm::Datatype(
                synthetic("Maybe"),
                vec!["&2".to_owned()],
                vec![self.ty(value)?],
            ),
            SemanticType::Result { ok, error } => BTerm::Datatype(
                synthetic("Result"),
                vec!["&2".to_owned(), "&2".to_owned()],
                vec![self.ty(error)?, self.ty(ok)?],
            ),
            SemanticType::List { element } | SemanticType::Set { element } => BTerm::Datatype(
                synthetic("List"),
                vec!["&2".to_owned()],
                vec![self.ty(element)?],
            ),
            SemanticType::Map { key, value } => {
                let pair = SemanticType::Product {
                    left: key.clone(),
                    right: value.clone(),
                };
                BTerm::Datatype(
                    synthetic("List"),
                    vec!["&2".to_owned()],
                    vec![self.ty(&pair)?],
                )
            }
            SemanticType::Product { left, right } => {
                let (left, right) = (self.ty(left)?, self.ty(right)?);
                call(self.prelude("Lean.Prod"), vec![left, right])
            }
            SemanticType::Function { parameters, result } => {
                self.function_type(parameters, result)?
            }
            SemanticType::Named { member, arguments } => {
                let head = self.member(member)?;
                if arguments.is_empty() {
                    var(head)
                } else {
                    let arguments = arguments
                        .iter()
                        .map(|argument| self.ty(argument))
                        .collect::<Result<Vec<_>, _>>()?;
                    BTerm::Datatype(synthetic(head), Vec::new(), arguments)
                }
            }
            SemanticType::ContractViolation => var(self.support("ContractViolation")),
            SemanticType::ReasoningFailure => var(self.support("ReasoningFailure")),
            other => {
                return Err(fail(format!(
                    "the semantic type `{other:?}` has no Bend representation in language 2.2"
                )))
            }
        })
    }

    // ------------------------------------------------------------------
    // Typing
    // ------------------------------------------------------------------

    /// The signature of a callable as `(type parameters, parameters,
    /// result)`, each type qualified to read from any module.
    fn signature(
        &self,
        member: &MemberRef,
    ) -> Result<(Vec<String>, Vec<SemanticParameter>, SemanticType), Diagnostic> {
        let home = self.home(member);
        let qualify_parameters = |parameters: &[SemanticParameter]| {
            parameters
                .iter()
                .map(|parameter| SemanticParameter {
                    name: parameter.name.clone(),
                    r#type: qualify(&parameter.r#type, &home),
                })
                .collect::<Vec<_>>()
        };
        match self.declaration(member)? {
            SemanticDeclaration::Definition {
                type_parameters,
                parameters,
                result,
                ..
            } => Ok((
                type_parameters.clone(),
                qualify_parameters(parameters),
                qualify(result, &home),
            )),
            SemanticDeclaration::Theorem {
                type_parameters,
                parameters,
                ..
            } => Ok((
                type_parameters.clone(),
                qualify_parameters(parameters),
                SemanticType::Prop,
            )),
            other => Err(fail(format!("`{}` is not callable", other.name()))),
        }
    }

    /// The owner type and field types of a constructor applied at
    /// `type_arguments`.
    fn constructor(
        &self,
        constructor: &MemberRef,
        type_arguments: &[SemanticType],
    ) -> Result<(SemanticType, Vec<SemanticType>), Diagnostic> {
        if constructor.module.is_none() {
            let builtin = match (constructor.name.as_str(), type_arguments) {
                ("Option.none", [value]) => Some((
                    SemanticType::Option {
                        value: Box::new(value.clone()),
                    },
                    Vec::new(),
                )),
                ("Option.some", [value]) => Some((
                    SemanticType::Option {
                        value: Box::new(value.clone()),
                    },
                    vec![value.clone()],
                )),
                ("Result.ok" | "Result.error", [ok, error]) => Some((
                    SemanticType::Result {
                        ok: Box::new(ok.clone()),
                        error: Box::new(error.clone()),
                    },
                    vec![if constructor.name == "Result.ok" {
                        ok.clone()
                    } else {
                        error.clone()
                    }],
                )),
                ("List.nil", [element]) => Some((
                    SemanticType::List {
                        element: Box::new(element.clone()),
                    },
                    Vec::new(),
                )),
                ("List.cons", [element]) => Some((
                    SemanticType::List {
                        element: Box::new(element.clone()),
                    },
                    vec![
                        element.clone(),
                        SemanticType::List {
                            element: Box::new(element.clone()),
                        },
                    ],
                )),
                ("Prod.mk", [left, right]) => Some((
                    SemanticType::Product {
                        left: Box::new(left.clone()),
                        right: Box::new(right.clone()),
                    },
                    vec![left.clone(), right.clone()],
                )),
                ("Nat.zero", _) => Some((SemanticType::Nat, Vec::new())),
                ("Nat.succ", _) => Some((SemanticType::Nat, vec![SemanticType::Nat])),
                ("Bool.true" | "Bool.false", _) => Some((SemanticType::Bool, Vec::new())),
                (name, _) if name.starts_with("ContractViolation.") => {
                    Some((SemanticType::ContractViolation, Vec::new()))
                }
                (name, _) if name.starts_with("ReasoningFailure.") => {
                    Some((SemanticType::ReasoningFailure, Vec::new()))
                }
                _ => None,
            };
            if let Some(found) = builtin {
                return Ok(found);
            }
        }
        let (owner, short) = constructor
            .name
            .rsplit_once('.')
            .ok_or_else(|| fail(format!("`{}` is not a constructor", constructor.name)))?;
        let owner_ref = MemberRef {
            module: constructor.module.clone(),
            name: owner.to_owned(),
        };
        let home = self.home(constructor);
        let declaration = self.declaration(&owner_ref)?;
        let (parameters, fields): (&Vec<String>, Vec<SemanticType>) = match declaration {
            SemanticDeclaration::Inductive {
                type_parameters,
                constructors,
                ..
            } => {
                let found = constructors
                    .iter()
                    .find(|candidate| candidate.name == short)
                    .ok_or_else(|| fail(format!("`{}` is not a constructor", constructor.name)))?;
                (type_parameters, found.fields.clone())
            }
            SemanticDeclaration::Structure {
                type_parameters,
                fields,
                ..
            }
            | SemanticDeclaration::Class {
                type_parameters,
                fields,
                ..
            } if short == "mk" => (
                type_parameters,
                fields.iter().map(|field| field.r#type.clone()).collect(),
            ),
            _ => return Err(fail(format!("`{}` is not a constructor", constructor.name))),
        };
        let map: BTreeMap<String, SemanticType> = parameters
            .iter()
            .cloned()
            .zip(type_arguments.iter().cloned())
            .collect();
        let owner_type = SemanticType::Named {
            member: MemberRef {
                module: Some(home.clone()),
                name: owner.to_owned(),
            },
            arguments: type_arguments.to_vec(),
        };
        Ok((
            owner_type,
            fields
                .iter()
                .map(|field| substitute_type(&qualify(field, &home), &map))
                .collect(),
        ))
    }

    /// The fields of a record type, in declaration order, at its arguments.
    fn record_fields(
        &self,
        ty: &SemanticType,
    ) -> Result<(MemberRef, Vec<(String, SemanticType)>), Diagnostic> {
        let SemanticType::Named { member, arguments } = ty else {
            return Err(fail(format!("`{ty:?}` is not a record type")));
        };
        let home = self.home(member);
        match self.declaration(member)? {
            SemanticDeclaration::Structure {
                type_parameters,
                fields,
                ..
            }
            | SemanticDeclaration::Class {
                type_parameters,
                fields,
                ..
            } => {
                let map: BTreeMap<String, SemanticType> = type_parameters
                    .iter()
                    .cloned()
                    .zip(arguments.iter().cloned())
                    .collect();
                Ok((
                    MemberRef {
                        module: Some(home.clone()),
                        name: member.name.clone(),
                    },
                    fields
                        .iter()
                        .map(|field| {
                            (
                                field.name.clone(),
                                substitute_type(&qualify(&field.r#type, &home), &map),
                            )
                        })
                        .collect(),
                ))
            }
            _ => Err(fail(format!("`{}` is not a record type", member.name))),
        }
    }

    /// Normalize a type for comparison: member modules made explicit.
    fn canonical(&self, ty: &SemanticType) -> SemanticType {
        qualify(ty, &self.module)
    }

    /// The type of a term.
    ///
    /// # Errors
    ///
    /// `LLB6008` when the term is outside what language 2.2 lowers.
    #[allow(clippy::too_many_lines)]
    pub fn infer(&self, term: &SemanticTerm, scope: &Scope) -> Result<SemanticType, Diagnostic> {
        Ok(match term {
            SemanticTerm::Var { name } => scope.get(name)?.1.clone(),
            SemanticTerm::Nat { .. } => SemanticType::Nat,
            SemanticTerm::Integer { representation, .. } => representation.semantic_type(),
            SemanticTerm::String { .. } => SemanticType::String,
            SemanticTerm::Bytes { .. } => SemanticType::Bytes,
            SemanticTerm::Primitive { result, .. } => self.canonical(result),
            SemanticTerm::Bool { .. }
            | SemanticTerm::Beq { .. }
            | SemanticTerm::Ble { .. }
            | SemanticTerm::Blt { .. }
            | SemanticTerm::And { .. }
            | SemanticTerm::Or { .. }
            | SemanticTerm::Not { .. } => SemanticType::Bool,
            SemanticTerm::Unit => SemanticType::Unit,
            SemanticTerm::Nil { element } => SemanticType::List {
                element: Box::new(self.canonical(element)),
            },
            SemanticTerm::Cons { head, .. } => SemanticType::List {
                element: Box::new(self.infer(head, scope)?),
            },
            SemanticTerm::Record {
                r#type,
                type_arguments,
                ..
            } => SemanticType::Named {
                member: MemberRef {
                    module: Some(self.home(r#type)),
                    name: r#type.name.clone(),
                },
                arguments: type_arguments.iter().map(|t| self.canonical(t)).collect(),
            },
            SemanticTerm::Constructor {
                constructor,
                type_arguments,
                ..
            } => {
                let arguments: Vec<SemanticType> =
                    type_arguments.iter().map(|t| self.canonical(t)).collect();
                self.constructor(constructor, &arguments)?.0
            }
            SemanticTerm::InstanceValue {
                class, arguments, ..
            } => SemanticType::Named {
                member: MemberRef {
                    module: Some(self.home(class)),
                    name: class.name.clone(),
                },
                arguments: arguments.iter().map(|t| self.canonical(t)).collect(),
            },
            SemanticTerm::Project { value, field } => {
                let ty = self.infer(value, scope)?;
                let (_, fields) = self.record_fields(&ty)?;
                fields
                    .into_iter()
                    .find(|(name, _)| name == field)
                    .map(|(_, ty)| ty)
                    .ok_or_else(|| fail(format!("no field `{field}`")))?
            }
            SemanticTerm::Call {
                function,
                type_arguments,
                ..
            } => {
                let (parameters, _, result) = self.signature(function)?;
                let map = parameters
                    .into_iter()
                    .zip(type_arguments.iter().map(|t| self.canonical(t)))
                    .collect();
                substitute_type(&result, &map)
            }
            SemanticTerm::FunctionRef {
                function,
                type_arguments,
            } => {
                let (parameters, value_parameters, result) = self.signature(function)?;
                let map: BTreeMap<String, SemanticType> = parameters
                    .into_iter()
                    .zip(type_arguments.iter().map(|t| self.canonical(t)))
                    .collect();
                SemanticType::Function {
                    parameters: value_parameters
                        .iter()
                        .map(|parameter| substitute_type(&parameter.r#type, &map))
                        .collect(),
                    result: Box::new(substitute_type(&result, &map)),
                }
            }
            SemanticTerm::If { then_value, .. } => self.infer(then_value, scope)?,
            SemanticTerm::Match {
                scrutinee,
                branches,
            } => {
                let scrutinee = self.infer(scrutinee, scope)?;
                let branch = branches
                    .first()
                    .ok_or_else(|| fail("a match has no branch"))?;
                let inner = self.branch_scope(&scrutinee, branch, scope)?;
                self.infer(&branch.body, &inner)?
            }
            SemanticTerm::Eq { .. }
            | SemanticTerm::Le { .. }
            | SemanticTerm::Lt { .. }
            | SemanticTerm::PropAnd { .. }
            | SemanticTerm::Implies { .. }
            | SemanticTerm::Iff { .. }
            | SemanticTerm::Forall { .. } => SemanticType::Prop,
            SemanticTerm::Add { left, .. } => self.infer(left, scope)?,
            SemanticTerm::Let {
                binder,
                value: _,
                body,
            } => {
                let inner = scope.with(&binder.name, self.canonical(&binder.r#type))?;
                self.infer(body, &inner)?
            }
            SemanticTerm::Pair { left, right } => SemanticType::Product {
                left: Box::new(self.infer(left, scope)?),
                right: Box::new(self.infer(right, scope)?),
            },
            SemanticTerm::First { value } | SemanticTerm::Second { value } => {
                match self.infer(value, scope)? {
                    SemanticType::Product { left, right } => {
                        if matches!(term, SemanticTerm::First { .. }) {
                            *left
                        } else {
                            *right
                        }
                    }
                    other => return Err(fail(format!("`{other:?}` is not a pair type"))),
                }
            }
            SemanticTerm::Lambda {
                parameters, body, ..
            } => {
                let mut inner = scope.clone();
                for parameter in parameters {
                    inner = inner.with(&parameter.name, self.canonical(&parameter.r#type))?;
                }
                SemanticType::Function {
                    parameters: parameters
                        .iter()
                        .map(|parameter| self.canonical(&parameter.r#type))
                        .collect(),
                    result: Box::new(self.infer(body, &inner)?),
                }
            }
            SemanticTerm::Apply {
                function,
                arguments,
            } => {
                let mut ty = self.infer(function, scope)?;
                let mut remaining = arguments.len();
                while remaining > 0 {
                    match ty {
                        SemanticType::Function { parameters, result } => {
                            if parameters.len() <= remaining {
                                remaining -= parameters.len();
                                ty = *result;
                            } else {
                                ty = SemanticType::Function {
                                    parameters: parameters[remaining..].to_vec(),
                                    result,
                                };
                                remaining = 0;
                            }
                        }
                        other => return Err(fail(format!("`{other:?}` is not a function type"))),
                    }
                }
                ty
            }
            SemanticTerm::MapLiteral { key, value, .. } => SemanticType::Map {
                key: Box::new(self.canonical(key)),
                value: Box::new(self.canonical(value)),
            },
            SemanticTerm::SetLiteral { element, .. } => SemanticType::Set {
                element: Box::new(self.canonical(element)),
            },
            SemanticTerm::GraphLiteral { node, .. } => SemanticType::Map {
                key: Box::new(self.canonical(node)),
                value: Box::new(SemanticType::Set {
                    element: Box::new(self.canonical(node)),
                }),
            },
            SemanticTerm::CheckedApply { .. } => {
                return Err(fail("a checked model application was not elaborated"))
            }
        })
    }

    /// The scope inside a match branch: its binders typed by the matched
    /// constructor's fields.
    fn branch_scope(
        &self,
        scrutinee: &SemanticType,
        branch: &SemanticBranch,
        scope: &Scope,
    ) -> Result<Scope, Diagnostic> {
        let fields = self.pattern_fields(scrutinee, &branch.constructor)?;
        let mut inner = scope.clone();
        for (binder, ty) in branch.binders.iter().zip(fields) {
            inner = inner.with(binder, ty)?;
        }
        Ok(inner)
    }

    /// The field types a constructor pattern binds when matching a value of
    /// `scrutinee`'s type.
    fn pattern_fields(
        &self,
        scrutinee: &SemanticType,
        constructor: &MemberRef,
    ) -> Result<Vec<SemanticType>, Diagnostic> {
        let arguments = match scrutinee {
            SemanticType::Option { value } => vec![(**value).clone()],
            SemanticType::Result { ok, error } => vec![(**ok).clone(), (**error).clone()],
            SemanticType::List { element } | SemanticType::Set { element } => {
                vec![(**element).clone()]
            }
            SemanticType::Product { left, right } => vec![(**left).clone(), (**right).clone()],
            SemanticType::Named { arguments, .. } => arguments.clone(),
            _ => Vec::new(),
        };
        let constructor = match scrutinee {
            SemanticType::Named { member, .. } if constructor.module.is_none() => {
                // A branch names a document constructor by its owner's
                // module only when that module is another one.
                match constructor.name.split_once('.') {
                    Some((owner, _))
                        if owner == member.name
                            && !crate::ir::semantic::BUILTIN_CONSTRUCTOR_OWNERS
                                .contains(&owner) =>
                    {
                        MemberRef {
                            module: member.module.clone(),
                            name: constructor.name.clone(),
                        }
                    }
                    _ => constructor.clone(),
                }
            }
            _ => constructor.clone(),
        };
        Ok(self.constructor(&constructor, &arguments)?.1)
    }

    // ------------------------------------------------------------------
    // Terms
    // ------------------------------------------------------------------

    fn nat_literal(value: &str) -> Result<BTerm, Diagnostic> {
        let parsed: u64 = value
            .parse()
            .map_err(|_| fail(format!("the numeral `{value}` is not a natural number")))?;
        if parsed > u64::from(u32::MAX) {
            return Err(fail(format!(
                "the numeral `{value}` exceeds 4294967295, the largest Bend Nat literal"
            )));
        }
        Ok(BTerm::Nat(value.to_owned()))
    }

    /// The Bend constructor term of a constructor applied to lowered
    /// fields.
    fn constructor_term(
        &mut self,
        constructor: &MemberRef,
        fields: Vec<BTerm>,
    ) -> Result<BTerm, Diagnostic> {
        if constructor.module.is_none() {
            let mut fields = fields;
            let builtin = match constructor.name.as_str() {
                "Option.none" => Some(BTerm::Constructor(synthetic("None"), Vec::new())),
                "Option.some" => Some(BTerm::Constructor(synthetic("Some"), fields.clone())),
                "Result.ok" => Some(BTerm::Constructor(synthetic("Done"), fields.clone())),
                "Result.error" => Some(BTerm::Constructor(synthetic("Fail"), fields.clone())),
                "List.nil" => Some(BTerm::Constructor(synthetic("Nil"), Vec::new())),
                "List.cons" => Some(BTerm::Constructor(synthetic("Con"), fields.clone())),
                "Bool.true" => Some(BTerm::Constructor(synthetic("True"), Vec::new())),
                "Bool.false" => Some(BTerm::Constructor(synthetic("False"), Vec::new())),
                "Nat.zero" => Some(BTerm::Nat("0".to_owned())),
                "Nat.succ" if fields.len() == 1 => Some(BTerm::Succ(Box::new(fields.remove(0)))),
                "Prod.mk" if fields.len() == 2 => {
                    let right = fields.remove(1);
                    let left = fields.remove(0);
                    Some(BTerm::Pair(Box::new(left), Box::new(right)))
                }
                name if name.starts_with("ContractViolation.")
                    || name.starts_with("ReasoningFailure.") =>
                {
                    Some(BTerm::Constructor(
                        synthetic(self.support(name)),
                        Vec::new(),
                    ))
                }
                _ => None,
            };
            if let Some(term) = builtin {
                return Ok(term);
            }
            return self
                .document_constructor(constructor)
                .map(|head| BTerm::Constructor(synthetic(head), fields));
        }
        let head = self.document_constructor(constructor)?;
        Ok(BTerm::Constructor(synthetic(head), fields))
    }

    fn document_constructor(&mut self, constructor: &MemberRef) -> Result<String, Diagnostic> {
        self.member(constructor)
    }

    /// The pattern a branch matches.
    fn pattern(
        &mut self,
        scrutinee: &SemanticType,
        constructor: &MemberRef,
        binders: &[String],
    ) -> Result<Pattern, Diagnostic> {
        let binder_names = binders
            .iter()
            .map(|binder| names::local(binder).map(synthetic))
            .collect::<Result<Vec<_>, _>>()?;
        let short = constructor.name.as_str();
        Ok(match (scrutinee, short) {
            (SemanticType::Nat, "Nat.zero" | "zero") => Pattern::Zero,
            (SemanticType::Nat, "Nat.succ" | "succ") => Pattern::Succ(
                binder_names
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| synthetic("_")),
            ),
            (SemanticType::Product { .. }, _) => {
                let mut binder_names = binder_names.into_iter();
                Pattern::Pair(
                    binder_names.next().unwrap_or_else(|| synthetic("_")),
                    binder_names.next().unwrap_or_else(|| synthetic("_")),
                )
            }
            (SemanticType::Bool, "Bool.true" | "true") => {
                Pattern::Constructor(synthetic("True"), Vec::new())
            }
            (SemanticType::Bool, "Bool.false" | "false") => {
                Pattern::Constructor(synthetic("False"), Vec::new())
            }
            (SemanticType::Option { .. }, "Option.none" | "none") => {
                Pattern::Constructor(synthetic("None"), Vec::new())
            }
            (SemanticType::Option { .. }, "Option.some" | "some") => {
                Pattern::Constructor(synthetic("Some"), binder_names)
            }
            (SemanticType::Result { .. }, "Result.ok" | "ok") => {
                Pattern::Constructor(synthetic("Done"), binder_names)
            }
            (SemanticType::Result { .. }, "Result.error" | "error") => {
                Pattern::Constructor(synthetic("Fail"), binder_names)
            }
            (SemanticType::List { .. }, "List.nil" | "nil") => {
                Pattern::Constructor(synthetic("Nil"), Vec::new())
            }
            (SemanticType::List { .. }, "List.cons" | "cons") => {
                Pattern::Constructor(synthetic("Con"), binder_names)
            }
            (SemanticType::ContractViolation | SemanticType::ReasoningFailure, name) => {
                let owner = if matches!(scrutinee, SemanticType::ContractViolation) {
                    "ContractViolation"
                } else {
                    "ReasoningFailure"
                };
                let short = name.rsplit('.').next().unwrap_or(name);
                Pattern::Constructor(
                    synthetic(self.support(&format!("{owner}.{short}"))),
                    Vec::new(),
                )
            }
            (SemanticType::Named { member, .. }, name) => {
                let short = name.rsplit('.').next().unwrap_or(name);
                let full = MemberRef {
                    module: member.module.clone(),
                    name: format!("{}.{short}", member.name),
                };
                Pattern::Constructor(synthetic(self.member(&full)?), binder_names)
            }
            (other, name) => {
                return Err(fail(format!(
                    "no Bend pattern for `{name}` over `{other:?}`"
                )))
            }
        })
    }

    /// The constructor a proof branch names, resolved against the type of
    /// the value it splits.
    fn branch_constructor(&self, scrutinee: &SemanticType, short: &str) -> MemberRef {
        let qualified = |owner: &str| MemberRef {
            module: None,
            name: format!("{owner}.{short}"),
        };
        match scrutinee {
            SemanticType::Nat => qualified("Nat"),
            SemanticType::Bool => qualified("Bool"),
            SemanticType::Option { .. } => qualified("Option"),
            SemanticType::Result { .. } => qualified("Result"),
            SemanticType::List { .. } => qualified("List"),
            SemanticType::Product { .. } => qualified("Prod"),
            SemanticType::Named { member, .. } => MemberRef {
                module: member.module.clone(),
                name: format!("{}.{short}", member.name),
            },
            _ => qualified("?"),
        }
    }

    fn arguments(
        &mut self,
        terms: &[SemanticTerm],
        scope: &Scope,
    ) -> Result<Vec<BTerm>, Diagnostic> {
        terms.iter().map(|term| self.term(term, scope)).collect()
    }

    /// A call of a definition or law: erased type arguments, then the
    /// value arguments in the callee's Bend order.
    fn call_of(
        &mut self,
        function: &MemberRef,
        type_arguments: &[SemanticType],
        arguments: Vec<BTerm>,
    ) -> Result<BTerm, Diagnostic> {
        let declaration = self.declaration(function)?;
        let order = bend_order(declaration);
        // Type parameters are templates (see `type_params`), so each type
        // argument is passed as one.
        let mut out = type_arguments
            .iter()
            .map(|argument| Ok(BTerm::Template(Box::new(self.ty(argument)?))))
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        if order.len() == arguments.len() {
            let mut slots: Vec<Option<BTerm>> = arguments.into_iter().map(Some).collect();
            for index in order {
                out.push(
                    slots[index]
                        .take()
                        .ok_or_else(|| fail("a call repeats an argument"))?,
                );
            }
        } else {
            out.extend(arguments);
        }
        Ok(BTerm::Call(synthetic(self.callee(function)?), out))
    }

    /// The Bend name a call of `function` uses.
    fn callee(&mut self, function: &MemberRef) -> Result<String, Diagnostic> {
        match self.declaration(function)? {
            SemanticDeclaration::Definition {
                termination: Some(_),
                ..
            } => {
                let home = self.home(function);
                self.spell(&home, &function.name)
            }
            _ => self.member(function),
        }
    }

    /// Lower a computational or propositional term.
    ///
    /// # Errors
    ///
    /// `LLB6008` when the term is outside what language 2.2 lowers.
    #[allow(clippy::too_many_lines)]
    pub fn term(&mut self, term: &SemanticTerm, scope: &Scope) -> Result<BTerm, Diagnostic> {
        Ok(match term {
            SemanticTerm::Var { name } if name == HOLE => BTerm::Hole,
            SemanticTerm::Var { name } => var(scope.get(name)?.0.clone()),
            SemanticTerm::Nat { value } => Self::nat_literal(value)?,
            SemanticTerm::Integer {
                representation: crate::ir::semantic::SemanticInteger::Int,
                value,
            } => {
                if let Some(magnitude) = value.strip_prefix('-') {
                    let magnitude: u64 = magnitude
                        .parse()
                        .map_err(|_| fail(format!("the integer `{value}` has no Bend spelling")))?;
                    let pred = (magnitude - 1).to_string();
                    BTerm::Constructor(
                        synthetic(self.prelude("negSucc")),
                        vec![Self::nat_literal(&pred)?],
                    )
                } else {
                    BTerm::Constructor(
                        synthetic(self.prelude("ofNat")),
                        vec![Self::nat_literal(value)?],
                    )
                }
            }
            SemanticTerm::String { value } => BTerm::Str(names::string_literal(value)),
            SemanticTerm::Bool { value } => BTerm::Constructor(
                synthetic(if *value { "True" } else { "False" }),
                Vec::new(),
            ),
            SemanticTerm::Unit => BTerm::Constructor(synthetic("Unit"), Vec::new()),
            SemanticTerm::Nil { .. } => BTerm::Constructor(synthetic("Nil"), Vec::new()),
            SemanticTerm::Cons { head, tail } => BTerm::Constructor(
                synthetic("Con"),
                vec![self.term(head, scope)?, self.term(tail, scope)?],
            ),
            SemanticTerm::Record {
                r#type,
                type_arguments,
                fields,
            } => {
                let ty = SemanticType::Named {
                    member: MemberRef {
                        module: Some(self.home(r#type)),
                        name: r#type.name.clone(),
                    },
                    arguments: type_arguments.iter().map(|t| self.canonical(t)).collect(),
                };
                let (owner, declared) = self.record_fields(&ty)?;
                let mut values = Vec::new();
                for (field, _) in &declared {
                    let assignment = fields
                        .iter()
                        .find(|assignment| &assignment.field == field)
                        .ok_or_else(|| fail(format!("the record omits `{field}`")))?;
                    values.push(self.term(&assignment.value, scope)?);
                }
                let constructor = MemberRef {
                    module: owner.module,
                    name: format!("{}.mk", owner.name),
                };
                BTerm::Constructor(synthetic(self.member(&constructor)?), values)
            }
            SemanticTerm::Constructor {
                constructor,
                arguments,
                ..
            } => {
                let fields = self.arguments(arguments, scope)?;
                self.constructor_term(constructor, fields)?
            }
            SemanticTerm::InstanceValue { resolved, .. } => {
                BTerm::Call(synthetic(self.member(resolved)?), Vec::new())
            }
            SemanticTerm::Project { value, field } => {
                let ty = self.infer(value, scope)?;
                let (owner, _) = self.record_fields(&ty)?;
                let SemanticType::Named { arguments, .. } = &ty else {
                    return Err(fail("a projection of a non-record"));
                };
                let mut args = arguments
                    .iter()
                    .map(|argument| self.ty(argument))
                    .collect::<Result<Vec<_>, _>>()?;
                args.push(self.term(value, scope)?);
                let projection = MemberRef {
                    module: owner.module,
                    name: format!("{}.{field}", owner.name),
                };
                BTerm::Call(synthetic(self.member(&projection)?), args)
            }
            SemanticTerm::Call {
                function,
                type_arguments,
                arguments,
            } => {
                let type_arguments: Vec<SemanticType> =
                    type_arguments.iter().map(|t| self.canonical(t)).collect();
                let (_, parameters, _) = self.signature(function)?;
                if !self.converts(&parameters) {
                    let lowered = self.arguments(arguments, scope)?;
                    self.call_of(function, &type_arguments, lowered)?
                } else {
                    let order = bend_order(self.declaration(function)?);
                    let args = self.call_with_closures(
                        function,
                        &type_arguments,
                        arguments,
                        &parameters,
                        &order,
                        scope,
                    )?;
                    BTerm::Call(synthetic(self.callee(function)?), args)
                }
            }
            SemanticTerm::FunctionRef {
                function,
                type_arguments,
            } => {
                let (_, parameters, _) = self.signature(function)?;
                let names: Vec<String> = parameters.iter().map(|_| self.fresh("x")).collect();
                let type_arguments: Vec<SemanticType> =
                    type_arguments.iter().map(|t| self.canonical(t)).collect();
                let mut body =
                    self.call_of(function, &type_arguments, names.iter().map(var).collect())?;
                for (name, parameter) in names.iter().zip(&parameters).rev() {
                    let marked = if self.is_data(&parameter.r#type) {
                        format!("+{name}")
                    } else {
                        name.clone()
                    };
                    body = BTerm::Lam(synthetic(marked), Box::new(body));
                }
                body
            }
            SemanticTerm::If {
                condition,
                then_value,
                else_value,
            } => {
                let ty = self.infer(then_value, scope)?;
                let ty = self.ty(&ty)?;
                let head = self.support("ite");
                call(
                    head,
                    vec![
                        ty,
                        self.term(condition, scope)?,
                        self.term(then_value, scope)?,
                        self.term(else_value, scope)?,
                    ],
                )
            }
            SemanticTerm::Match {
                scrutinee,
                branches,
            } => self.lifted_match(scrutinee, branches, scope)?,
            SemanticTerm::Eq { left, right } => {
                let ty = self.infer(left, scope)?;
                let ty = self.ty(&ty)?;
                BTerm::Equal(
                    Box::new(self.term(left, scope)?),
                    Box::new(self.term(right, scope)?),
                    Box::new(ty),
                )
            }
            SemanticTerm::Le { left, right } | SemanticTerm::Lt { left, right } => {
                let ty = self.infer(left, scope)?;
                let less = matches!(term, SemanticTerm::Lt { .. });
                let head = match ty {
                    SemanticType::Nat => self.support(if less { "lt" } else { "le" }),
                    SemanticType::Int => self.prelude(if less { "Lean.Int.lt" } else { "Lean.Int.le" }),
                    other => {
                        return Err(fail(format!("no Bend order on `{other:?}`")));
                    }
                };
                call(head, vec![self.term(left, scope)?, self.term(right, scope)?])
            }
            SemanticTerm::Add { left, right } => {
                let ty = self.infer(left, scope)?;
                let head = match ty {
                    SemanticType::Nat => self.prelude("Lean.Nat.add"),
                    SemanticType::Int => self.prelude("Lean.Int.add"),
                    other => return Err(fail(format!("no Bend addition on `{other:?}`"))),
                };
                call(head, vec![self.term(left, scope)?, self.term(right, scope)?])
            }
            SemanticTerm::Beq { left, right }
            | SemanticTerm::Ble { left, right }
            | SemanticTerm::Blt { left, right } => {
                let head = self.prelude(match term {
                    SemanticTerm::Beq { .. } => "Lean.Nat.beq",
                    SemanticTerm::Ble { .. } => "Lean.Nat.ble",
                    _ => "Lean.Nat.blt",
                });
                call(head, vec![self.term(left, scope)?, self.term(right, scope)?])
            }
            SemanticTerm::And { left, right } | SemanticTerm::Or { left, right } => {
                let head = self.prelude(if matches!(term, SemanticTerm::And { .. }) {
                    "Lean.Bool.and"
                } else {
                    "Lean.Bool.or"
                });
                call(head, vec![self.term(left, scope)?, self.term(right, scope)?])
            }
            SemanticTerm::Not { value } => {
                let head = self.prelude("Lean.Bool.not");
                call(head, vec![self.term(value, scope)?])
            }
            SemanticTerm::PropAnd { left, right } => {
                let (left, right) = (self.term(left, scope)?, self.term(right, scope)?);
                if self.prop_is_data(&left) && self.prop_is_data(&right) {
                    call(self.prelude("Lean.Prod"), vec![left, right])
                } else {
                    BTerm::Product(Box::new(left), Box::new(right))
                }
            }
            SemanticTerm::Implies {
                premise,
                conclusion,
            } => BTerm::Pi {
                name: None,
                erased: false,
                domain: Box::new(self.term(premise, scope)?),
                codomain: Box::new(self.term(conclusion, scope)?),
            },
            SemanticTerm::Iff { left, right } => {
                let (l, r) = (self.term(left, scope)?, self.term(right, scope)?);
                let arrow = |a: &BTerm, b: &BTerm| BTerm::Pi {
                    name: None,
                    erased: false,
                    domain: Box::new(a.clone()),
                    codomain: Box::new(b.clone()),
                };
                BTerm::Product(Box::new(arrow(&l, &r)), Box::new(arrow(&r, &l)))
            }
            SemanticTerm::Forall { binder, body } => {
                let ty = self.canonical(&binder.r#type);
                let inner = scope.with(&binder.name, ty.clone())?;
                BTerm::Pi {
                    name: Some(synthetic(inner.get(&binder.name)?.0.clone())),
                    erased: false,
                    domain: Box::new(self.ty(&ty)?),
                    codomain: Box::new(self.term(body, &inner)?),
                }
            }
            SemanticTerm::Let {
                binder,
                value,
                body,
            } => {
                let ty = self.canonical(&binder.r#type);
                let inner = scope.with(&binder.name, ty.clone())?;
                if self.infer(body, &inner)? == SemanticType::Prop {
                    // A proposition is read up to definitional unfolding,
                    // so its `let` is unfolded: Bend admits statements only
                    // in bodies.
                    let unfolded = normal::substitute(body, &binder.name, value);
                    return self.term(&unfolded, scope);
                }
                let name = synthetic(inner.get(&binder.name)?.0.clone());
                let value = self.term(value, scope)?;
                let tail = self.term(body, &inner)?;
                let stmt = if self.is_data(&ty) {
                    Stmt::Share {
                        name,
                        value,
                        source: here(),
                    }
                } else {
                    Stmt::Let {
                        name,
                        value,
                        source: here(),
                    }
                };
                BTerm::Block(Box::new(Body {
                    stmts: vec![stmt],
                    tail: Tail::Term(tail, here()),
                }))
            }
            SemanticTerm::Pair { left, right } => BTerm::Pair(
                Box::new(self.term(left, scope)?),
                Box::new(self.term(right, scope)?),
            ),
            SemanticTerm::First { value } | SemanticTerm::Second { value } => {
                let SemanticType::Product { left, right } = self.infer(value, scope)? else {
                    return Err(fail("a projection of a non-pair"));
                };
                let head = self.support(if matches!(term, SemanticTerm::First { .. }) {
                    "fst"
                } else {
                    "snd"
                });
                call(
                    head,
                    vec![self.ty(&left)?, self.ty(&right)?, self.term(value, scope)?],
                )
            }
            SemanticTerm::Lambda {
                parameters, body, ..
            } => {
                let mut inner = scope.clone();
                let mut binders = Vec::new();
                for parameter in parameters {
                    let ty = self.canonical(&parameter.r#type);
                    inner = inner.with(&parameter.name, ty.clone())?;
                    let spelled = inner.get(&parameter.name)?.0.clone();
                    binders.push(if self.is_data(&ty) {
                        format!("+{spelled}")
                    } else {
                        spelled
                    });
                }
                let mut out = self.term(body, &inner)?;
                for binder in binders.into_iter().rev() {
                    out = BTerm::Lam(synthetic(binder), Box::new(out));
                }
                out
            }
            SemanticTerm::Apply {
                function,
                arguments,
            } => {
                let lowered = self.arguments(arguments, scope)?;
                match function.as_ref() {
                    SemanticTerm::Var { name } => self.apply_local(name, lowered, scope)?,
                    other => BTerm::Apply(Box::new(self.term(other, scope)?), lowered),
                }
            }
            SemanticTerm::MapLiteral { entries, .. } => {
                let mut out = BTerm::Constructor(synthetic("Nil"), Vec::new());
                for entry in entries.iter().rev() {
                    let pair = BTerm::Pair(
                        Box::new(self.term(&entry.key, scope)?),
                        Box::new(self.term(&entry.value, scope)?),
                    );
                    out = BTerm::Constructor(synthetic("Con"), vec![pair, out]);
                }
                out
            }
            SemanticTerm::SetLiteral { elements, .. } => {
                let mut out = BTerm::Constructor(synthetic("Nil"), Vec::new());
                for element in elements.iter().rev() {
                    out = BTerm::Constructor(
                        synthetic("Con"),
                        vec![self.term(element, scope)?, out],
                    );
                }
                out
            }
            SemanticTerm::GraphLiteral { nodes, edges, .. } => {
                let mut out = BTerm::Constructor(synthetic("Nil"), Vec::new());
                for source in nodes.iter().rev() {
                    let mut targets = BTerm::Constructor(synthetic("Nil"), Vec::new());
                    for edge in edges.iter().filter(|edge| edge.source == *source).rev() {
                        targets = BTerm::Constructor(
                            synthetic("Con"),
                            vec![self.term(&edge.target, scope)?, targets],
                        );
                    }
                    let pair =
                        BTerm::Pair(Box::new(self.term(source, scope)?), Box::new(targets));
                    out = BTerm::Constructor(synthetic("Con"), vec![pair, out]);
                }
                out
            }
            SemanticTerm::Primitive {
                operation,
                arguments,
                result,
            } if self.arithmetic(*operation, &self.canonical(result)).is_some() => {
                let head = self
                    .arithmetic(*operation, &self.canonical(result))
                    .ok_or_else(|| fail("an arithmetic primitive lost its head"))?;
                let head = self.prelude(head);
                call(head, self.arguments(arguments, scope)?)
            }
            SemanticTerm::Integer { .. }
            | SemanticTerm::Bytes { .. }
            | SemanticTerm::Primitive { .. } => {
                return Err(fail(
                    "fixed-width integers, byte strings and runtime primitives have no Bend lowering in language 2.2",
                ))
            }
            SemanticTerm::CheckedApply { .. } => {
                return Err(fail("a checked model application was not elaborated"))
            }
        })
    }

    /// Whether a lowered proposition is a Bend type of kind `Data`.
    fn prop_is_data(&self, prop: &BTerm) -> bool {
        match prop {
            BTerm::Equal(..) => true,
            BTerm::Call(head, _) => {
                head.text == format!("{SUPPORT_ALIAS}.Sem.le")
                    || head.text == format!("{SUPPORT_ALIAS}.Sem.lt")
                    || head.text == format!("{PRELUDE_ALIAS}.Lean.Prod")
            }
            _ => false,
        }
    }

    /// A `match` on a computed value or inside a term: an auxiliary def
    /// that matches its first parameter and takes every free local after
    /// it.
    /// The prelude function of an arithmetic primitive on `Nat` or `Int`
    /// that is exactly a Lean operation (truncated subtraction on `Nat`).
    /// Quotient and remainder take a zero case and round toward zero, so
    /// they are the runtime's, not the prelude's.
    fn arithmetic(
        &self,
        operation: SemanticPrimitive,
        result: &SemanticType,
    ) -> Option<&'static str> {
        Some(match (operation, result) {
            (SemanticPrimitive::Subtract, SemanticType::Nat) => "Lean.Nat.sub",
            (SemanticPrimitive::Multiply, SemanticType::Nat) => "Lean.Nat.mul",
            (SemanticPrimitive::Subtract, SemanticType::Int) => "Lean.Int.sub",
            (SemanticPrimitive::Multiply, SemanticType::Int) => "Lean.Int.mul",
            (SemanticPrimitive::Negate, SemanticType::Int) => "Lean.Int.neg",
            _ => return None,
        })
    }

    fn lifted_match(
        &mut self,
        scrutinee: &SemanticTerm,
        branches: &[SemanticBranch],
        scope: &Scope,
    ) -> Result<BTerm, Diagnostic> {
        let scrutinee_type = self.infer(scrutinee, scope)?;
        let result_type = {
            let branch = branches
                .first()
                .ok_or_else(|| fail("a match has no branch"))?;
            let inner = self.branch_scope(&scrutinee_type, branch, scope)?;
            self.infer(&branch.body, &inner)?
        };
        let mut free = BTreeSet::new();
        for branch in branches {
            let mut bound: BTreeSet<String> = branch.binders.iter().cloned().collect();
            normal::free_vars(&branch.body, &mut bound, &mut free);
        }
        let free: Vec<(String, String, SemanticType)> = free
            .into_iter()
            .filter_map(|name| {
                scope
                    .locals
                    .get(&name)
                    .map(|(spelled, ty)| (name.clone(), spelled.clone(), ty.clone()))
            })
            .collect();
        let name = self.fresh("match");
        let target = self.fresh("v");
        let mut params = Vec::new();
        for type_parameter in self.type_parameters.clone() {
            params.push(Param {
                quantity: Quantity::Template,
                name: synthetic(names::local(&type_parameter)?),
                ty: BTerm::Kind("Data"),
                source: here(),
            });
        }
        params.push(self.param(&target, &scrutinee_type)?);
        let mut inner = Scope::default();
        for (source, spelled, ty) in &free {
            params.push(self.param(spelled, ty)?);
            inner
                .locals
                .insert(source.clone(), (spelled.clone(), ty.clone()));
        }
        let mut cases = Vec::new();
        for branch in branches {
            let pattern = self.pattern(&scrutinee_type, &branch.constructor, &branch.binders)?;
            let branch_scope = self.branch_scope(&scrutinee_type, branch, &inner)?;
            let body = self.term(&branch.body, &branch_scope)?;
            cases.push((pattern, Body::term(body, here())));
        }
        let result = self.ty(&result_type)?;
        self.aux.push(Item::Def {
            name: synthetic(name.clone()),
            params,
            result,
            result_source: here(),
            body: Body {
                stmts: Vec::new(),
                tail: Tail::Match {
                    scrutinee: synthetic(target),
                    cases,
                    source: here(),
                },
            },
            source: here(),
        });
        let mut args: Vec<BTerm> = self
            .type_parameters
            .clone()
            .iter()
            .map(|type_parameter| {
                names::local(type_parameter).map(|t| BTerm::Template(Box::new(var(t))))
            })
            .collect::<Result<_, _>>()?;
        args.push(self.term(scrutinee, scope)?);
        args.extend(free.iter().map(|(_, spelled, _)| var(spelled.clone())));
        Ok(BTerm::Call(synthetic(name), args))
    }

    /// A parameter, reusable when its type is `Data`.
    fn param(&mut self, spelled: &str, ty: &SemanticType) -> Result<Param, Diagnostic> {
        Ok(Param {
            quantity: if self.is_data(ty) {
                Quantity::Reusable
            } else {
                Quantity::Affine
            },
            name: synthetic(spelled),
            ty: self.ty(ty)?,
            source: here(),
        })
    }

    // ------------------------------------------------------------------
    // Declarations
    // ------------------------------------------------------------------

    fn type_params(&mut self, type_parameters: &[String]) -> Result<Vec<Param>, Diagnostic> {
        self.type_parameters = type_parameters.iter().cloned().collect();
        type_parameters
            .iter()
            .map(|name| {
                Ok(Param {
                    quantity: Quantity::Template,
                    name: synthetic(names::local(name)?),
                    ty: BTerm::Kind("Data"),
                    source: here(),
                })
            })
            .collect()
    }

    /// Lower one declaration to its Bend items.
    ///
    /// # Errors
    ///
    /// `LLB6008` when it has no Bend lowering.
    #[allow(clippy::too_many_lines)]
    pub fn declaration_items(
        &mut self,
        declaration: &SemanticDeclaration,
    ) -> Result<Vec<Item>, Diagnostic> {
        self.type_parameters.clear();
        let mut items = match declaration {
            SemanticDeclaration::Structure {
                name,
                type_parameters,
                fields,
                ..
            }
            | SemanticDeclaration::Class {
                name,
                type_parameters,
                fields,
                ..
            } => self.record(name, type_parameters, fields)?,
            SemanticDeclaration::Inductive {
                name,
                type_parameters,
                constructors,
                ..
            } => {
                let spelled = names::global(name)?;
                let parameters = type_parameters
                    .iter()
                    .map(|p| names::local(p).map(synthetic))
                    .collect::<Result<Vec<_>, _>>()?;
                let self_type = SemanticType::Named {
                    member: MemberRef {
                        module: None,
                        name: name.clone(),
                    },
                    arguments: type_parameters
                        .iter()
                        .map(|p| SemanticType::Parameter { name: p.clone() })
                        .collect(),
                };
                let kind = if self.is_data(&self.canonical(&self_type)) {
                    "Data"
                } else {
                    "Type"
                };
                let mut lowered = Vec::new();
                for constructor in constructors {
                    let mut fields = Vec::new();
                    for (index, field) in constructor.fields.iter().enumerate() {
                        fields.push((
                            synthetic(format!("a{index}")),
                            self.ty(&self.canonical(field))?,
                        ));
                    }
                    lowered.push((
                        synthetic(names::global(&format!("{name}.{}", constructor.name))?),
                        fields,
                    ));
                }
                vec![Item::Type {
                    name: synthetic(spelled),
                    parameters,
                    kind,
                    constructors: lowered,
                    source: here(),
                }]
            }
            SemanticDeclaration::Instance {
                name,
                class,
                arguments,
                fields,
                ..
            } => {
                let ty = SemanticType::Named {
                    member: MemberRef {
                        module: Some(self.home(class)),
                        name: class.name.clone(),
                    },
                    arguments: arguments.iter().map(|t| self.canonical(t)).collect(),
                };
                let record = SemanticTerm::Record {
                    r#type: class.clone(),
                    type_arguments: arguments.clone(),
                    fields: fields.clone(),
                };
                let body = self.term(&record, &Scope::default())?;
                vec![Item::Def {
                    name: synthetic(names::global(name)?),
                    params: Vec::new(),
                    result: self.ty(&ty)?,
                    result_source: here(),
                    body: Body::term(body, here()),
                    source: here(),
                }]
            }
            SemanticDeclaration::Definition {
                mutual: Some(key), ..
            } => self.mutual_group(key)?,
            SemanticDeclaration::Definition { body, .. } => {
                vec![self.definition(declaration, body)?]
            }
            SemanticDeclaration::Theorem { .. } => proof::theorem(self, declaration)?,
            other => {
                return Err(fail(format!(
                    "the declaration `{}` was not elaborated to ordinary declarations",
                    other.name()
                )))
            }
        };
        let mut out = std::mem::take(&mut self.aux);
        out.append(&mut items);
        Ok(out)
    }

    fn record(
        &mut self,
        name: &str,
        type_parameters: &[String],
        fields: &[crate::ir::semantic::SemanticField],
    ) -> Result<Vec<Item>, Diagnostic> {
        let spelled = names::global(name)?;
        let parameters = type_parameters
            .iter()
            .map(|p| names::local(p).map(synthetic))
            .collect::<Result<Vec<_>, _>>()?;
        let self_type = SemanticType::Named {
            member: MemberRef {
                module: Some(self.module.clone()),
                name: name.to_owned(),
            },
            arguments: type_parameters
                .iter()
                .map(|p| SemanticType::Parameter { name: p.clone() })
                .collect(),
        };
        let kind = if self.is_data(&self_type) {
            "Data"
        } else {
            "Type"
        };
        let mut lowered_fields = Vec::new();
        for field in fields {
            lowered_fields.push((
                synthetic(names::local(&field.name)?),
                self.ty(&self.canonical(&field.r#type))?,
            ));
        }
        let constructor = names::global(&format!("{name}.mk"))?;
        let mut items = vec![Item::Type {
            name: synthetic(spelled),
            parameters: parameters.clone(),
            kind,
            constructors: vec![(synthetic(constructor.clone()), lowered_fields.clone())],
            source: here(),
        }];
        // Each projection matches the one constructor, as Lean's projection
        // reduces on a constructor application.
        let self_bend = self.ty(&self_type)?;
        for (index, field) in fields.iter().enumerate() {
            let mut params: Vec<Param> = parameters
                .iter()
                .map(|p| Param {
                    quantity: Quantity::Erased,
                    name: p.clone(),
                    ty: BTerm::Kind("Data"),
                    source: here(),
                })
                .collect();
            params.push(Param {
                quantity: Quantity::Affine,
                name: synthetic("ll_record"),
                ty: self_bend.clone(),
                source: here(),
            });
            let binders: Vec<Name> = (0..fields.len())
                .map(|i| synthetic(format!("ll_f{i}")))
                .collect();
            items.push(Item::Def {
                name: synthetic(names::global(&format!("{name}.{}", field.name))?),
                params,
                result: lowered_fields[index].1.clone(),
                result_source: here(),
                body: Body {
                    stmts: Vec::new(),
                    tail: Tail::Match {
                        scrutinee: synthetic("ll_record"),
                        cases: vec![(
                            Pattern::Constructor(synthetic(constructor.clone()), binders),
                            Body::term(var(format!("ll_f{index}")), here()),
                        )],
                        source: here(),
                    },
                },
                source: here(),
            });
        }
        Ok(items)
    }

    #[allow(clippy::too_many_lines)]
    /// Every member of the mutual group `key`, at its first member; the
    /// later members lower to nothing (see `mutual`).
    fn mutual_group(&mut self, key: &str) -> Result<Vec<Item>, Diagnostic> {
        if !self.mutual_done.insert(key.to_owned()) {
            return Ok(Vec::new());
        }
        let unit = self.project.units.get(&self.module).ok_or_else(|| {
            fail(format!(
                "the module `{}` has no semantic lowering",
                self.module
            ))
        })?;
        let members: Vec<&SemanticDeclaration> = unit
            .order
            .iter()
            .copied()
            .filter(|declaration| {
                matches!(declaration, SemanticDeclaration::Definition { mutual: Some(other), .. } if other == key)
            })
            .collect();
        let plan = mutual::plan(&members, &self.module, key)?;
        let mut items = Vec::new();
        for name in &plan.order {
            let declaration = members
                .iter()
                .find(|declaration| declaration.name() == name)
                .ok_or_else(|| fail("a planned member vanished"))?;
            self.type_parameters.clear();
            let item = self.definition(declaration, &plan.bodies[name])?;
            items.append(&mut self.aux);
            items.push(item);
        }
        Ok(items)
    }

    /// The body of a definition in tail position. A `match` on a local
    /// anywhere outside a binder is floated up to a `match` statement, its
    /// context copied into each branch: Bend matches only as a statement,
    /// and a match lifted into an auxiliary definition could not make the
    /// recursive calls its branches make (the auxiliary is not the
    /// recursive definition, and is defined above it).
    fn tail_body(&mut self, term: &SemanticTerm, scope: &Scope) -> Result<Body, Diagnostic> {
        match term {
            SemanticTerm::Match {
                scrutinee,
                branches,
            } if scope.matchable(scrutinee) => {
                let SemanticTerm::Var { name } = scrutinee.as_ref() else {
                    return Err(fail("a matchable scrutinee is not a local"));
                };
                let (spelled, ty) = scope.get(name)?.clone();
                let mut cases = Vec::new();
                for branch in branches {
                    let pattern = self.pattern(&ty, &branch.constructor, &branch.binders)?;
                    let inner = self.branch_scope(&ty, branch, scope)?;
                    cases.push((pattern, self.tail_body(&branch.body, &inner)?));
                }
                Ok(Body {
                    stmts: Vec::new(),
                    tail: Tail::Match {
                        scrutinee: synthetic(spelled),
                        cases,
                        source: here(),
                    },
                })
            }
            SemanticTerm::Let {
                binder,
                value,
                body,
            } if self.infer(term, scope)? != SemanticType::Prop => {
                let ty = self.canonical(&binder.r#type);
                let inner = scope.with_let(&binder.name, ty.clone())?;
                let name = synthetic(inner.get(&binder.name)?.0.clone());
                let value = self.term(value, scope)?;
                let stmt = if self.is_data(&ty) {
                    Stmt::Share {
                        name,
                        value,
                        source: here(),
                    }
                } else {
                    Stmt::Let {
                        name,
                        value,
                        source: here(),
                    }
                };
                let mut rest = self.tail_body(body, &inner)?;
                rest.stmts.insert(0, stmt);
                Ok(rest)
            }
            _ => {
                let mut sites = Vec::new();
                normal::subterms(term, &mut Vec::new(), &mut sites);
                let site = sites.into_iter().find(|(path, subterm)| {
                    !path.is_empty()
                        && matches!(subterm, SemanticTerm::Match { scrutinee, .. } if scope.matchable(scrutinee))
                });
                let Some((
                    path,
                    SemanticTerm::Match {
                        scrutinee,
                        branches,
                    },
                )) = site
                else {
                    return Ok(Body::term(self.term(term, scope)?, here()));
                };
                let mut taken = BTreeSet::new();
                normal::free_vars(term, &mut BTreeSet::new(), &mut taken);
                taken.extend(scope.locals.keys().cloned());
                let mut floated = Vec::new();
                for branch in &branches {
                    // A binder is renamed when the copied context could
                    // capture it.
                    let mut renaming = BTreeMap::new();
                    let mut binders = Vec::new();
                    for binder in &branch.binders {
                        let mut chosen = binder.clone();
                        let mut suffix = 0;
                        while taken.contains(&chosen) {
                            suffix += 1;
                            chosen = format!("{binder}{suffix}");
                        }
                        taken.insert(chosen.clone());
                        if &chosen != binder {
                            renaming.insert(
                                binder.clone(),
                                SemanticTerm::Var {
                                    name: chosen.clone(),
                                },
                            );
                        }
                        binders.push(chosen);
                    }
                    let body = normal::substitute_all(&branch.body, &renaming);
                    floated.push(crate::ir::semantic::SemanticBranch {
                        constructor: branch.constructor.clone(),
                        binders,
                        body: normal::replace_at(term, &path, &body),
                    });
                }
                self.tail_body(
                    &SemanticTerm::Match {
                        scrutinee,
                        branches: floated,
                    },
                    scope,
                )
            }
        }
    }

    fn definition(
        &mut self,
        declaration: &SemanticDeclaration,
        body: &SemanticTerm,
    ) -> Result<Item, Diagnostic> {
        let SemanticDeclaration::Definition {
            name,
            type_parameters,
            parameters,
            result,
            termination,
            ..
        } = declaration
        else {
            return Err(fail("not a definition"));
        };
        if termination.is_some() {
            return self.well_founded(declaration);
        }
        let mut params = self.type_params(type_parameters)?;
        let order = bend_order(declaration);
        let (values, scope) = self.value_params(parameters, &order)?;
        params.extend(values);
        let result_type = self.canonical(result);
        let body_out = self.tail_body(body, &scope)?;
        // A predicate built from equations is `Data`, so its proofs stay
        // reusable where it is used.
        let result_bend = if result_type == SemanticType::Prop {
            match &body_out.tail {
                Tail::Term(term, _) if body_out.stmts.is_empty() && self.prop_is_data(term) => {
                    BTerm::Kind("Data")
                }
                _ => BTerm::Kind("Type"),
            }
        } else {
            self.ty(&result_type)?
        };
        Ok(Item::Def {
            name: synthetic(names::global(name)?),
            params,
            result: result_bend,
            result_source: here(),
            body: body_out,
            source: here(),
        })
    }

    /// A well-founded definition counts down a `Nat` fuel set to its
    /// measure plus one: the evidence proves the measure decreases at every
    /// recursive call, so the fuel never runs out on any input and the
    /// result equals Lean's.
    fn well_founded(&mut self, declaration: &SemanticDeclaration) -> Result<Item, Diagnostic> {
        let SemanticDeclaration::Definition { name, .. } = declaration else {
            return Err(fail("not a definition"));
        };
        Err(fail(format!(
            "the well-founded definition `{name}` has no Bend lowering in language 2.2"
        )))
    }
}

/// Render one semantic module's `.bend`, traced declaration by declaration
/// to its source, as the semantic Lean module is.
///
/// # Errors
///
/// `LLB6008` when a construct has no Bend lowering.
pub fn render_module(
    checked: &CheckedModule,
    module: &SemanticModule,
    project: &SemanticProject<'_>,
    name: &str,
) -> Result<(Emitter, bool, bool), Diagnostic> {
    let mut lower = Lower::new(project, name);
    let mut chunks: Vec<String> = Vec::new();
    for (index, source) in module.declarations.iter().enumerate() {
        let declarations: Vec<&SemanticDeclaration> = match module.elaborated(index) {
            Some(elaborated) => elaborated.iter().collect(),
            None => vec![source],
        };
        let mut items = Vec::new();
        for declaration in declarations {
            items.extend(lower.declaration_items(declaration)?);
        }
        let mut text = String::new();
        for printed in print_items(&items) {
            text.push('\n');
            text.push_str(&printed);
        }
        chunks.push(text);
    }
    let own_path = crate::backend::bend::module_path(&checked.document.lean_module);
    let mut text = String::from("import Base\n");
    let mut import = |path: &str, alias: &str| {
        text.push_str(&format!(
            "import {} as {alias}\n",
            crate::backend::bend::relative(&own_path, path)
        ));
    };
    if lower.uses_prelude || lower.uses_support {
        import(
            crate::backend::bend::prelude::PRELUDE_BUILD_PATH,
            PRELUDE_ALIAS,
        );
    }
    if lower.uses_support {
        import(SUPPORT_BUILD_PATH, SUPPORT_ALIAS);
    }
    for (_, generated) in lower.imports() {
        import(
            &crate::backend::bend::module_path(&generated),
            &module_alias(&generated),
        );
    }
    let mut starts = Vec::new();
    for chunk in &chunks {
        starts.push(text.len());
        text.push_str(chunk);
    }
    let end = text.len();
    let emitter = crate::backend::semantic::emit_declarations_for(
        checked,
        &text,
        "semantic-bend-module",
        &starts,
        end,
        &crate::backend::semantic::DeclarationSource {
            control: "\\semanticdata{",
            owner: "lexlean.core::semanticdata",
            environment: "semanticmodule",
            notation_owner: "lexlean.core::semanticsource",
            node: "semantic-declaration",
            skip_blank: false,
        },
    )?;
    Ok((
        emitter,
        lower.uses_prelude || lower.uses_support,
        lower.uses_support,
    ))
}
