//! Closure conversion of function parameters.
//!
//! Bend shares a function value only as a template, a `~` binder that each
//! use substitutes with a *closed* argument, and a function hypothesis is
//! otherwise used at most once. A higher-order definition uses its function
//! parameter at every recursive step, so each function parameter `f` is
//! split in two:
//!
//! - its code, the template `~f: @+e: E -> A -> B`, closed at every call;
//! - its environment, the runtime `Data` value `+e: E`, with `E` itself a
//!   template type.
//!
//! An application `f(a)` becomes `f(e, a)`. A function argument is converted
//! where it is passed: a function parameter passes its own code and
//! environment, a function reference passes its eta-expansion with the
//! empty environment `Unit`, and a lambda passes a closed code that rebinds
//! the locals it captures from the tuple of their values, which is its
//! environment. A function that is the *result* of a definition is an
//! ordinary Bend function value; it is used once, where it is applied.
//!
//! A parameter whose type is neither data nor a function, such as a record
//! of functions, can be shared only as a template too; it is one, and its
//! argument must be closed where it is passed.

use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Param, Quantity, Stmt, Tail};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{MemberRef, SemanticParameter, SemanticTerm, SemanticType};

use super::{call, here, normal, synthetic, var, Lower, Scope};

/// A converted function parameter in scope: the Bend spellings of its code
/// template, its environment, and the environment's template type.
#[derive(Clone, Debug)]
pub struct Closure {
    pub code: String,
    pub env: String,
    pub env_type: BTerm,
}

/// One converted function argument: its environment type, its closed code,
/// and its environment value.
pub(super) struct Converted {
    pub env_type: BTerm,
    pub code: BTerm,
    pub env: BTerm,
}

fn unit_type() -> BTerm {
    var("Unit")
}

fn unit_value() -> BTerm {
    BTerm::Constructor(synthetic("Unit"), Vec::new())
}

impl Lower<'_, '_> {
    /// The Bend type of a function: a chain of arrows whose `Data` domains
    /// bind `+x`, as a lambda over a `Data` value does.
    pub(super) fn function_type(
        &mut self,
        parameters: &[SemanticType],
        result: &SemanticType,
    ) -> Result<BTerm, Diagnostic> {
        let mut out = self.ty(result)?;
        for parameter in parameters.iter().rev() {
            let canonical = self.canonical(parameter);
            out = BTerm::Pi {
                name: self.is_data(&canonical).then(|| synthetic("+x")),
                erased: false,
                domain: Box::new(self.ty(&canonical)?),
                codomain: Box::new(out),
            };
        }
        Ok(out)
    }

    /// The positions of a callable's function parameters.
    pub(super) fn function_slots(&self, parameters: &[SemanticParameter]) -> Vec<usize> {
        parameters
            .iter()
            .enumerate()
            .filter(|(_, parameter)| {
                matches!(
                    self.canonical(&parameter.r#type),
                    SemanticType::Function { .. }
                )
            })
            .map(|(index, _)| index)
            .collect()
    }

    /// The positions of a callable's parameters that are neither data nor
    /// functions, which are templates.
    pub(super) fn template_slots(&self, parameters: &[SemanticParameter]) -> Vec<usize> {
        parameters
            .iter()
            .enumerate()
            .filter(|(_, parameter)| {
                let ty = self.canonical(&parameter.r#type);
                !self.is_data(&ty)
                    && !matches!(
                        ty,
                        SemanticType::Function { .. } | SemanticType::Prop | SemanticType::Type
                    )
            })
            .map(|(index, _)| index)
            .collect()
    }

    /// Whether calls of a callable with these parameters need conversion.
    pub(super) fn converts(&self, parameters: &[SemanticParameter]) -> bool {
        !self.function_slots(parameters).is_empty() || !self.template_slots(parameters).is_empty()
    }

    /// The Bend binders of a callable's value parameters, taken in `order`,
    /// and the scope they bind. Every function parameter contributes a
    /// template environment type and a template code ahead of all value
    /// binders, and its environment in its own place.
    pub(super) fn value_params(
        &mut self,
        parameters: &[SemanticParameter],
        order: &[usize],
    ) -> Result<(Vec<Param>, Scope), Diagnostic> {
        let mut scope = Scope::default();
        for parameter in parameters {
            scope = scope.with(&parameter.name, self.canonical(&parameter.r#type))?;
        }
        let slots = self.function_slots(parameters);
        let mut types = Vec::new();
        let mut codes = Vec::new();
        for slot in &slots {
            let parameter = &parameters[*slot];
            let spelled = scope.get(&parameter.name)?.0.clone();
            let env_type = format!("ll_E_{spelled}");
            let SemanticType::Function {
                parameters: domain,
                result,
            } = self.canonical(&parameter.r#type)
            else {
                return Err(fail("a function slot lost its type"));
            };
            let function = self.function_type(&domain, &result)?;
            types.push(Param {
                quantity: Quantity::Template,
                name: synthetic(env_type.clone()),
                ty: BTerm::Kind("Data"),
                source: here(),
            });
            codes.push(Param {
                quantity: Quantity::Template,
                name: synthetic(spelled.clone()),
                ty: BTerm::Pi {
                    name: Some(synthetic("+ll_e")),
                    erased: false,
                    domain: Box::new(var(env_type.clone())),
                    codomain: Box::new(function),
                },
                source: here(),
            });
            scope.closures.insert(
                parameter.name.clone(),
                Closure {
                    code: spelled.clone(),
                    env: format!("ll_env_{spelled}"),
                    env_type: var(env_type),
                },
            );
        }
        let templates = self.template_slots(parameters);
        let mut params = types;
        params.append(&mut codes);
        for slot in &templates {
            let (spelled, ty) = scope.get(&parameters[*slot].name)?.clone();
            params.push(Param {
                quantity: Quantity::Template,
                name: synthetic(spelled),
                ty: self.ty(&ty)?,
                source: here(),
            });
        }
        for index in order {
            let parameter = &parameters[*index];
            if templates.contains(index) {
                continue;
            }
            if let Some(closure) = scope.closures.get(&parameter.name) {
                params.push(Param {
                    quantity: Quantity::Reusable,
                    name: synthetic(closure.env.clone()),
                    ty: closure.env_type.clone(),
                    source: here(),
                });
            } else {
                let (spelled, ty) = scope.get(&parameter.name)?.clone();
                params.push(self.param(&spelled, &ty)?);
            }
        }
        Ok((params, scope))
    }

    /// The application of a local function: a converted parameter takes
    /// its environment first.
    pub(super) fn apply_local(
        &mut self,
        name: &str,
        arguments: Vec<BTerm>,
        scope: &Scope,
    ) -> Result<BTerm, Diagnostic> {
        if let Some(closure) = scope.closures.get(name) {
            let mut args = vec![var(closure.env.clone())];
            args.extend(arguments);
            return Ok(BTerm::Call(synthetic(closure.code.clone()), args));
        }
        Ok(BTerm::Call(
            synthetic(scope.get(name)?.0.clone()),
            arguments,
        ))
    }

    /// A call of a callable with function parameters: template types, then
    /// each function argument's environment type and code, then the value
    /// arguments in Bend order with each function argument's environment in
    /// its place.
    pub(super) fn call_with_closures(
        &mut self,
        function: &MemberRef,
        type_arguments: &[SemanticType],
        arguments: &[SemanticTerm],
        parameters: &[SemanticParameter],
        order: &[usize],
        scope: &Scope,
    ) -> Result<Vec<BTerm>, Diagnostic> {
        let slots = self.function_slots(parameters);
        let mut out = type_arguments
            .iter()
            .map(|argument| Ok(BTerm::Template(Box::new(self.ty(argument)?))))
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        let mut converted = std::collections::BTreeMap::new();
        for slot in &slots {
            let argument = arguments.get(*slot).ok_or_else(|| {
                fail(format!(
                    "`{}` is applied to too few arguments",
                    function.name
                ))
            })?;
            converted.insert(*slot, self.convert(argument, scope)?);
        }
        for slot in &slots {
            out.push(BTerm::Template(Box::new(converted[slot].env_type.clone())));
        }
        for slot in &slots {
            out.push(BTerm::Template(Box::new(converted[slot].code.clone())));
        }
        let templates = self.template_slots(parameters);
        for slot in &templates {
            out.push(BTerm::Template(Box::new(
                self.term(&arguments[*slot], scope)?,
            )));
        }
        for index in order {
            if templates.contains(index) {
                continue;
            }
            match converted.remove(index) {
                Some(closure) => out.push(closure.env),
                None => out.push(self.term(&arguments[*index], scope)?),
            }
        }
        Ok(out)
    }

    /// Convert one function argument.
    pub(super) fn convert(
        &mut self,
        argument: &SemanticTerm,
        scope: &Scope,
    ) -> Result<Converted, Diagnostic> {
        match argument {
            SemanticTerm::Var { name } if scope.closures.contains_key(name) => {
                let closure = &scope.closures[name];
                Ok(Converted {
                    env_type: closure.env_type.clone(),
                    code: var(closure.code.clone()),
                    env: var(closure.env.clone()),
                })
            }
            SemanticTerm::FunctionRef { function, .. } => {
                let (_, parameters, _) = self.signature(function)?;
                if !self.function_slots(&parameters).is_empty() {
                    return Err(fail(format!(
                        "the higher-order function `{}` is passed as a value; Bend shares functions only as closed templates, so language 2.2 lowers no such argument",
                        function.name
                    )));
                }
                let eta = self.term(argument, scope)?;
                Ok(Converted {
                    env_type: unit_type(),
                    code: BTerm::Lam(synthetic("+ll_e"), Box::new(eta)),
                    env: unit_value(),
                })
            }
            SemanticTerm::Lambda { parameters, body, .. } => {
                let mut bound = parameters
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .collect();
                let mut free = std::collections::BTreeSet::new();
                normal::free_vars(body, &mut bound, &mut free);
                // What the lambda captures, as (Bend name, Bend type, value).
                let mut captured: Vec<(String, BTerm, BTerm)> = Vec::new();
                for name in &free {
                    if let Some(closure) = scope.closures.get(name) {
                        captured.push((
                            closure.env.clone(),
                            closure.env_type.clone(),
                            var(closure.env.clone()),
                        ));
                    } else if let Some((spelled, ty)) = scope.locals.get(name) {
                        if !self.is_data(ty) {
                            return Err(fail(format!(
                                "a lambda passed as a function argument captures `{name}`, which is not data; Bend shares only data with a closed template"
                            )));
                        }
                        captured.push((spelled.clone(), self.ty(ty)?, var(spelled.clone())));
                    }
                }
                let lambda = self.term(argument, scope)?;
                let (env_type, env) = self.tuple(&captured);
                let code = BTerm::Lam(
                    synthetic("+ll_e"),
                    Box::new(self.rebind(lambda, &captured, &var("ll_e"))?),
                );
                Ok(Converted {
                    env_type,
                    code,
                    env,
                })
            }
            _ => Err(fail(
                "a function argument that is not a lambda, a function reference, or a function parameter has no Bend lowering in language 2.2",
            )),
        }
    }

    /// The environment tuple of `captured`: its type and its value, nested
    /// to the right; `Unit` when nothing is captured.
    fn tuple(&mut self, captured: &[(String, BTerm, BTerm)]) -> (BTerm, BTerm) {
        match captured {
            [] => (unit_type(), unit_value()),
            [(_, ty, value)] => (ty.clone(), value.clone()),
            [(_, ty, value), rest @ ..] => {
                let (rest_type, rest_value) = self.tuple(rest);
                (
                    call(self.prelude("Lean.Prod"), vec![ty.clone(), rest_type]),
                    BTerm::Pair(Box::new(value.clone()), Box::new(rest_value)),
                )
            }
        }
    }

    /// `lambda` with its captured locals rebound, inside its innermost
    /// binder, from the environment `env`.
    fn rebind(
        &mut self,
        lambda: BTerm,
        captured: &[(String, BTerm, BTerm)],
        env: &BTerm,
    ) -> Result<BTerm, Diagnostic> {
        match lambda {
            BTerm::Lam(binder, body) if matches!(body.as_ref(), BTerm::Lam(..)) => Ok(BTerm::Lam(
                binder,
                Box::new(self.rebind(*body, captured, env)?),
            )),
            BTerm::Lam(binder, body) => {
                if captured.is_empty() {
                    return Ok(BTerm::Lam(binder, body));
                }
                let mut stmts = Vec::new();
                let mut rest = env.clone();
                for (index, (name, ty, _)) in captured.iter().enumerate() {
                    let value = if index + 1 == captured.len() {
                        rest.clone()
                    } else {
                        let (rest_type, _) = self.tuple(&captured[index + 1..]);
                        let head = call(
                            self.support("Sem.fst"),
                            vec![ty.clone(), rest_type.clone(), rest.clone()],
                        );
                        rest = call(self.support("Sem.snd"), vec![ty.clone(), rest_type, rest]);
                        head
                    };
                    stmts.push(Stmt::Share {
                        name: synthetic(name.clone()),
                        value,
                        source: here(),
                    });
                }
                Ok(BTerm::Lam(
                    binder,
                    Box::new(BTerm::Block(Box::new(Body {
                        stmts,
                        tail: Tail::Term(*body, here()),
                    }))),
                ))
            }
            _ => Err(fail("a converted lambda lost its binders")),
        }
    }
}
