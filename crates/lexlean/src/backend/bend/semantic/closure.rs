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
use crate::backend::bend::syntax::{BTerm, Body, Item, Param, Quantity, Stmt, Tail};
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

impl Closure {
    /// The name of the environment's template type, which the parameter
    /// binds.
    pub fn env_type_name(&self) -> Result<String, Diagnostic> {
        match &self.env_type {
            BTerm::Name(name) => Ok(name.text.clone()),
            _ => Err(fail(
                "a converted parameter's environment type is not a name",
            )),
        }
    }
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

/// A code definition as a template argument: its name, applied to the
/// templates it takes, if any.
fn applied(name: String, arguments: Vec<BTerm>) -> BTerm {
    if arguments.is_empty() {
        var(name)
    } else {
        BTerm::Call(synthetic(name), arguments)
    }
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
            SemanticTerm::FunctionRef {
                function,
                type_arguments,
            } => {
                let (type_parameters, parameters, result) = self.signature(function)?;
                if !self.function_slots(&parameters).is_empty() {
                    return Err(fail(format!(
                        "the higher-order function `{}` is passed as a value; Bend shares functions only as closed templates, so language 2.2 lowers no such argument",
                        function.name
                    )));
                }
                let name = self.function_code(function, &type_parameters, &parameters, &result)?;
                let mut arguments = Vec::new();
                for argument in type_arguments {
                    let canonical = self.canonical(argument);
                    arguments.push(BTerm::Template(Box::new(self.ty(&canonical)?)));
                }
                Ok(Converted {
                    env_type: unit_type(),
                    code: applied(name, arguments),
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
                // What the lambda captures, as (Bend name, Bend type, value),
                // and the converted function parameters among them.
                let mut captured: Vec<(String, BTerm, BTerm)> = Vec::new();
                let mut closures: Vec<(Closure, SemanticType)> = Vec::new();
                for name in &free {
                    if let Some(closure) = scope.closures.get(name) {
                        captured.push((
                            closure.env.clone(),
                            closure.env_type.clone(),
                            var(closure.env.clone()),
                        ));
                        if let Some((_, ty)) = scope.locals.get(name) {
                            closures.push((closure.clone(), ty.clone()));
                        }
                    } else if let Some((spelled, ty)) = scope.locals.get(name) {
                        if !self.is_data(ty) {
                            return Err(fail(format!(
                                "a lambda passed as a function argument captures `{name}`, which is not data; Bend shares only data with a closed template"
                            )));
                        }
                        captured.push((spelled.clone(), self.ty(ty)?, var(spelled.clone())));
                    }
                }
                let (env_type, env) = self.tuple(&captured);
                // A lambda that makes a recursive call stays in the
                // definition it recurses in: a code definition would lie
                // above it, and Bend has no forward reference.
                if self.calls_recursively(body) {
                    let lambda = self.term(argument, scope)?;
                    let code = BTerm::Lam(
                        synthetic("+ll_e"),
                        Box::new(self.rebind(lambda, &captured, &var("ll_e"))?),
                    );
                    return Ok(Converted {
                        env_type,
                        code,
                        env,
                    });
                }
                let code = self.lambda_code(parameters, body, &captured, &closures, &env_type, scope)?;
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

    /// The code definition a function reference passed as an argument
    /// lowers to: its eta-expansion over the empty environment, generic in
    /// the function's own type parameters, declared once per module. A
    /// template argument is a named definition rather than a lambda, since
    /// Bend's kernel types a template's type only through named heads, and
    /// a generated theorem names the same code the definition used.
    fn function_code(
        &mut self,
        function: &MemberRef,
        type_parameters: &[String],
        parameters: &[SemanticParameter],
        result: &SemanticType,
    ) -> Result<String, Diagnostic> {
        let home = self.home(function);
        let key = format!("{home}::{}", function.name);
        if let Some(name) = self.codes.get(&key) {
            return Ok(name.clone());
        }
        let name = if home == self.module {
            format!("{}.ll_code", super::names::global(&function.name)?)
        } else {
            self.fresh("code")
        };
        let saved = std::mem::replace(
            &mut self.type_parameters,
            type_parameters.iter().cloned().collect(),
        );
        let built = self.function_code_item(&name, function, type_parameters, parameters, result);
        self.type_parameters = saved;
        self.aux.push(built?);
        self.codes.insert(key, name.clone());
        Ok(name)
    }

    fn function_code_item(
        &mut self,
        name: &str,
        function: &MemberRef,
        type_parameters: &[String],
        parameters: &[SemanticParameter],
        result: &SemanticType,
    ) -> Result<Item, Diagnostic> {
        let mut params = Vec::new();
        for type_parameter in type_parameters {
            params.push(Param {
                quantity: Quantity::Template,
                name: synthetic(super::names::local(type_parameter)?),
                ty: BTerm::Kind("Data"),
                source: here(),
            });
        }
        params.push(Param {
            quantity: Quantity::Reusable,
            name: synthetic("ll_e"),
            ty: unit_type(),
            source: here(),
        });
        let mut values = Vec::new();
        for (index, parameter) in parameters.iter().enumerate() {
            let spelled = format!("ll_x{index}");
            let ty = self.canonical(&parameter.r#type);
            params.push(self.param(&spelled, &ty)?);
            values.push(var(spelled));
        }
        let type_arguments: Vec<SemanticType> = type_parameters
            .iter()
            .map(|name| SemanticType::Parameter { name: name.clone() })
            .collect();
        let body = self.call_of(function, &type_arguments, values)?;
        let result = self.canonical(result);
        Ok(Item::Def {
            name: synthetic(name),
            params,
            result: self.ty(&result)?,
            result_source: here(),
            body: Body::term(body, here()),
            source: here(),
        })
    }

    /// The code definition a lambda passed as an argument lowers to: its
    /// parameters after the environment, with the captured locals rebound
    /// from the environment, generic in the type parameters in scope and in
    /// the code and environment type of each converted parameter it
    /// captures. Returns the template argument naming it.
    fn lambda_code(
        &mut self,
        parameters: &[SemanticParameter],
        body: &SemanticTerm,
        captured: &[(String, BTerm, BTerm)],
        closures: &[(Closure, SemanticType)],
        env_type: &BTerm,
        scope: &Scope,
    ) -> Result<BTerm, Diagnostic> {
        let mut params = Vec::new();
        let mut arguments = Vec::new();
        for type_parameter in self.type_parameters.clone() {
            let spelled = super::names::local(&type_parameter)?;
            params.push(Param {
                quantity: Quantity::Template,
                name: synthetic(spelled.clone()),
                ty: BTerm::Kind("Data"),
                source: here(),
            });
            arguments.push(BTerm::Template(Box::new(var(spelled))));
        }
        let mut codes = Vec::new();
        let mut code_arguments = Vec::new();
        for (closure, ty) in closures {
            let SemanticType::Function {
                parameters: domain,
                result,
            } = ty
            else {
                return Err(fail("a converted function parameter lost its type"));
            };
            let function = self.function_type(domain, result)?;
            params.push(Param {
                quantity: Quantity::Template,
                name: synthetic(closure.env_type_name()?),
                ty: BTerm::Kind("Data"),
                source: here(),
            });
            arguments.push(BTerm::Template(Box::new(closure.env_type.clone())));
            codes.push(Param {
                quantity: Quantity::Template,
                name: synthetic(closure.code.clone()),
                ty: BTerm::Pi {
                    name: Some(synthetic("+ll_e")),
                    erased: false,
                    domain: Box::new(closure.env_type.clone()),
                    codomain: Box::new(function),
                },
                source: here(),
            });
            code_arguments.push(BTerm::Template(Box::new(var(closure.code.clone()))));
        }
        params.append(&mut codes);
        arguments.append(&mut code_arguments);
        params.push(Param {
            quantity: Quantity::Reusable,
            name: synthetic("ll_e"),
            ty: env_type.clone(),
            source: here(),
        });
        let mut inner = scope.clone();
        for parameter in parameters {
            let ty = self.canonical(&parameter.r#type);
            inner = inner.with(&parameter.name, ty.clone())?;
            let spelled = inner.get(&parameter.name)?.0.clone();
            params.push(self.param(&spelled, &ty)?);
        }
        let result = self.infer(body, &inner)?;
        let result = self.ty(&result)?;
        let tail = self.term(body, &inner)?;
        let stmts = self.rebinding(captured, &var("ll_e"));
        let body = Body {
            stmts,
            tail: Tail::Term(tail, here()),
        };
        // Equal lambdas share one code definition, so a theorem about a fold
        // names the step its definition folds with, wherever it was spelled.
        let key = format!("{params:?}{result:?}{body:?}");
        if let Some(name) = self.codes.get(&key) {
            return Ok(applied(name.clone(), arguments));
        }
        let name = self.fresh("code");
        self.codes.insert(key, name.clone());
        self.aux.push(Item::Def {
            name: synthetic(name.clone()),
            params,
            result,
            result_source: here(),
            body,
            source: here(),
        });
        Ok(applied(name, arguments))
    }

    /// Whether `term` calls the recursive definition, or a member of the
    /// simultaneous group, being lowered.
    fn calls_recursively(&self, term: &SemanticTerm) -> bool {
        if let SemanticTerm::Call { function, .. } | SemanticTerm::FunctionRef { function, .. } =
            term
        {
            let local = function
                .module
                .as_deref()
                .is_none_or(|home| home == self.module);
            let wellfounded = self
                .recursion
                .as_ref()
                .is_some_and(|recursion| local && recursion.name() == function.name);
            if self.recursive_position(function).is_some() || wellfounded {
                return true;
            }
        }
        let mut found = false;
        normal::for_each_child(term, &mut |child| {
            found = found || self.calls_recursively(child);
        });
        found
    }

    /// The statements rebinding each captured local from the environment
    /// `env`, the tuple `tuple` builds.
    fn rebinding(&mut self, captured: &[(String, BTerm, BTerm)], env: &BTerm) -> Vec<Stmt> {
        let mut stmts = Vec::new();
        let mut rest = env.clone();
        for (index, (name, ty, _)) in captured.iter().enumerate() {
            let value = if index + 1 == captured.len() {
                rest.clone()
            } else {
                let (rest_type, _) = self.tuple(&captured[index + 1..]);
                let head = call(
                    self.support("fst"),
                    vec![ty.clone(), rest_type.clone(), rest.clone()],
                );
                rest = call(self.support("snd"), vec![ty.clone(), rest_type, rest]);
                head
            };
            stmts.push(Stmt::Share {
                name: synthetic(name.clone()),
                value,
                source: here(),
            });
        }
        stmts
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
                let stmts = self.rebinding(captured, env);
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
