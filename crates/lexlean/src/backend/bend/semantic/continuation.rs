//! Recursive calls under a lifted match, as continuations (SPEC.md
//! §18.11.3).
//!
//! Bend matches only a parameter or a pattern variable, so a match on a
//! computed value, or one that would break Bend's binder order, lowers to an
//! auxiliary definition (`lifted_match`). The auxiliary is defined above the
//! definition it serves, and Bend has no forward reference, so a recursive
//! call in one of its branches cannot name the recursive definition. Such a
//! call is passed in instead: the caller builds a function over the call's
//! other arguments, `+a => f(piece, a)`, around the recursive call on the
//! same piece of the decreasing argument, which Bend's termination check
//! and the kernel accept inside a lambda, and the branch applies it. Only
//! the branch the match takes applies its function, so evaluation follows
//! Lean's. A call whose decreasing argument the match's own binders reach
//! has no such form and is refused.

use std::collections::BTreeSet;

use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::BTerm;
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{MemberRef, SemanticBranch, SemanticTerm, SemanticType};

use super::{generated, normal, substitute_type, synthetic};
use super::{Lower, Scope};

/// The structurally recursive definition being lowered.
#[derive(Clone)]
pub struct Structural {
    pub name: String,
    /// Its decreasing parameter's position.
    pub recursive: usize,
}

/// A recursive call a lifted match's branches make, passed to the match's
/// auxiliary as a function its branch applies.
pub struct Hoisted {
    /// The function local's Bend spelling (see `generated`).
    name: String,
    function: MemberRef,
    type_arguments: Vec<SemanticType>,
    /// The call's arguments, the decreasing one kept and each other a
    /// parameter of the function.
    arguments: Vec<Option<SemanticTerm>>,
    /// The function's type: the callee's other parameters, or `Unit` when it
    /// has none, to its result.
    ty: SemanticType,
}

impl Hoisted {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> &SemanticType {
        &self.ty
    }
}

impl Lower<'_, '_> {
    /// The decreasing parameter's position when `function` is the recursive
    /// definition, or a member of the simultaneous group, being lowered.
    pub(super) fn recursive_position(&self, function: &MemberRef) -> Option<usize> {
        let local = function
            .module
            .as_deref()
            .is_none_or(|home| home == self.module);
        if !local {
            return None;
        }
        match &self.group {
            Some(group) => group.recursive_position(&function.name),
            None => self
                .structural
                .as_ref()
                .filter(|structural| structural.name == function.name)
                .map(|structural| structural.recursive),
        }
    }

    /// Refuse a recursive call inside a lifted match's auxiliary, which lies
    /// above the definition it would call.
    pub(super) fn refuse_lifted_call(&self, function: &MemberRef) -> Result<(), Diagnostic> {
        if self.lifted && self.recursive_position(function).is_some() {
            return Err(fail(format!(
                "a recursive call of `{}` inside a match on a computed value depends on that match's binders; the auxiliary the match lifts to cannot make it, so language 2.2 does not lower it",
                function.name
            )));
        }
        Ok(())
    }

    /// Each recursive call in a lifted match's `branches` whose decreasing
    /// argument none of their binders reaches, replaced by the application
    /// of a fresh function local to its other arguments. Returns the
    /// rewritten branches and what each function local names.
    pub(super) fn hoist_recursive_calls(
        &mut self,
        branches: &[SemanticBranch],
        scope: &Scope,
    ) -> Result<(Vec<SemanticBranch>, Vec<Hoisted>), Diagnostic> {
        if self.lifted || (self.group.is_none() && self.structural.is_none()) {
            return Ok((branches.to_vec(), Vec::new()));
        }
        let mut hoisted = Vec::new();
        let mut rewritten = Vec::new();
        for branch in branches {
            let mut bound: BTreeSet<String> = branch.binders.iter().cloned().collect();
            binders_of(&branch.body, &mut bound);
            let body = self.continue_calls(&branch.body, scope, &bound, &mut hoisted)?;
            rewritten.push(SemanticBranch {
                constructor: branch.constructor.clone(),
                binders: branch.binders.clone(),
                body,
            });
        }
        Ok((rewritten, hoisted))
    }

    fn continue_calls(
        &mut self,
        term: &SemanticTerm,
        scope: &Scope,
        bound: &BTreeSet<String>,
        hoisted: &mut Vec<Hoisted>,
    ) -> Result<SemanticTerm, Diagnostic> {
        let mut out = term.clone();
        let mut failure = None;
        normal::map_children(&mut out, &mut |child| match self
            .continue_calls(child, scope, bound, hoisted)
        {
            Ok(next) => *child = next,
            Err(error) => failure = failure.take().or(Some(error)),
        });
        if let Some(error) = failure {
            return Err(error);
        }
        let SemanticTerm::Call {
            function,
            type_arguments,
            arguments,
        } = &out
        else {
            return Ok(out);
        };
        let Some(recursive) = self.recursive_position(function) else {
            return Ok(out);
        };
        let Some(carrier) = arguments.get(recursive) else {
            return Ok(out);
        };
        let mut free = BTreeSet::new();
        normal::free_vars(carrier, &mut BTreeSet::new(), &mut free);
        if !free
            .iter()
            .all(|name| scope.locals.contains_key(name) && !bound.contains(name))
        {
            return Ok(out);
        }
        let type_arguments: Vec<SemanticType> =
            type_arguments.iter().map(|t| self.canonical(t)).collect();
        let (type_parameters, parameters, result) = self.signature(function)?;
        let map = type_parameters
            .into_iter()
            .zip(type_arguments.iter().cloned())
            .collect();
        let others: Vec<usize> = (0..arguments.len()).filter(|p| *p != recursive).collect();
        let (domain, applied) = if others.is_empty() {
            (vec![SemanticType::Unit], vec![SemanticTerm::Unit])
        } else {
            (
                others
                    .iter()
                    .map(|p| substitute_type(&parameters[*p].r#type, &map))
                    .collect(),
                others.iter().map(|p| arguments[*p].clone()).collect(),
            )
        };
        let name = self.fresh("k");
        hoisted.push(Hoisted {
            name: name.clone(),
            function: function.clone(),
            type_arguments,
            arguments: (0..arguments.len())
                .map(|p| (p == recursive).then(|| carrier.clone()))
                .collect(),
            ty: SemanticType::Function {
                parameters: domain,
                result: Box::new(substitute_type(&result, &map)),
            },
        });
        Ok(SemanticTerm::Apply {
            function: Box::new(SemanticTerm::Var {
                name: generated(&name),
            }),
            arguments: applied,
        })
    }

    /// The Bend function a hoisted call is passed as, in the caller's scope:
    /// a lambda over the callee's other arguments making the call.
    pub(super) fn hoisted_argument(
        &mut self,
        hoisted: &Hoisted,
        scope: &Scope,
    ) -> Result<BTerm, Diagnostic> {
        let SemanticType::Function { parameters, .. } = &hoisted.ty else {
            return Err(fail("a continuation is not a function"));
        };
        let mut inner = scope.clone();
        let mut lambdas = Vec::new();
        let mut domain = parameters.iter();
        let mut arguments = Vec::new();
        for argument in &hoisted.arguments {
            if let Some(carrier) = argument {
                arguments.push(carrier.clone());
                continue;
            }
            let ty = domain
                .next()
                .ok_or_else(|| fail("a continuation misses a parameter type"))?
                .clone();
            let spelled = self.fresh("a");
            inner = inner.with_generated(&spelled, ty.clone());
            arguments.push(SemanticTerm::Var {
                name: generated(&spelled),
            });
            lambdas.push(if self.is_data(&ty) {
                format!("+{spelled}")
            } else {
                spelled
            });
        }
        if lambdas.is_empty() {
            lambdas.push("+ll_unit".to_owned());
        }
        let call = SemanticTerm::Call {
            function: hoisted.function.clone(),
            type_arguments: hoisted.type_arguments.clone(),
            arguments,
        };
        let mut body = self.term(&call, &inner)?;
        for name in lambdas.into_iter().rev() {
            body = BTerm::Lam(synthetic(name), Box::new(body));
        }
        Ok(body)
    }
}

/// Every name a binder inside `term` introduces.
fn binders_of(term: &SemanticTerm, out: &mut BTreeSet<String>) {
    match term {
        SemanticTerm::Match { branches, .. } => {
            for branch in branches {
                out.extend(branch.binders.iter().cloned());
            }
        }
        SemanticTerm::Let { binder, .. } | SemanticTerm::Forall { binder, .. } => {
            out.insert(binder.name.clone());
        }
        SemanticTerm::Lambda { parameters, .. } => {
            out.extend(parameters.iter().map(|parameter| parameter.name.clone()));
        }
        _ => {}
    }
    normal::for_each_child(term, &mut |child| binders_of(child, out));
}
