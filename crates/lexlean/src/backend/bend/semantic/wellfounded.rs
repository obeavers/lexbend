//! Well-founded definitions as proof-carrying fuel.
//!
//! Bend admits only structural recursion, so a definition with a measure
//! and termination evidence (§17.12) is lowered to a helper `f.ll_go` that
//! recurses on a `Nat` fuel and carries a proof that the measure is below
//! it. `f` calls the helper with fuel `measure + 1` and the proof
//! `measure < measure + 1`. At each recursive call the declared evidence
//! proves the measure of the call's arguments below the caller's, so the
//! carried proof is re-established for the smaller fuel, and at fuel zero
//! the carried proof is absurd. Nothing is assumed: Bend checks that every
//! call shrinks the fuel and that every carried proof holds, so a wrong
//! measure or a missing evidence fails to check rather than being believed.
//!
//! The evidence's hypotheses are the conditions of the `if`s and the
//! equations of the `match`es enclosing the call. An `if` enclosing a call
//! is lowered through `Sem.iteDep`, which hands each arm its condition's
//! equation; a `match` enclosing a call matches on its local, after which
//! Bend sees the scrutinee as the constructor and the equation holds by
//! reflexivity.

use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Item, Param, Pattern, Quantity, Tail};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{
    MemberRef, PlannedNode, SemanticDeclaration, SemanticParameter, SemanticTerm, SemanticType,
    Step,
};

use super::{call, here, normal, synthetic, var, Lower, Scope};

/// An enclosing node of a recursive call, as both the plan and the lowering
/// identify it: the `if` condition and arm, or the `match` scrutinee and
/// branch constructor.
#[derive(Clone, PartialEq)]
enum Key {
    If(SemanticTerm, bool),
    Match(SemanticTerm, String),
}

/// One planned recursive call and the evidence that it decreases.
struct Site {
    keys: Vec<Key>,
    binders: Vec<String>,
    arguments: Vec<SemanticTerm>,
    evidence: MemberRef,
}

/// The well-founded definition whose body is being lowered.
pub(super) struct Recursion {
    name: String,
    go: String,
    measure: SemanticTerm,
    parameters: Vec<SemanticParameter>,
    type_parameters: Vec<String>,
    sites: Vec<Site>,
    /// The nodes enclosing the term being lowered, each with the Bend proof
    /// of its hypothesis.
    path: Vec<(Key, BTerm)>,
    /// The fuel one below the caller's.
    pred: String,
    /// The carried proof `measure < fuel`.
    bound: String,
}

/// Whether `term` calls the definition `name` of `module`.
fn calls(term: &SemanticTerm, name: &str, module: &str) -> bool {
    if let SemanticTerm::Call { function, .. } | SemanticTerm::FunctionRef { function, .. } = term {
        if function.name == name && function.module.as_deref().is_none_or(|home| home == module) {
            return true;
        }
    }
    let mut found = false;
    normal::for_each_child(term, &mut |child| found |= calls(child, name, module));
    found
}

/// Whether every recursive call in `term` lies outside any `if`, `match`,
/// `let`, or binder of `term`: such a call shares the path of `term`.
fn plain(term: &SemanticTerm, name: &str, module: &str) -> bool {
    let nested = matches!(
        term,
        SemanticTerm::If { .. }
            | SemanticTerm::Match { .. }
            | SemanticTerm::Let { .. }
            | SemanticTerm::Lambda { .. }
            | SemanticTerm::Forall { .. }
    );
    if nested && calls(term, name, module) {
        return false;
    }
    let mut ok = true;
    normal::for_each_child(term, &mut |child| ok &= plain(child, name, module));
    ok
}

impl Lower<'_, '_> {
    /// A well-founded definition: its fuelled helper, then itself.
    ///
    /// # Errors
    ///
    /// `LLB6008` when a recursive call sits where its decrease proof cannot
    /// be carried: under a binder, inside a `match` on a compound term, or
    /// in a mutual group.
    pub(super) fn well_founded(
        &mut self,
        declaration: &SemanticDeclaration,
    ) -> Result<Vec<Item>, Diagnostic> {
        let SemanticDeclaration::Definition {
            name,
            type_parameters,
            parameters,
            result,
            body,
            termination: Some(termination),
            mutual,
            ..
        } = declaration
        else {
            return Err(fail("not a well-founded definition"));
        };
        if mutual.is_some() {
            return Err(fail(format!(
                "the well-founded definition `{name}` belongs to a mutual group; Bend admits only self-recursion, so language 2.2 lowers no well-founded group"
            )));
        }
        if self.converts(parameters) {
            return Err(fail(format!(
                "the well-founded definition `{name}` takes a function, whose decrease proof Bend cannot carry"
            )));
        }
        let result_type = self.canonical(result);
        if result_type == SemanticType::Prop {
            return Err(fail(format!(
                "the well-founded definition `{name}` is a proposition, which Bend cannot define by fuel"
            )));
        }
        let group = std::iter::once(name.clone()).collect();
        let plan = crate::ir::semantic::well_founded_plan(name, &group, type_parameters, parameters, body)
            .map_err(|reason| fail(format!("the well-founded definition `{name}` has no plan: {reason}")))?;
        if plan.sites.len() != termination.evidence.len() {
            return Err(fail(format!(
                "the well-founded definition `{name}` has {} recursive calls and {} evidence theorems",
                plan.sites.len(),
                termination.evidence.len()
            )));
        }
        let key = |step: &Step| match (step, &plan.nodes[step.node()]) {
            (Step::If { polarity, .. }, PlannedNode::If { condition }) => {
                Ok(Key::If((*condition).clone(), *polarity))
            }
            (Step::Match { branch, .. }, PlannedNode::Match { scrutinee, branches }) => Ok(
                Key::Match((*scrutinee).clone(), branches[*branch].constructor.name.clone()),
            ),
            _ => Err(fail("a planned step names the wrong kind of node")),
        };
        let mut sites = Vec::new();
        for (site, evidence) in plan.sites.iter().zip(&termination.evidence) {
            sites.push(Site {
                keys: site.path.iter().map(key).collect::<Result<_, _>>()?,
                binders: plan.binders(site),
                arguments: site.arguments.clone(),
                evidence: evidence.clone(),
            });
        }
        let spelled = super::names::global(name)?;
        let go = format!("{spelled}.ll_go");
        let fuel = self.fresh("fuel");
        let pred = self.fresh("fuel");
        let bound = self.fresh("bound");

        let mut params = self.type_params(type_parameters)?;
        let templates: Vec<BTerm> = params
            .iter()
            .map(|param| BTerm::Template(Box::new(BTerm::Name(param.name.clone()))))
            .collect();
        let order: Vec<usize> = (0..parameters.len()).collect();
        let (values, scope) = self.value_params(parameters, &order)?;
        let result_bend = self.ty(&result_type)?;
        let measure = self.term(&termination.measure, &scope)?;
        let lt = self.support("lt");

        // The helper: fuel first, so Bend sees it shrink; the carried proof
        // last.
        let mut go_params = params.clone();
        go_params.push(Param {
            quantity: Quantity::Reusable,
            name: synthetic(fuel.clone()),
            ty: var("Nat"),
            source: here(),
        });
        go_params.extend(values.iter().cloned());
        go_params.push(Param {
            quantity: Quantity::Reusable,
            name: synthetic(bound.clone()),
            ty: call(lt, vec![measure.clone(), var(fuel.clone())]),
            source: here(),
        });
        self.recursion = Some(Recursion {
            name: name.clone(),
            go: go.clone(),
            measure: termination.measure.clone(),
            parameters: parameters.clone(),
            type_parameters: type_parameters.clone(),
            sites,
            path: Vec::new(),
            pred: pred.clone(),
            bound: bound.clone(),
        });
        let lowered = self.recursive_body(body, &scope);
        self.recursion = None;
        let lowered = lowered?;
        let absurd = self.support("lt_zero");
        let go_body = Body {
            stmts: Vec::new(),
            tail: Tail::Match {
                scrutinee: synthetic(fuel),
                cases: vec![
                    (
                        Pattern::Zero,
                        Body::term(
                            call(absurd, vec![result_bend.clone(), measure.clone(), var(bound)]),
                            here(),
                        ),
                    ),
                    (Pattern::Succ(synthetic(pred)), lowered),
                ],
                source: here(),
            },
        };
        let helper = Item::Def {
            name: synthetic(go.clone()),
            params: go_params,
            result: result_bend.clone(),
            result_source: here(),
            body: go_body,
            source: here(),
        };

        // The definition itself: the helper at fuel `measure + 1`.
        let mut arguments = templates;
        arguments.push(BTerm::Succ(Box::new(measure.clone())));
        for parameter in parameters {
            arguments.push(var(scope.get(&parameter.name)?.0.clone()));
        }
        let start = self.support("lt_succ");
        arguments.push(call(start, vec![measure]));
        params.extend(values);
        let wrapper = Item::Def {
            name: synthetic(spelled),
            params,
            result: result_bend,
            result_source: here(),
            body: Body::term(call(go, arguments), here()),
            source: here(),
        };
        Ok(vec![helper, wrapper])
    }

    /// The helper's body below its fuel match.
    fn recursive_body(&mut self, term: &SemanticTerm, scope: &Scope) -> Result<Body, Diagnostic> {
        let (name, module) = match &self.recursion {
            Some(recursion) => (recursion.name.clone(), self.module.clone()),
            None => return Err(fail("a recursive body outside a well-founded definition")),
        };
        if !calls(term, &name, &module) {
            return self.tail_body(term, scope);
        }
        match term {
            SemanticTerm::If {
                condition,
                then_value,
                else_value,
            } if plain(condition, &name, &module) => {
                let ty = self.infer(term, scope)?;
                let ty = self.ty(&ty)?;
                let lowered = self.term(condition, scope)?;
                let mut arms = Vec::new();
                for (polarity, arm) in [(true, then_value), (false, else_value)] {
                    let hypothesis = self.fresh("w");
                    self.enter(Key::If((**condition).clone(), polarity), var(hypothesis.clone()));
                    let body = self.recursive_body(arm, scope);
                    self.leave();
                    arms.push(BTerm::Lam(
                        synthetic(format!("+{hypothesis}")),
                        Box::new(BTerm::Block(Box::new(body?))),
                    ));
                }
                let otherwise = arms.pop().ok_or_else(|| fail("an if has no else arm"))?;
                let then = arms.pop().ok_or_else(|| fail("an if has no then arm"))?;
                let head = self.support("iteDep");
                Ok(Body::term(call(head, vec![ty, lowered, then, otherwise]), here()))
            }
            SemanticTerm::Match {
                scrutinee,
                branches,
            } if scope.matchable(scrutinee) => {
                let SemanticTerm::Var { name: local } = scrutinee.as_ref() else {
                    return Err(fail("a matchable scrutinee is not a local"));
                };
                let (spelled, ty) = scope.get(local)?.clone();
                let mut cases = Vec::new();
                for branch in branches {
                    let pattern = self.pattern(&ty, &branch.constructor, &branch.binders)?;
                    let inner = self.branch_scope(&ty, branch, scope)?;
                    self.enter(
                        Key::Match((**scrutinee).clone(), branch.constructor.name.clone()),
                        BTerm::Refl,
                    );
                    let body = self.recursive_body(&branch.body, &inner);
                    self.leave();
                    cases.push((pattern, body?));
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
            SemanticTerm::Match { .. } => Err(fail(format!(
                "a match enclosing a recursive call of `{name}` inspects a compound term, which Bend cannot match on"
            ))),
            SemanticTerm::Let {
                binder,
                value,
                body,
            } if plain(value, &name, &module) => {
                let ty = self.canonical(&binder.r#type);
                let inner = scope.with_let(&binder.name, ty.clone())?;
                let bound = synthetic(inner.get(&binder.name)?.0.clone());
                let value = self.term(value, scope)?;
                let stmt = if self.is_data(&ty) {
                    crate::backend::bend::syntax::Stmt::Share {
                        name: bound,
                        value,
                        source: here(),
                    }
                } else {
                    crate::backend::bend::syntax::Stmt::Let {
                        name: bound,
                        value,
                        source: here(),
                    }
                };
                let mut rest = self.recursive_body(body, &inner)?;
                rest.stmts.insert(0, stmt);
                Ok(rest)
            }
            _ if plain(term, &name, &module) => Ok(Body::term(self.term(term, scope)?, here())),
            _ => Err(fail(format!(
                "a recursive call of `{name}` lies under a binder or a nested conditional, where Bend cannot carry its decrease proof"
            ))),
        }
    }

    fn enter(&mut self, key: Key, proof: BTerm) {
        if let Some(recursion) = &mut self.recursion {
            recursion.path.push((key, proof));
        }
    }

    fn leave(&mut self) {
        if let Some(recursion) = &mut self.recursion {
            recursion.path.pop();
        }
    }

    /// A recursive call of the well-founded definition being lowered, as a
    /// call of its helper at the smaller fuel with the re-established
    /// bound; `None` for any other call.
    pub(super) fn recursive_call(
        &mut self,
        function: &MemberRef,
        arguments: &[SemanticTerm],
        scope: &Scope,
    ) -> Result<Option<BTerm>, Diagnostic> {
        let Some(recursion) = &self.recursion else {
            return Ok(None);
        };
        let local = function.module.as_deref().is_none_or(|home| home == self.module);
        if !local || function.name != recursion.name {
            return Ok(None);
        }
        let keys: Vec<Key> = recursion.path.iter().map(|(key, _)| key.clone()).collect();
        let Some(site) = recursion
            .sites
            .iter()
            .find(|site| site.keys == keys && site.arguments == arguments)
        else {
            return Err(fail(format!(
                "a recursive call of `{}` lies where its planned decrease proof does not reach",
                recursion.name
            )));
        };
        let evidence = site.evidence.clone();
        let binders = site.binders.clone();
        let hypotheses: Vec<BTerm> = recursion.path.iter().map(|(_, proof)| proof.clone()).collect();
        let parameters = recursion.parameters.clone();
        let type_arguments: Vec<SemanticType> = recursion
            .type_parameters
            .iter()
            .map(|name| SemanticType::Parameter { name: name.clone() })
            .collect();
        let measure = recursion.measure.clone();
        let go = recursion.go.clone();
        let pred = recursion.pred.clone();
        let bound = recursion.bound.clone();

        let mut evidence_arguments = Vec::new();
        for parameter in &parameters {
            evidence_arguments.push(var(scope.get(&parameter.name)?.0.clone()));
        }
        for binder in &binders {
            evidence_arguments.push(var(scope.get(binder)?.0.clone()));
        }
        evidence_arguments.extend(hypotheses);
        let decreases = self.call_of(&evidence, &type_arguments, evidence_arguments)?;
        let substitution = parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .zip(arguments.iter().cloned())
            .collect();
        let smaller = self.term(&normal::substitute_all(&measure, &substitution), scope)?;
        let current = self.term(&measure, scope)?;
        let step = self.support("lt_fuel");
        let proof = call(step, vec![smaller, current, var(pred.clone()), decreases, var(bound)]);

        let mut out: Vec<BTerm> = Vec::new();
        for ty in &type_arguments {
            out.push(BTerm::Template(Box::new(self.ty(ty)?)));
        }
        out.push(var(pred));
        out.extend(self.arguments(arguments, scope)?);
        out.push(proof);
        Ok(Some(call(go, out)))
    }
}
