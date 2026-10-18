//! Proof terms: citations, hypotheses, and the lemmas of `Reasoning.bend`
//! and the runtime they name.
//!
//! A Lean lemma that takes a step, a predicate, and a hypothesis as values
//! is a generic law here that takes them as templates. Its predicate and
//! hypothesis become definitions below the theorem: the predicate over the
//! theorem's parameters as one environment `k`, and the hypothesis proved
//! by applying the Lean hypothesis term to the law's own binders, so the
//! Lean proof term is reused as it stands.

use std::collections::BTreeMap;

use super::engine::{plain, subst, Engine, State};
use super::{environment, formula_type, one, Context};
use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Item, Param, Quantity, Stmt, Tail};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::reasoning::{Formula, Lemma, ProofTerm};
use crate::ir::semantic::{MemberRef, SemanticTerm, SemanticType};

use super::super::{call, here, synthetic, var};

/// The Bend proofs the enclosing proof terms' hypotheses name, with their
/// types when known.
pub(super) type Hyps = BTreeMap<String, BTerm>;

/// A fold or loop step: its code definition as a template argument, its
/// environment and that environment's type, and its semantic signature.
pub(super) struct StepFn {
    pub code: BTerm,
    pub env_type: BTerm,
    pub env: BTerm,
    pub parameters: Vec<SemanticType>,
    pub result: SemanticType,
}

impl StepFn {
    /// The code applied to the environment `env` and `args`.
    pub(super) fn at(&self, env: BTerm, args: Vec<BTerm>) -> BTerm {
        let mut all = vec![env];
        all.extend(args);
        apply_code(&self.code, all)
    }
}

/// A code or definition head, given as a template argument, applied.
pub(super) fn apply_code(code: &BTerm, args: Vec<BTerm>) -> BTerm {
    match code {
        BTerm::Call(head, prefix) => {
            let mut all = prefix.clone();
            all.extend(args);
            BTerm::Call(head.clone(), all)
        }
        BTerm::Name(head) => BTerm::Call(head.clone(), args),
        other => BTerm::Apply(Box::new(other.clone()), args),
    }
}

pub(super) fn template(term: BTerm) -> BTerm {
    BTerm::Template(Box::new(term))
}

fn unit() -> BTerm {
    BTerm::Constructor(synthetic("Unit"), Vec::new())
}

/// A function-valued semantic term applied to arguments.
pub(super) fn apply_semantic(
    function: &SemanticTerm,
    arguments: Vec<SemanticTerm>,
) -> SemanticTerm {
    match function {
        SemanticTerm::FunctionRef {
            function,
            type_arguments,
        } => SemanticTerm::Call {
            function: function.clone(),
            type_arguments: type_arguments.clone(),
            arguments,
        },
        SemanticTerm::Lambda {
            parameters, body, ..
        } if parameters.len() == arguments.len() => {
            let map: BTreeMap<String, SemanticTerm> = parameters
                .iter()
                .map(|parameter| parameter.name.clone())
                .zip(arguments)
                .collect();
            super::super::normal::substitute_all(body, &map)
        }
        other => SemanticTerm::Apply {
            function: Box::new(other.clone()),
            arguments,
        },
    }
}

fn given(term: &ProofTerm) -> Result<&SemanticTerm, Diagnostic> {
    match term {
        ProofTerm::Term { term } => Ok(term),
        other => Err(fail(format!("a lemma expected a term, not {other:?}"))),
    }
}

/// The arguments of `expected`, a datatype or call headed `head`.
fn arguments_of<'t>(expected: Option<&'t BTerm>, head: &str) -> Result<&'t [BTerm], Diagnostic> {
    match expected {
        Some(BTerm::Datatype(name, _, args) | BTerm::Call(name, args)) if name.text == head => {
            Ok(args)
        }
        other => Err(fail(format!(
            "a lemma's expected type is not `{head}`: {other:?}"
        ))),
    }
}

impl Engine<'_, '_, '_> {
    /// The Bend proof a proof term denotes; `expected` is its type when the
    /// caller knows it, which a lemma whose Lean arguments are inferred
    /// reads them from.
    pub(super) fn proof(
        &mut self,
        context: &Context<'_>,
        term: &ProofTerm,
        hyps: &Hyps,
        expected: Option<&BTerm>,
    ) -> Result<BTerm, Diagnostic> {
        match term {
            ProofTerm::Term { term } => Ok(plain(&self.lower.term(term, &context.scope)?)),
            ProofTerm::Both { left, right } => {
                let parts = match expected.and_then(super::engine::conjuncts) {
                    Some((left, right)) => (Some(left), Some(right)),
                    None => (None, None),
                };
                Ok(BTerm::Pair(
                    Box::new(self.proof(context, left, hyps, parts.0.as_ref())?),
                    Box::new(self.proof(context, right, hyps, parts.1.as_ref())?),
                ))
            }
            ProofTerm::Refl => Ok(BTerm::Refl),
            ProofTerm::Trivial => Ok(unit()),
            ProofTerm::Infer => Err(fail("a proof term left an argument to inference")),
            ProofTerm::Predicate { .. } => {
                Err(fail("a predicate stands where a proof is expected"))
            }
            other => self.apply(context, other, Vec::new(), hyps, expected),
        }
    }

    /// The proof term applied to `args`.
    pub(super) fn apply(
        &mut self,
        context: &Context<'_>,
        term: &ProofTerm,
        args: Vec<BTerm>,
        hyps: &Hyps,
        expected: Option<&BTerm>,
    ) -> Result<BTerm, Diagnostic> {
        match term {
            ProofTerm::Theorem {
                theorem,
                type_arguments,
                arguments,
            } => {
                let mut lowered = Vec::new();
                for argument in arguments {
                    lowered.push(self.proof(context, argument, hyps, None)?);
                }
                lowered.extend(args);
                self.cite(theorem, type_arguments, lowered)
            }
            ProofTerm::Assume { binders, body } => {
                let mut inner = hyps.clone();
                let bound = binders.len().min(args.len());
                for (binder, arg) in binders.iter().zip(&args) {
                    inner.insert(binder.clone(), arg.clone());
                }
                if binders.len() > args.len() {
                    // The lambda's binders read their marks and types off the
                    // function type it is checked against: a value binder is
                    // reusable, as Bend binds a `Data` domain.
                    let mut current = expected.cloned();
                    let mut fresh = Vec::new();
                    for binder in &binders[bound..] {
                        let name = self.fresh("h");
                        inner.insert(binder.clone(), var(name.clone()));
                        let mut mark = String::new();
                        current = match current {
                            Some(BTerm::Pi {
                                name: binder_name,
                                domain,
                                codomain,
                                ..
                            }) => {
                                self.hyp_types.insert(name.clone(), (*domain).clone());
                                match binder_name {
                                    Some(bound_name) => {
                                        mark.push('+');
                                        Some(subst(
                                            &codomain,
                                            &one(
                                                &super::engine::bound(&bound_name.text),
                                                var(name.clone()),
                                            ),
                                        ))
                                    }
                                    None => Some(*codomain),
                                }
                            }
                            _ => None,
                        };
                        fresh.push(format!("{mark}{name}"));
                    }
                    let mut out = self.proof(context, body, &inner, current.as_ref())?;
                    for name in fresh.into_iter().rev() {
                        out = BTerm::Lam(synthetic(name), Box::new(out));
                    }
                    return Ok(out);
                }
                let rest = args[bound..].to_vec();
                if rest.is_empty() {
                    self.proof(context, body, &inner, expected)
                } else {
                    self.apply(context, body, rest, &inner, expected)
                }
            }
            ProofTerm::Lemma { lemma, arguments } => {
                self.lemma(context, *lemma, arguments, hyps, expected, args)
            }
            ProofTerm::Hypothesis { name } => {
                let bound = hyps
                    .get(name)
                    .cloned()
                    .ok_or_else(|| fail(format!("the hypothesis `{name}` is not bound")))?;
                if args.is_empty() {
                    return Ok(bound);
                }
                Ok(match bound {
                    BTerm::Name(head) => BTerm::Call(head, args),
                    other => BTerm::Apply(Box::new(other), args),
                })
            }
            other if args.is_empty() => self.proof(context, other, hyps, expected),
            other => Err(fail(format!(
                "a proof term is applied but is not a function: {other:?}"
            ))),
        }
    }

    /// A function of `arity` hypotheses applying `term` to them.
    pub(super) fn eta(
        &mut self,
        context: &Context<'_>,
        term: &ProofTerm,
        arity: usize,
        hyps: &Hyps,
    ) -> Result<BTerm, Diagnostic> {
        let names: Vec<String> = (0..arity).map(|_| self.fresh("h")).collect();
        let mut out = self.apply(
            context,
            term,
            names.iter().map(|name| var(name.clone())).collect(),
            hyps,
            None,
        )?;
        for name in names.into_iter().rev() {
            out = BTerm::Lam(synthetic(name), Box::new(out));
        }
        Ok(out)
    }

    /// A call of a law: its type arguments as templates, then `args`.
    pub(super) fn cite(
        &mut self,
        theorem: &MemberRef,
        type_arguments: &[SemanticType],
        args: Vec<BTerm>,
    ) -> Result<BTerm, Diagnostic> {
        let home = self.lower.home(theorem);
        let head = self.lower.spell(&home, &theorem.name)?;
        let mut all = Vec::new();
        for argument in type_arguments {
            let canonical = self.lower.canonical(argument);
            all.push(template(plain(&self.lower.ty(&canonical)?)));
        }
        all.extend(args);
        Ok(self.applied_law(&head, all))
    }

    /// A step term's code, environment, and signature.
    pub(super) fn step_of(
        &mut self,
        context: &Context<'_>,
        term: &ProofTerm,
    ) -> Result<StepFn, Diagnostic> {
        let term = given(term)?;
        let converted = self.lower.convert(term, &context.scope)?;
        let ty = self.lower.infer(term, &context.scope)?;
        let SemanticType::Function { parameters, result } = self.lower.canonical(&ty) else {
            return Err(fail("a step is not a function"));
        };
        Ok(StepFn {
            code: plain(&converted.code),
            env_type: plain(&converted.env_type),
            env: plain(&converted.env),
            parameters,
            result: *result,
        })
    }

    /// The Bend type of a semantic type.
    pub(super) fn bend_type(&mut self, ty: &SemanticType) -> Result<BTerm, Diagnostic> {
        let canonical = self.lower.canonical(ty);
        Ok(plain(&self.lower.ty(&canonical)?))
    }

    /// A function-valued term applied to fresh locals of the given types:
    /// the Bend term, over those locals' names.
    pub(super) fn applied(
        &mut self,
        context: &Context<'_>,
        function: &SemanticTerm,
        locals: &[(String, SemanticType)],
    ) -> Result<BTerm, Diagnostic> {
        let mut scope = context.scope.clone();
        let mut arguments = Vec::new();
        for (name, ty) in locals {
            scope = scope.with_generated(name, self.lower.canonical(ty));
            arguments.push(SemanticTerm::Var {
                name: super::super::generated(name),
            });
        }
        let applied = apply_semantic(function, arguments);
        Ok(plain(&self.lower.term(&applied, &scope)?))
    }

    /// A function-valued term applied to Bend terms.
    pub(super) fn applied_to(
        &mut self,
        context: &Context<'_>,
        function: &SemanticTerm,
        types: &[SemanticType],
        args: &[BTerm],
    ) -> Result<BTerm, Diagnostic> {
        let names: Vec<(String, SemanticType)> = types
            .iter()
            .map(|ty| (self.fresh("v"), ty.clone()))
            .collect();
        let body = self.applied(context, function, &names)?;
        let map: BTreeMap<String, BTerm> = names
            .iter()
            .map(|(name, _)| name.clone())
            .zip(args.iter().cloned())
            .collect();
        Ok(subst(&body, &map))
    }

    /// A predicate argument as a Bend proposition over a fresh local of
    /// type `ty`: a predicate term, `True`, or a function value.
    pub(super) fn predicate(
        &mut self,
        context: &Context<'_>,
        term: &ProofTerm,
        ty: &SemanticType,
    ) -> Result<(String, BTerm), Diagnostic> {
        let name = self.fresh("v");
        match term {
            ProofTerm::Predicate { binder, body } => {
                let canonical = self.lower.canonical(&binder.r#type);
                let scope = context.scope.bind(&binder.name, name.clone(), canonical);
                Ok((name, plain(&formula_type(self.lower, body, &scope)?)))
            }
            ProofTerm::Term { term } => {
                let body = self.applied(context, term, &[(name.clone(), ty.clone())])?;
                Ok((name, body))
            }
            other => Err(fail(format!("a lemma expected a predicate, not {other:?}"))),
        }
    }

    /// A definition below the theorem, generic in its type parameters, with
    /// its template argument.
    pub(super) fn define(
        &mut self,
        stem: &str,
        params: Vec<Param>,
        result: BTerm,
        body: Body,
    ) -> (String, BTerm) {
        let name = self.below(stem);
        // A data proof the template binds affinely may be used twice (two
        // theorems over the same step equation), so it is shared first.
        let mut stmts: Vec<Stmt> = params
            .iter()
            .filter(|param| {
                param.quantity == Quantity::Affine && self.lower.prop_is_data(&param.ty)
            })
            .map(|param| Stmt::Share {
                name: param.name.clone(),
                value: var(param.name.text.clone()),
                source: here(),
            })
            .collect();
        stmts.extend(body.stmts);
        let body = Body {
            stmts,
            tail: body.tail,
        };
        let mut all = self.template_params();
        all.extend(params);
        self.push(Item::Def {
            name: synthetic(name.clone()),
            params: all,
            result,
            result_source: here(),
            body,
            source: here(),
        });
        let templates = self.templates();
        let argument = if templates.is_empty() {
            var(name.clone())
        } else {
            call(name.clone(), templates)
        };
        (name, template(argument))
    }

    #[allow(clippy::too_many_lines)]
    fn lemma(
        &mut self,
        context: &Context<'_>,
        lemma: Lemma,
        args: &[ProofTerm],
        hyps: &Hyps,
        expected: Option<&BTerm>,
        mut extra: Vec<BTerm>,
    ) -> Result<BTerm, Diagnostic> {
        let arg = |index: usize| -> Result<&ProofTerm, Diagnostic> {
            args.get(index)
                .ok_or_else(|| fail(format!("`{}` lost an argument", lemma.lean())))
        };
        let mut out = match lemma {
            Lemma::Guarded | Lemma::GuardedRank => {
                let state = given(arg(1)?)?;
                let ty = self.lower.infer(state, &context.scope)?;
                let mut lowered = vec![self.bend_type(&ty)?];
                lowered.push(self.proof(context, arg(0)?, hyps, None)?);
                lowered.push(self.proof(context, arg(1)?, hyps, None)?);
                lowered.push(self.proof(context, arg(2)?, hyps, None)?);
                lowered.push(self.proof(context, arg(3)?, hyps, None)?);
                lowered.push(self.eta(context, arg(4)?, 1, hyps)?);
                lowered.push(self.proof(context, arg(5)?, hyps, None)?);
                let name = if lemma == Lemma::Guarded {
                    "RS.guarded"
                } else {
                    "RS.guardedRank"
                };
                call(name, lowered)
            }
            Lemma::ReachesStart => {
                let expected = arguments_of(expected, "R.LexLeanReasoning.Reaches")?;
                let mut lowered = vec![expected[0].clone(), expected[1].clone()];
                lowered.push(self.proof(context, arg(0)?, hyps, None)?);
                lowered.push(self.proof(context, arg(1)?, hyps, None)?);
                call("R.LexLeanReasoning.reachesStart", lowered)
            }
            Lemma::StarRefl => {
                let star = arguments_of(expected, "R.LexLeanReasoning.Star")?;
                call(
                    "R.LexLeanReasoning.Star.refl",
                    vec![star[0].clone(), star[1].clone(), star[2].clone()],
                )
            }
            Lemma::StarTail => {
                let star = arguments_of(expected, "R.LexLeanReasoning.Star")?.to_vec();
                let mid = self.proof(context, arg(1)?, hyps, None)?;
                let end = self.proof(context, arg(2)?, hyps, None)?;
                let prefix = self.proof(context, arg(3)?, hyps, None)?;
                let last = self.proof(context, arg(4)?, hyps, None)?;
                call(
                    "R.LexLeanReasoning.Star.tail",
                    vec![
                        star[0].clone(),
                        star[1].clone(),
                        star[2].clone(),
                        mid,
                        end,
                        prefix,
                        last,
                    ],
                )
            }
            Lemma::AllNil => {
                let all = arguments_of(expected, "R.LexLeanReasoning.All")?;
                call(
                    "R.LexLeanReasoning.All.nil",
                    vec![all[0].clone(), all[1].clone()],
                )
            }
            Lemma::NoneSome => {
                let e = self.proof(context, arg(1)?, hyps, None)?;
                let ty = match &e {
                    BTerm::Name(name) => self.hyp_types.get(&name.text).cloned(),
                    _ => None,
                }
                .ok_or_else(|| fail("`noneSome` refutes an equation whose type is unknown"))?;
                let (_, right, maybe) = super::templates::equation(&ty)?;
                let (BTerm::Datatype(_, _, element), BTerm::Constructor(_, payload)) =
                    (&maybe, &right)
                else {
                    return Err(fail(
                        "`noneSome` refutes an equation that is not onto `Some`",
                    ));
                };
                let goal = expected
                    .cloned()
                    .ok_or_else(|| fail("`noneSome` proves a goal it cannot see"))?;
                call(
                    "RS.noneSome",
                    vec![
                        element.first().cloned().unwrap_or_else(|| var("Unit")),
                        goal,
                        payload.first().cloned().unwrap_or_else(|| var("Unit")),
                        e,
                    ],
                )
            }
            Lemma::AllSingle => {
                let ok = self.proof(context, arg(0)?, hyps, None)?;
                let element = given(arg(1)?)?;
                let ty = self.lower.infer(element, &context.scope)?;
                let node = self.bend_type(&ty)?;
                let value = self.proof(context, arg(1)?, hyps, None)?;
                let wanted = super::folds::beta(&ok, &value);
                let held = self.proof(context, arg(2)?, hyps, Some(&wanted))?;
                super::folds::all_single(&node, &ok, value, held)
            }
            Lemma::AllAppend => {
                let [node, ok, list] = arguments_of(expected, "R.LexLeanReasoning.All")? else {
                    return Err(fail("`allAppend` proves no `All`"));
                };
                let (node, ok, list) = (node.clone(), ok.clone(), list.clone());
                let saved = self.unfold_all;
                self.unfold_all = true;
                let appended = self.whnf(&list).term().clone();
                self.unfold_all = saved;
                let parts = match &appended {
                    BTerm::Call(head, args)
                        if head.text == "R.LexLeanRuntime.append.List" && args.len() == 3 =>
                    {
                        (args[1].clone(), args[2].clone())
                    }
                    other => {
                        return Err(fail(format!(
                            "`allAppend` proves `All` of {}, which is no append",
                            super::engine::show(other)
                        )))
                    }
                };
                let first = super::folds::all(&node, &ok, parts.0.clone());
                let second = super::folds::all(&node, &ok, parts.1.clone());
                let first = self.proof(context, arg(3)?, hyps, Some(&first))?;
                let second = self.proof(context, arg(4)?, hyps, Some(&second))?;
                super::folds::all_append(&node, &ok, parts.0, parts.1, first, second)
            }
            Lemma::SearchStart => {
                let [node, answer, ok, accept, frontier, _] =
                    arguments_of(expected, "RS.SearchOk")?
                else {
                    return Err(fail("`searchStart` proves no `SearchOk`"));
                };
                let (node, answer, ok, accept, frontier) = (
                    node.clone(),
                    answer.clone(),
                    ok.clone(),
                    accept.clone(),
                    frontier.clone(),
                );
                let wanted = super::folds::all(&node, &ok, frontier.clone());
                let held = self.proof(context, arg(3)?, hyps, Some(&wanted))?;
                call(
                    "RS.searchStart",
                    vec![node, answer, ok, accept, frontier, held],
                )
            }
            Lemma::CapAll => {
                let [node, ok, list] = arguments_of(expected, "R.LexLeanReasoning.All")? else {
                    return Err(fail("`capAll` proves no `All`"));
                };
                let (node, ok, list) = (node.clone(), ok.clone(), list.clone());
                let fold = super::folds::Fold::of(self, &list)?;
                let wanted = super::folds::all(&node, &ok, fold.values.clone());
                let values_ok = self.proof(context, arg(3)?, hyps, Some(&wanted))?;
                self.cap_all(context, &fold, &node, &ok, values_ok)?
            }
            Lemma::CapBound => {
                let [measured, _] = arguments_of(expected, "S.Sem.le")? else {
                    return Err(fail("`capBound` proves no `<=`"));
                };
                let list = self.measured_list(measured)?;
                let fold = super::folds::Fold::of(self, &list)?;
                self.cap_bound(&fold)?
            }
            Lemma::FreshAll => {
                let [node, ok, list] = arguments_of(expected, "R.LexLeanReasoning.All")? else {
                    return Err(fail("`freshAll` proves no `All`"));
                };
                let (node, ok, list) = (node.clone(), ok.clone(), list.clone());
                let fold = super::folds::Fold::of(self, &list)?;
                if extra.is_empty() {
                    return Err(fail("`freshAll` lost the proof about the nodes it filters"));
                }
                let values_ok = extra.remove(0);
                self.fresh_all(context, &fold, &node, &ok, values_ok)?
            }
            Lemma::ZeroLe => {
                let le = arguments_of(expected, "S.Sem.le")?;
                call("RS.zeroLe", vec![le[1].clone()])
            }
            Lemma::FoldInvariant => self.fold_invariant(context, args, hyps)?,
            Lemma::StarPreserves => self.star_preserves(context, args, hyps)?,
            Lemma::IterateUntilInvariant => {
                let step = self.step_of(context, arg(0)?)?;
                let state = step
                    .parameters
                    .first()
                    .cloned()
                    .ok_or_else(|| fail("a loop step takes no state"))?;
                let (v, body) = self.predicate(context, arg(1)?, &state)?;
                self.iterate_invariant(
                    context,
                    &step,
                    &v,
                    body,
                    arg(2)?,
                    arg(3)?,
                    arg(4)?,
                    arg(5)?,
                    hyps,
                )?
            }
            Lemma::IterateUntilBound => {
                let step = self.step_of(context, arg(0)?)?;
                let state = step
                    .parameters
                    .first()
                    .cloned()
                    .ok_or_else(|| fail("a loop step takes no state"))?;
                let counter = given(arg(1)?)?.clone();
                let bound = given(arg(2)?)?.clone();
                let v = self.fresh("v");
                let mut scope = context.scope.clone();
                scope = scope.with_generated(&v, self.lower.canonical(&state));
                let le = SemanticTerm::Le {
                    left: Box::new(apply_semantic(
                        &counter,
                        vec![SemanticTerm::Var {
                            name: super::super::generated(&v),
                        }],
                    )),
                    right: Box::new(bound),
                };
                let body = plain(&self.lower.term(&le, &scope)?);
                self.iterate_invariant(
                    context,
                    &step,
                    &v,
                    body,
                    arg(3)?,
                    arg(4)?,
                    arg(5)?,
                    arg(6)?,
                    hyps,
                )?
            }
            Lemma::IterateUntilCount | Lemma::IterateUntilGrowth => {
                self.iterate_count(context, lemma == Lemma::IterateUntilCount, args, hyps)?
            }
            Lemma::IterateUntilStops => self.iterate_stops(context, args, hyps)?,
            Lemma::IterateUntilSimulate => self.iterate_simulate(context, args, hyps)?,
        };
        if !extra.is_empty() {
            out = match out {
                BTerm::Call(head, mut args) => {
                    args.extend(extra);
                    BTerm::Call(head, args)
                }
                other => BTerm::Apply(Box::new(other), extra),
            };
        }
        Ok(out)
    }

    /// `starPreserves r j hp a c h ha`.
    fn star_preserves(
        &mut self,
        context: &Context<'_>,
        args: &[ProofTerm],
        hyps: &Hyps,
    ) -> Result<BTerm, Diagnostic> {
        let [r, j, hp, a, c, h, ha] = args else {
            return Err(fail("`starPreserves` takes seven arguments"));
        };
        let start = given(a)?;
        let state = self.lower.infer(start, &context.scope)?;
        let state = self.lower.canonical(&state);
        let state_type = self.bend_type(&state)?;
        let (k_type, k, rebind) = environment(self.lower, context, &var("ll_k"));
        let relation = given(r)?.clone();
        let related = self.applied_to(
            context,
            &relation,
            &[state.clone(), state.clone()],
            &[var("ll_s"), var("ll_t")],
        )?;
        let (rel, rel_arg) = self.define(
            "rel",
            vec![
                reusable("ll_k", k_type.clone()),
                reusable("ll_s", state_type.clone()),
                reusable("ll_t", state_type.clone()),
            ],
            BTerm::Kind("Type"),
            Body {
                stmts: rebind.clone(),
                tail: Tail::Term(related, here()),
            },
        );
        let (v, body) = self.predicate(context, j, &state)?;
        let (inv, inv_arg) = self.define(
            "inv",
            vec![
                reusable("ll_k", k_type.clone()),
                reusable(&v, state_type.clone()),
            ],
            BTerm::Kind("Type"),
            Body {
                stmts: rebind.clone(),
                tail: Tail::Term(body.clone(), here()),
            },
        );
        let named = |engine: &Self, head: &str, args: Vec<BTerm>| {
            let mut all = engine.templates();
            all.push(var("ll_k"));
            all.extend(args);
            call(head.to_owned(), all)
        };
        let result = named(self, &inv, vec![var("ll_t")]);
        let wanted = subst(&body, &one(&v, var("ll_t")));
        let hyp_body = self.apply(
            context,
            hp,
            vec![var("ll_s"), var("ll_t"), var("ll_p"), var("ll_q")],
            hyps,
            Some(&wanted),
        )?;
        let (_, hyp_arg) = self.define(
            "hyp",
            vec![
                reusable("ll_k", k_type.clone()),
                reusable("ll_s", state_type.clone()),
                reusable("ll_t", state_type.clone()),
                affine("ll_p", named(self, &inv, vec![var("ll_s")])),
                affine("ll_q", named(self, &rel, vec![var("ll_s"), var("ll_t")])),
            ],
            result,
            Body {
                stmts: rebind,
                tail: Tail::Term(hyp_body, here()),
            },
        );
        let first = self.proof(context, a, hyps, None)?;
        let last = self.proof(context, c, hyps, None)?;
        let closure = self.proof(context, h, hyps, None)?;
        let initial = self.proof(
            context,
            ha,
            hyps,
            Some(&subst(&body, &one(&v, first.clone()))),
        )?;
        Ok(call(
            "RS.starPreserves",
            vec![
                template(state_type),
                template(k_type),
                rel_arg,
                inv_arg,
                hyp_arg,
                k,
                first,
                last,
                closure,
                initial,
            ],
        ))
    }

    /// The list whose length `measured` is: the term itself, or what the
    /// definitions it calls unfold to (a ledger field the start state
    /// records is the length of the frontier it starts with).
    fn measured_list(&mut self, measured: &BTerm) -> Result<BTerm, Diagnostic> {
        const LENGTH: &str = "R.LexLeanRuntime.length.List";
        let length_of = |term: &BTerm| match term {
            BTerm::Call(head, args) if head.text == LENGTH && args.len() == 2 => {
                Some(args[1].clone())
            }
            _ => None,
        };
        if let Some(list) = length_of(measured) {
            return Ok(list);
        }
        let mut heads = Vec::new();
        call_heads(measured, &mut heads);
        let added: Vec<String> = heads
            .into_iter()
            .filter(|head| head != LENGTH && self.unfold.insert(head.clone()))
            .collect();
        let reached = self.whnf(measured).term().clone();
        for head in &added {
            self.unfold.remove(head);
        }
        length_of(&reached).ok_or_else(|| {
            fail(format!(
                "`capBound` bounds {}, which is no length",
                super::engine::show(measured)
            ))
        })
    }

    /// `foldInvariant f p h xs init hinit`.
    fn fold_invariant(
        &mut self,
        context: &Context<'_>,
        args: &[ProofTerm],
        hyps: &Hyps,
    ) -> Result<BTerm, Diagnostic> {
        let [f, p, h, xs, init, hinit] = args else {
            return Err(fail("`foldInvariant` takes six arguments"));
        };
        let step = self.step_of(context, f)?;
        let [held, element] = step.parameters.as_slice() else {
            return Err(fail("a fold step takes a state and an element"));
        };
        let (held, element) = (held.clone(), element.clone());
        let held_type = self.bend_type(&held)?;
        let element_type = self.bend_type(&element)?;
        let (k_type, k, rebind) = environment(self.lower, context, &var("ll_k"));
        let rebind = from_env(rebind, &step.env);
        let (v, body) = self.predicate(context, p, &held)?;
        let (inv, inv_arg) = self.define(
            "inv",
            vec![
                reusable("ll_k", k_type.clone()),
                reusable("ll_e", step.env_type.clone()),
                reusable(&v, held_type.clone()),
            ],
            BTerm::Kind("Type"),
            Body {
                stmts: rebind.clone(),
                tail: Tail::Term(body.clone(), here()),
            },
        );
        let at = |engine: &Self, k: BTerm, s: BTerm| {
            let mut all = engine.templates();
            all.extend([k, var("ll_e"), s]);
            call(inv.clone(), all)
        };
        let result = at(
            self,
            var("ll_k"),
            step.at(var("ll_e"), vec![var("ll_s"), var("ll_a")]),
        );
        let wanted = subst(
            &body,
            &one(&v, step.at(var("ll_e"), vec![var("ll_s"), var("ll_a")])),
        );
        let hyp_body = self.apply(
            context,
            h,
            vec![var("ll_s"), var("ll_a"), var("ll_p")],
            hyps,
            Some(&wanted),
        )?;
        let (_, hyp_arg) = self.define(
            "hyp",
            vec![
                reusable("ll_e", step.env_type.clone()),
                reusable("ll_k", k_type.clone()),
                reusable("ll_s", held_type.clone()),
                reusable("ll_a", element_type.clone()),
                affine("ll_p", at(self, var("ll_k"), var("ll_s"))),
            ],
            result,
            Body {
                stmts: rebind,
                tail: Tail::Term(hyp_body, here()),
            },
        );
        let values = self.proof(context, xs, hyps, None)?;
        let initial = self.proof(context, init, hyps, None)?;
        let wanted = subst(&body, &one(&v, initial.clone()));
        let start = self.proof(context, hinit, hyps, Some(&wanted))?;
        Ok(call(
            "RS.foldInvariant",
            vec![
                template(element_type),
                template(held_type),
                template(step.env_type.clone()),
                template(step.code.clone()),
                template(k_type),
                inv_arg,
                hyp_arg,
                step.env.clone(),
                k,
                values,
                initial,
                start,
            ],
        ))
    }

    /// `iterateUntilInvariant step p h fuel init hinit`, with `p` the
    /// proposition `body` over the local `v`.
    #[allow(clippy::too_many_arguments)]
    fn iterate_invariant(
        &mut self,
        context: &Context<'_>,
        step: &StepFn,
        v: &str,
        body: BTerm,
        h: &ProofTerm,
        fuel: &ProofTerm,
        init: &ProofTerm,
        hinit: &ProofTerm,
        hyps: &Hyps,
    ) -> Result<BTerm, Diagnostic> {
        let state = step
            .parameters
            .first()
            .cloned()
            .ok_or_else(|| fail("a loop step takes no state"))?;
        let state_type = self.bend_type(&state)?;
        let next_type = self.bend_type(&step.result)?;
        let (k_type, k, rebind) = environment(self.lower, context, &var("ll_k"));
        let rebind = from_env(rebind, &step.env);
        let (inv, inv_arg) = self.define(
            "inv",
            vec![
                reusable("ll_k", k_type.clone()),
                reusable("ll_e", step.env_type.clone()),
                reusable(v, state_type.clone()),
            ],
            BTerm::Kind("Type"),
            Body {
                stmts: rebind.clone(),
                tail: Tail::Term(body.clone(), here()),
            },
        );
        let at = |engine: &Self, s: BTerm| {
            let mut all = engine.templates();
            all.push(var("ll_k"));
            all.push(var("ll_e"));
            all.push(s);
            call(inv.clone(), all)
        };
        let result = at(self, var("ll_b"));
        let moved = BTerm::Equal(
            Box::new(step.at(var("ll_e"), vec![var("ll_a")])),
            Box::new(BTerm::Constructor(synthetic("Some"), vec![var("ll_b")])),
            Box::new(next_type),
        );
        let wanted = subst(&body, &one(v, var("ll_b")));
        let hyp_body = self.apply(
            context,
            h,
            vec![var("ll_a"), var("ll_b"), var("ll_en"), var("ll_p")],
            hyps,
            Some(&wanted),
        )?;
        let (_, hyp_arg) = self.define(
            "hyp",
            vec![
                reusable("ll_e", step.env_type.clone()),
                reusable("ll_k", k_type.clone()),
                reusable("ll_a", state_type.clone()),
                reusable("ll_b", state_type.clone()),
                affine("ll_en", moved),
                affine("ll_p", at(self, var("ll_a"))),
            ],
            result,
            Body {
                stmts: rebind,
                tail: Tail::Term(hyp_body, here()),
            },
        );
        let fuel = self.proof(context, fuel, hyps, None)?;
        let initial = self.proof(context, init, hyps, None)?;
        let wanted = subst(&body, &one(v, initial.clone()));
        let start = self.proof(context, hinit, hyps, Some(&wanted))?;
        Ok(call(
            "RS.iterateUntilInvariant",
            vec![
                template(state_type),
                template(step.env_type.clone()),
                template(step.code.clone()),
                template(k_type),
                inv_arg,
                hyp_arg,
                step.env.clone(),
                k,
                fuel,
                initial,
                start,
            ],
        ))
    }

    /// The fuel law instantiated at the invariant `body` over `n` (the fuel
    /// left) and `v` (the state), with the hypothesis `hyp_body` over the
    /// law's binders; returns the law's application and the loop's run.
    #[allow(clippy::too_many_arguments, clippy::type_complexity)]
    fn iterate_fuel(
        &mut self,
        context: &Context<'_>,
        step: &StepFn,
        n: &str,
        v: &str,
        body: BTerm,
        hyp: &mut dyn FnMut(
            &mut Self,
            &dyn Fn(&Self, BTerm, BTerm) -> BTerm,
        ) -> Result<BTerm, Diagnostic>,
        fuel: BTerm,
        initial: BTerm,
        start: BTerm,
    ) -> Result<(BTerm, BTerm), Diagnostic> {
        let state = step
            .parameters
            .first()
            .cloned()
            .ok_or_else(|| fail("a loop step takes no state"))?;
        let state_type = self.bend_type(&state)?;
        let next_type = self.bend_type(&step.result)?;
        let (k_type, k, rebind) = environment(self.lower, context, &var("ll_k"));
        let rebind = from_env(rebind, &step.env);
        let (inv, inv_arg) = self.define(
            "inv",
            vec![
                reusable("ll_k", k_type.clone()),
                reusable("ll_e", step.env_type.clone()),
                reusable(n, var("Nat")),
                reusable(v, state_type.clone()),
            ],
            BTerm::Kind("Type"),
            Body {
                stmts: rebind.clone(),
                tail: Tail::Term(body, here()),
            },
        );
        let at = move |engine: &Self, fuel: BTerm, s: BTerm| {
            let mut all = engine.templates();
            all.push(var("ll_k"));
            all.push(var("ll_e"));
            all.push(fuel);
            all.push(s);
            call(inv.clone(), all)
        };
        let result = at(self, var("ll_n"), var("ll_b"));
        let before = at(self, BTerm::Succ(Box::new(var("ll_n"))), var("ll_a"));
        let moved = BTerm::Equal(
            Box::new(step.at(var("ll_e"), vec![var("ll_a")])),
            Box::new(BTerm::Constructor(synthetic("Some"), vec![var("ll_b")])),
            Box::new(next_type),
        );
        let hyp_body = hyp(self, &at)?;
        let (_, hyp_arg) = self.define(
            "hyp",
            vec![
                reusable("ll_e", step.env_type.clone()),
                reusable("ll_k", k_type.clone()),
                reusable("ll_n", var("Nat")),
                reusable("ll_a", state_type.clone()),
                reusable("ll_b", state_type.clone()),
                affine("ll_en", moved),
                affine("ll_p", before),
            ],
            result,
            Body {
                stmts: rebind,
                tail: Tail::Term(hyp_body, here()),
            },
        );
        let run = call(
            "S.Sem.iterateUntil",
            vec![
                template(state_type.clone()),
                template(step.env_type.clone()),
                template(step.code.clone()),
                step.env.clone(),
                fuel.clone(),
                initial.clone(),
            ],
        );
        let law = call(
            "RS.iterateUntilFuel",
            vec![
                template(state_type),
                template(step.env_type.clone()),
                template(step.code.clone()),
                template(k_type),
                inv_arg,
                hyp_arg,
                step.env.clone(),
                k,
                fuel,
                initial,
                start,
            ],
        );
        Ok((law, run))
    }

    /// `iterateUntilCount step c h fuel init h0` (or `Growth`): the fuel law
    /// at `c s + n <= fuel`, finished by `fuelBound`.
    fn iterate_count(
        &mut self,
        context: &Context<'_>,
        exact: bool,
        args: &[ProofTerm],
        hyps: &Hyps,
    ) -> Result<BTerm, Diagnostic> {
        let [f, c, h, fuel, init, h0] = args else {
            return Err(fail("`iterateUntilCount` takes six arguments"));
        };
        if !matches!(h0, ProofTerm::Refl) {
            return Err(fail("a counter that does not start at zero by computation"));
        }
        let step = self.step_of(context, f)?;
        let state = step
            .parameters
            .first()
            .cloned()
            .ok_or_else(|| fail("a loop step takes no state"))?;
        let counter = given(c)?.clone();
        let fuel_term = given(fuel)?.clone();
        let fuel_value = self.proof(context, fuel, hyps, None)?;
        let initial = self.proof(context, init, hyps, None)?;
        let n = self.fresh("n");
        let v = self.fresh("v");
        let mut scope = context.scope.clone();
        scope = scope.with_generated(&n, SemanticType::Nat);
        scope = scope.with_generated(&v, self.lower.canonical(&state));
        let bound = SemanticTerm::Le {
            left: Box::new(SemanticTerm::Add {
                left: Box::new(apply_semantic(
                    &counter,
                    vec![SemanticTerm::Var {
                        name: super::super::generated(&v),
                    }],
                )),
                right: Box::new(SemanticTerm::Var {
                    name: super::super::generated(&n),
                }),
            }),
            right: Box::new(fuel_term),
        };
        let body = plain(&self.lower.term(&bound, &scope)?);
        let fuel_in = fuel_value.clone();
        let types = vec![state.clone()];
        let mut hyp = |engine: &mut Self, _: &dyn Fn(&Self, BTerm, BTerm) -> BTerm| {
            let before = engine.applied_to(context, &counter, &types, &[var("ll_a")])?;
            let after = engine.applied_to(context, &counter, &types, &[var("ll_b")])?;
            let grows = engine.apply(
                context,
                h,
                vec![var("ll_a"), var("ll_b"), var("ll_en")],
                hyps,
                None,
            )?;
            Ok(call(
                if exact { "RS.countPres" } else { "RS.growPres" },
                vec![
                    before,
                    after,
                    var("ll_n"),
                    fuel_in.clone(),
                    grows,
                    var("ll_p"),
                ],
            ))
        };
        let start = call("RS.fuelStart", vec![fuel_value.clone()]);
        let (law, run) = self.iterate_fuel(
            context,
            &step,
            &n,
            &v,
            body,
            &mut hyp,
            fuel_value.clone(),
            initial,
            start,
        )?;
        let state_type = self.bend_type(&state)?;
        let last = call(
            "S.Sem.fst",
            vec![state_type.clone(), var("Bool"), run.clone()],
        );
        let stopped = call("S.Sem.snd", vec![state_type, var("Bool"), run]);
        let counted = self.applied_to(context, &counter, &[state], &[last])?;
        Ok(call(
            "RS.fuelBound",
            vec![counted, fuel_value, stopped, law],
        ))
    }

    /// `iterateUntilStops step p mu h fuel init hinit hmu`: the fuel law at
    /// `p s /\ mu s < n`, finished by `fuelStops`.
    fn iterate_stops(
        &mut self,
        context: &Context<'_>,
        args: &[ProofTerm],
        hyps: &Hyps,
    ) -> Result<BTerm, Diagnostic> {
        let [f, p, mu, h, fuel, init, hinit, hmu] = args else {
            return Err(fail("`iterateUntilStops` takes eight arguments"));
        };
        let step = self.step_of(context, f)?;
        let state = step
            .parameters
            .first()
            .cloned()
            .ok_or_else(|| fail("a loop step takes no state"))?;
        let measure = given(mu)?.clone();
        let (pv, held) = self.predicate(context, p, &state)?;
        let fuel_value = self.proof(context, fuel, hyps, None)?;
        let initial = self.proof(context, init, hyps, None)?;
        let n = self.fresh("n");
        let v = self.fresh("v");
        let types = vec![state.clone()];
        let rank_v = self.applied_to(context, &measure, &types, &[var(v.clone())])?;
        let held_at = |s: BTerm| subst(&held, &one(&pv, s));
        let body = call(
            "L.Lean.Prod",
            vec![
                held_at(var(v.clone())),
                call("S.Sem.lt", vec![rank_v, var(n.clone())]),
            ],
        );
        let mut hyp = |engine: &mut Self, _: &dyn Fn(&Self, BTerm, BTerm) -> BTerm| {
            let before = engine.applied_to(context, &measure, &types, &[var("ll_a")])?;
            let after = engine.applied_to(context, &measure, &types, &[var("ll_b")])?;
            let kept = engine.eta_with(
                context,
                h,
                vec![var("ll_a"), var("ll_b"), var("ll_en")],
                hyps,
            )?;
            Ok(call(
                "RS.stopsStep",
                vec![
                    held_at(var("ll_a")),
                    held_at(var("ll_b")),
                    after,
                    before,
                    var("ll_n"),
                    var("ll_p"),
                    kept,
                ],
            ))
        };
        let first = self.proof(context, hinit, hyps, Some(&held_at(initial.clone())))?;
        let second = self.proof(context, hmu, hyps, None)?;
        let start = BTerm::Pair(Box::new(first), Box::new(second));
        let (law, run) = self.iterate_fuel(
            context, &step, &n, &v, body, &mut hyp, fuel_value, initial, start,
        )?;
        let state_type = self.bend_type(&state)?;
        let last = call(
            "S.Sem.fst",
            vec![state_type.clone(), var("Bool"), run.clone()],
        );
        let stopped = call("S.Sem.snd", vec![state_type, var("Bool"), run]);
        let rank = self.applied_to(context, &measure, &types, std::slice::from_ref(&last))?;
        Ok(call(
            "RS.fuelStops",
            vec![held_at(last), stopped, rank, law],
        ))
    }

    /// A function of one more hypothesis applying `term` to `args` and it.
    /// The hypothesis is data (`stopsStep` holds the invariant at kind
    /// `Data`) and a pair of proofs may use it twice, so it is reusable.
    fn eta_with(
        &mut self,
        context: &Context<'_>,
        term: &ProofTerm,
        mut args: Vec<BTerm>,
        hyps: &Hyps,
    ) -> Result<BTerm, Diagnostic> {
        let name = self.fresh("h");
        args.push(var(name.clone()));
        let body = self.apply(context, term, args, hyps, None)?;
        Ok(BTerm::Lam(synthetic(format!("+{name}")), Box::new(body)))
    }

    /// `iterateUntilSimulate f g pi hnone hsome fuel init`: the lockstep law
    /// at the relation `pi a == b`.
    #[allow(clippy::too_many_lines)]
    fn iterate_simulate(
        &mut self,
        context: &Context<'_>,
        args: &[ProofTerm],
        hyps: &Hyps,
    ) -> Result<BTerm, Diagnostic> {
        let [f, g, pi, hnone, hsome, fuel, init] = args else {
            return Err(fail("`iterateUntilSimulate` takes seven arguments"));
        };
        let first = self.step_of(context, f)?;
        let second = self.step_of(context, g)?;
        let a = first
            .parameters
            .first()
            .cloned()
            .ok_or_else(|| fail("a loop step takes no state"))?;
        let b = second
            .parameters
            .first()
            .cloned()
            .ok_or_else(|| fail("a loop step takes no state"))?;
        let projection = given(pi)?.clone();
        let a_type = self.bend_type(&a)?;
        let b_type = self.bend_type(&b)?;
        let (k_type, k, rebind) = environment(self.lower, context, &var("ll_k"));
        let project = |engine: &mut Self, value: BTerm| {
            engine.applied_to(context, &projection, std::slice::from_ref(&a), &[value])
        };
        let related = project(self, var("ll_a"))?;
        let (rel, rel_arg) = self.define(
            "rel",
            vec![
                reusable("ll_k", k_type.clone()),
                reusable("ll_a", a_type.clone()),
                reusable("ll_b", b_type.clone()),
            ],
            BTerm::Kind("Data"),
            Body {
                stmts: rebind.clone(),
                tail: Tail::Term(
                    BTerm::Equal(
                        Box::new(related),
                        Box::new(var("ll_b")),
                        Box::new(b_type.clone()),
                    ),
                    here(),
                ),
            },
        );
        let templates = self.templates();
        let lock = |na: BTerm, nb: BTerm| {
            let mut rel_args = templates.clone();
            rel_args.extend([var("ll_k"), var("ll_u"), var("ll_w")]);
            call(
                "RS.Lock",
                vec![
                    a_type.clone(),
                    b_type.clone(),
                    BTerm::Lam(
                        synthetic("+ll_u"),
                        Box::new(BTerm::Lam(
                            synthetic("+ll_w"),
                            Box::new(call(rel.clone(), rel_args)),
                        )),
                    ),
                    na,
                    nb,
                ],
            )
        };
        let moved_a = first.at(var("ll_e"), vec![var("ll_a")]);
        let result = lock(moved_a.clone(), second.at(var("ll_f"), vec![var("ll_b")]));
        // `ll_r : pi a == b` turns the second step's state into `pi a`;
        // then the first step's result is split.
        let pi_a = project(self, var("ll_a"))?;
        let mut stmts = rebind.clone();
        stmts.push(Stmt::Rewrite {
            proof: var("ll_r"),
            motive: lock(moved_a.clone(), second.at(var("ll_f"), vec![BTerm::Hole])),
            source: here(),
        });
        let goal = lock(moved_a.clone(), second.at(var("ll_f"), vec![pi_a.clone()]));
        let mut state = State::new(goal);
        for (name, ty) in &context.values {
            state.push_value(name, ty.clone());
        }
        state.push_value("ll_e", first.env_type.clone());
        state.push_value("ll_f", second.env_type.clone());
        state.push_value("ll_k", k_type.clone());
        state.push_value("ll_a", a_type.clone());
        let next_a = self.bend_type(&first.result)?;
        let other_next = second.at(var("ll_f"), vec![pi_a.clone()]);
        let next_b = self.bend_type(&second.result)?;
        let split = self.split(&state, &moved_a, &next_a, &mut |engine, taken| {
            let en = taken
                .path
                .last()
                .and_then(|taken| taken.en.clone())
                .ok_or_else(|| fail("a lockstep split lost its equation"))?;
            let binders = taken
                .path
                .last()
                .map(|t| t.binders.clone())
                .unwrap_or_default();
            let mut inner = taken.clone();
            let mut stmts = Vec::new();
            let (proof, to, tail) = match binders.as_slice() {
                [] => (
                    engine.apply(
                        context,
                        hnone,
                        vec![var("ll_a"), var(en.clone())],
                        hyps,
                        None,
                    )?,
                    BTerm::Constructor(synthetic("None"), Vec::new()),
                    unit(),
                ),
                [q] => {
                    let pi_q = engine.applied_to(
                        context,
                        &projection,
                        std::slice::from_ref(&a),
                        &[var(q.clone())],
                    )?;
                    (
                        engine.apply(
                            context,
                            hsome,
                            vec![var("ll_a"), var(q.clone()), var(en.clone())],
                            hyps,
                            None,
                        )?,
                        BTerm::Constructor(synthetic("Some"), vec![pi_q]),
                        BTerm::Refl,
                    )
                }
                _ => return Err(fail("a lockstep split met an unexpected constructor")),
            };
            engine.rewrite(&mut inner, &mut stmts, &other_next, &to, proof, &next_b);
            Ok(Body {
                stmts,
                tail: Tail::Term(tail, here()),
            })
        })?;
        let (_, lock_arg) = self.define(
            "lock",
            vec![
                reusable("ll_e", first.env_type.clone()),
                reusable("ll_f", second.env_type.clone()),
                reusable("ll_k", k_type.clone()),
                reusable("ll_a", a_type.clone()),
                reusable("ll_b", b_type.clone()),
                affine("ll_r", {
                    let mut all = self.templates();
                    all.extend([var("ll_k"), var("ll_a"), var("ll_b")]);
                    call(rel.clone(), all)
                }),
            ],
            result,
            Body {
                stmts,
                tail: Tail::Term(split, here()),
            },
        );
        let fuel = self.proof(context, fuel, hyps, None)?;
        let initial = self.proof(context, init, hyps, None)?;
        let projected = project(self, initial.clone())?;
        Ok(call(
            "RS.iterateUntilLockstep",
            vec![
                template(a_type),
                template(b_type),
                template(first.env_type.clone()),
                template(second.env_type.clone()),
                template(first.code.clone()),
                template(second.code.clone()),
                template(k_type),
                rel_arg,
                lock_arg,
                first.env.clone(),
                second.env.clone(),
                k,
                fuel,
                initial,
                projected,
                BTerm::Refl,
            ],
        ))
    }
}

pub(super) fn reusable(name: &str, ty: BTerm) -> Param {
    Param {
        quantity: Quantity::Reusable,
        name: synthetic(name),
        ty,
        source: here(),
    }
}

pub(super) fn affine(name: &str, ty: BTerm) -> Param {
    Param {
        quantity: Quantity::Affine,
        name: synthetic(name),
        ty,
        source: here(),
    }
}

/// Unused import guard for formulas a predicate may carry.
#[allow(dead_code)]
fn formula_kind(_: &Formula) {}

/// `rebind` with the parameter the fold's environment `env` names bound to
/// the step's environment `ll_e` instead: the step reads its environment
/// through `ll_e`, so an invariant over the same parameter must too.
fn from_env(rebind: Vec<Stmt>, env: &BTerm) -> Vec<Stmt> {
    let BTerm::Name(env) = env else {
        return rebind;
    };
    rebind
        .into_iter()
        .map(|stmt| match stmt {
            Stmt::Share { name, source, .. } if name.text == env.text => Stmt::Share {
                name,
                value: var("ll_e"),
                source,
            },
            other => other,
        })
        .collect()
}

/// The heads of the calls in `term`, outermost first.
fn call_heads(term: &BTerm, heads: &mut Vec<String>) {
    if let BTerm::Call(head, args) = term {
        heads.push(head.text.clone());
        for arg in args {
            call_heads(arg, heads);
        }
    }
}
