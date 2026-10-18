//! The Bend counterparts of the fixed Lean templates (see
//! `backend::semantic::reasoning`), one per [`Proof`] variant.
//!
//! Each follows its Lean script step for step: `dsimp only [f]` is the set
//! of definitions [`Engine::whnf`] may unfold, `split at h` and `cases h`
//! are [`Engine::auto`], `generalize` is [`Engine::generalize`], `rw` is a
//! Bend rewrite, and `exact` is the same citation. A template names its
//! theorem's parameters by position, as the Lean script names them by the
//! names the elaboration gave them.

use super::engine::{block, conjuncts, show, values_of, Engine, Leaf, State, Whnf};
use super::lemmas::Hyps;
use super::{formula_type, peel_formula, Context};
use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Stmt, Tail};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::reasoning::{Formula, Helper, Proof, ProofTerm};
use crate::ir::semantic::MemberRef;

use super::super::{call, here, synthetic, var};

fn refl() -> Body {
    Body::term(BTerm::Refl, here())
}

fn term(proof: BTerm) -> Body {
    Body::term(proof, here())
}

/// The sides and type of an equation.
pub(super) fn equation(ty: &BTerm) -> Result<(BTerm, BTerm, BTerm), Diagnostic> {
    match ty {
        BTerm::Equal(left, right, ty) => Ok(((**left).clone(), (**right).clone(), (**ty).clone())),
        other => Err(fail(format!(
            "a generated proof expected an equation, not {}",
            show(other)
        ))),
    }
}

/// A function type's binder, domain, and codomain.
pub(super) fn arrow(ty: &BTerm) -> Result<(Option<String>, BTerm, BTerm), Diagnostic> {
    match ty {
        BTerm::Pi {
            name,
            domain,
            codomain,
            ..
        } => Ok((
            name.as_ref().map(|name| super::engine::bound(&name.text)),
            (**domain).clone(),
            (**codomain).clone(),
        )),
        other => Err(fail(format!(
            "a generated proof expected a function type, not {}",
            show(other)
        ))),
    }
}

/// The payload of a constructor term.
fn payload(term: &BTerm) -> Vec<BTerm> {
    match term {
        BTerm::Constructor(_, args) => args.clone(),
        _ => Vec::new(),
    }
}

impl Engine<'_, '_, '_> {
    /// The Bend name of one of the theorem's parameters, by position.
    pub(super) fn parameter(
        &self,
        context: &Context<'_>,
        index: usize,
    ) -> Result<String, Diagnostic> {
        context
            .values
            .get(index)
            .map(|(name, _)| name.clone())
            .ok_or_else(|| fail("a template lost one of its theorem's parameters"))
    }

    /// The theorem's premise `index`, from the end when `from_end`.
    pub(super) fn premise(context: &Context<'_>, index: usize) -> Result<String, Diagnostic> {
        context
            .premises
            .get(index)
            .cloned()
            .ok_or_else(|| fail("a template lost one of its theorem's premises"))
    }

    pub(super) fn last_premise(context: &Context<'_>) -> Result<String, Diagnostic> {
        context
            .premises
            .last()
            .cloned()
            .ok_or_else(|| fail("a template's theorem has no premise"))
    }

    /// The Bend head of a member.
    pub(super) fn head(&mut self, member: &MemberRef) -> Result<String, Diagnostic> {
        let home = self.lower.home(member);
        self.lower.spell(&home, &member.name)
    }

    /// Normalization may unfold these members.
    pub(super) fn unfolding(&mut self, members: &[&MemberRef]) -> Result<(), Diagnostic> {
        for member in members {
            let head = self.head(member)?;
            self.unfold.insert(head);
        }
        Ok(())
    }

    /// The reasoner's own theorem `member` cited at its type parameters.
    pub(super) fn own_law(
        &mut self,
        member: &MemberRef,
        args: Vec<BTerm>,
    ) -> Result<BTerm, Diagnostic> {
        let head = self.head(member)?;
        let mut all = self.templates();
        all.extend(args);
        Ok(self.applied_law(&head, all))
    }

    /// A theorem of this declaration at `args`, as a hypothesis: its
    /// statement, quantified over the binders and premises its law takes
    /// as parameters, and the law abstracted over them.
    pub(super) fn instance(
        &mut self,
        context: &Context<'_>,
        member: &MemberRef,
        args: &[BTerm],
    ) -> Result<(BTerm, BTerm), Diagnostic> {
        let theorem = context
            .siblings
            .iter()
            .find(|theorem| theorem.name == member.name)
            .ok_or_else(|| {
                fail(format!(
                    "a template names `{}`, which it does not know",
                    member.name
                ))
            })?;
        let (binders, premises, claim) = peel_formula(&theorem.statement);
        let mut scope = super::super::Scope::default();
        let mut map = std::collections::BTreeMap::new();
        for (parameter, arg) in theorem.parameters.iter().zip(args) {
            let local = self.fresh("p");
            let ty = self.lower.canonical(&parameter.r#type);
            scope = scope.bind(&parameter.name, local.clone(), ty);
            map.insert(local, arg.clone());
        }
        let mut quantified = Vec::new();
        for binder in &binders {
            let local = self.fresh("v");
            let ty = self.lower.canonical(&binder.r#type);
            let bend = super::engine::plain(&self.lower.ty(&ty)?);
            scope = scope.bind(&binder.name, local.clone(), ty);
            quantified.push((local, Some(bend)));
        }
        for premise in &premises {
            let local = self.fresh("h");
            let ty = super::engine::plain(&formula_type(self.lower, premise, &scope)?);
            quantified.push((local, None));
            let last = quantified.len() - 1;
            quantified[last].1 = Some(ty);
        }
        let mut ty = super::engine::plain(&formula_type(self.lower, &claim, &scope)?);
        let mut law_args = args.to_vec();
        law_args.extend(quantified.iter().map(|(name, _)| var(name.clone())));
        let mut proof = self.own_law(member, law_args)?;
        for (index, (name, domain)) in quantified.iter().enumerate().rev() {
            let value = index < binders.len();
            let domain = domain.clone().unwrap_or_else(|| var("Unit"));
            ty = BTerm::Pi {
                name: value.then(|| synthetic(format!("+{name}"))),
                erased: false,
                domain: Box::new(domain),
                codomain: Box::new(ty),
            };
            let binder = if value {
                format!("+{name}")
            } else {
                name.clone()
            };
            proof = BTerm::Lam(synthetic(binder), Box::new(proof));
        }
        Ok((
            super::engine::subst(&ty, &map),
            super::engine::subst(&proof, &map),
        ))
    }

    /// Unfold the subject hypothesis's left side once, so a term it
    /// computes with appears in its type (Lean's `dsimp only [f] at h`
    /// before `generalize`).
    pub(super) fn unfold_subject(
        &self,
        state: &mut State,
        subject: &str,
    ) -> Result<(), Diagnostic> {
        let (left, right, ty) = equation(&state.type_of(subject)?)?;
        let reduced = self.whnf(&left).term().clone();
        state.retype(
            subject,
            BTerm::Equal(Box::new(reduced), Box::new(right), Box::new(ty)),
        );
        Ok(())
    }
}

impl Engine<'_, '_, '_> {
    /// Introduce the goal's leading binders (Lean's `intro`): each value
    /// binder becomes a local and each premise a hypothesis, named fresh;
    /// returns the names bound, outermost first, and whether each is a
    /// value.
    pub(super) fn intro(
        &mut self,
        state: &mut State,
        count: usize,
    ) -> Result<Vec<(String, bool)>, Diagnostic> {
        let mut bound = Vec::new();
        for _ in 0..count {
            let (binder, domain, codomain) = arrow(&state.goal)?;
            match binder {
                Some(binder) => {
                    let name = self.fresh("v");
                    state.push_value(&name, domain);
                    state.goal =
                        super::engine::subst(&codomain, &super::one(&binder, var(name.clone())));
                    bound.push((name, true));
                }
                None => {
                    let name = self.fresh("h");
                    state.push_hypothesis(&name, domain);
                    state.goal = codomain;
                    bound.push((name, false));
                }
            }
        }
        Ok(bound)
    }

    /// Prove the goal by splitting `term`, a subterm of it, until it
    /// reaches a value or an opaque term (Lean's `split` on the goal); the
    /// leaf proves each branch.
    pub(super) fn auto_term(
        &mut self,
        state: &State,
        term: &BTerm,
        leaf: &mut dyn FnMut(&mut Self, &State) -> Result<Body, Diagnostic>,
    ) -> Result<Body, Diagnostic> {
        match self.whnf(term) {
            Whnf::Stuck {
                term: stuck,
                scrutinee,
                ty,
            } => {
                let mut restated = state.clone();
                restated.goal = super::engine::replace(&state.goal, term, &stuck);
                let proof = self.split(&restated, &scrutinee, &ty, &mut |engine, taken| {
                    let last = taken
                        .path
                        .last()
                        .ok_or_else(|| fail("a goal split lost its constructor"))?;
                    let value = super::engine::constructed(&last.constructor, &last.binders);
                    let next = super::engine::replace(&stuck, &scrutinee, &value);
                    engine.auto_term(&taken, &next, &mut *leaf)
                })?;
                Ok(Body::term(proof, here()))
            }
            _ => leaf(self, state),
        }
    }

    /// Bind the theorem `member` at `args` as a hypothesis.
    pub(super) fn have_theorem(
        &mut self,
        context: &Context<'_>,
        state: &mut State,
        name: &str,
        member: &MemberRef,
        args: &[BTerm],
    ) -> Result<(), Diagnostic> {
        let (ty, proof) = self.instance(context, member, args)?;
        state.have(name, ty, proof);
        Ok(())
    }
}

/// Prove a generated theorem's claim; `state` holds its parameters and
/// premises.
#[allow(clippy::too_many_lines)]
pub(super) fn prove(
    engine: &mut Engine<'_, '_, '_>,
    context: &Context<'_>,
    state: &State,
    claim: &Formula,
) -> Result<Body, Diagnostic> {
    let hyps = Hyps::new();
    match &context.theorem.proof {
        Proof::Term { term } | Proof::Unfold { term, .. } => {
            proof_term(engine, context, term, claim, &state.goal, &hyps).map(self::term)
        }
        Proof::FireCases { arms } => {
            let step = engine.parameter(context, 1)?;
            let ty = state.type_of(&step)?;
            let proof = engine.split(state, &var(step.clone()), &ty, &mut |engine, taken| {
                let last = taken
                    .path
                    .last()
                    .ok_or_else(|| fail("a step split lost its constructor"))?;
                let constructor = last.constructor.rsplit('.').next().unwrap_or("").to_owned();
                let arm = arms
                    .iter()
                    .find(|arm| arm.constructor.rsplit('.').next() == Some(constructor.as_str()))
                    .ok_or_else(|| fail(format!("no rule fires the step `{constructor}`")))?;
                let mut args = Vec::new();
                for (index, (name, _)) in context.values.iter().enumerate() {
                    if index == 1 {
                        args.extend(last.binders.iter().map(|b| var(b.clone())));
                    } else {
                        args.push(var(name.clone()));
                    }
                }
                args.extend(context.premises.iter().map(|p| var(p.clone())));
                let cited = engine.cite(&arm.theorem, &arm.type_arguments, args)?;
                Ok(self::term(cited))
            })?;
            Ok(self::term(proof))
        }
        Proof::ReplayFire { replay } => {
            engine.unfolding(&[replay])?;
            let subject = Engine::last_premise(context)?;
            let proof = engine.split_goal(state, &mut |engine, taken| {
                engine.auto(&taken, &subject, &mut |_, _, _| Ok(refl()))
            })?;
            Ok(self::term(proof))
        }
        Proof::ReplaySound { replay, fire_sound } => {
            engine.unfolding(&[replay])?;
            let acc = engine.parameter(context, 1)?;
            let step = engine.parameter(context, 2)?;
            let reaches = Engine::premise(context, 0)?;
            let ty = state.type_of(&acc)?;
            let fire_sound = fire_sound.clone();
            let proof = engine.split(state, &var(acc.clone()), &ty, &mut |engine, taken| {
                // `Reaches` is `@s -> {acc == Done{s}} -> Star<...>`.
                let BTerm::Call(_, args) = &taken.goal else {
                    return Err(fail("a replay's goal is not `Reaches`"));
                };
                let [state_type, _, relation, start, held] = args.as_slice() else {
                    return Err(fail("a replay's goal is not `Reaches`"));
                };
                let u = engine.fresh("u");
                let e = engine.fresh("e");
                let mut inner = taken.clone();
                inner.push_value(&u, state_type.clone());
                inner.push_hypothesis(
                    &e,
                    BTerm::Equal(
                        Box::new(held.clone()),
                        Box::new(BTerm::Constructor(synthetic("Done"), vec![var(u.clone())])),
                        Box::new(ty.clone()),
                    ),
                );
                inner.goal = BTerm::Datatype(
                    synthetic("R.LexLeanReasoning.Star"),
                    Vec::new(),
                    vec![
                        state_type.clone(),
                        relation.clone(),
                        start.clone(),
                        var(u.clone()),
                    ],
                );
                let prior = taken.path.last().cloned();
                let body = engine.auto(&inner, &e, &mut |engine, here_state, leaf| {
                    let Leaf::Value(values) = leaf else {
                        return Err(fail("a replay's step did not reach a state"));
                    };
                    let [next] = values.as_slice() else {
                        return Err(fail("a replay's step reached no single state"));
                    };
                    let fired = here_state
                        .path
                        .iter()
                        .rev()
                        .find(|taken| taken.en.is_some())
                        .ok_or_else(|| fail("a replay lost the step's equation"))?;
                    let held_state = prior
                        .as_ref()
                        .and_then(|prior| prior.binders.first().cloned())
                        .ok_or_else(|| fail("a replay lost its held state"))?;
                    let sound = engine.own_law(
                        &fire_sound,
                        vec![
                            var(held_state.clone()),
                            var(step.clone()),
                            next.clone(),
                            var(fired.en.clone().unwrap_or_default()),
                        ],
                    )?;
                    let reached = BTerm::Call(
                        synthetic(reaches.clone()),
                        vec![var(held_state.clone()), BTerm::Refl],
                    );
                    Ok(self::term(call(
                        "R.LexLeanReasoning.Star.tail",
                        vec![
                            state_type.clone(),
                            relation.clone(),
                            start.clone(),
                            var(held_state),
                            next.clone(),
                            reached,
                            sound,
                        ],
                    )))
                })?;
                Ok(self::term(BTerm::Lam(
                    synthetic(u),
                    Box::new(BTerm::Lam(synthetic(e), Box::new(block(body)))),
                )))
            })?;
            Ok(self::term(proof))
        }
        Proof::NextSound { next, fire_sound } => {
            engine.unfolding(&[next])?;
            let subject = Engine::last_premise(context)?;
            let fire_sound = fire_sound.clone();
            engine.auto(state, &subject, &mut |engine, here_state, leaf| {
                cite_stuck(engine, here_state, &fire_sound, leaf, &subject, &[])
            })
        }
        Proof::NextProgress {
            next,
            fire_progress,
            invariant,
        } => {
            engine.unfolding(&[next])?;
            let subject = Engine::premise(context, 0)?;
            let before = if *invariant {
                vec![var(Engine::premise(context, 1)?)]
            } else {
                Vec::new()
            };
            let fire_progress = fire_progress.clone();
            engine.auto(state, &subject, &mut |engine, here_state, leaf| {
                cite_stuck(engine, here_state, &fire_progress, leaf, &subject, &before)
            })
        }
        Proof::StepNone { step, next } | Proof::StepSome { step, next } => {
            engine.unfolding(&[step, next])?;
            engine.normalize_goal = true;
            let subject = Engine::last_premise(context)?;
            engine.auto(state, &subject, &mut |_, _, _| Ok(refl()))
        }
        Proof::StepCount { step } => {
            engine.unfolding(&[step])?;
            let subject = Engine::last_premise(context)?;
            engine.auto(state, &subject, &mut |_, _, _| Ok(refl()))
        }
        Proof::StepTrace {
            step,
            follow,
            replay_fire,
        } => {
            engine.unfolding(&[step])?;
            let subject = Engine::premise(context, 0)?;
            let traced = Engine::premise(context, 1)?;
            let follow = engine.head(follow)?;
            let replay_fire = replay_fire.clone();
            engine.auto(state, &subject, &mut |engine, here_state, _| {
                step_trace(engine, here_state, &follow, &traced, &replay_fire)
            })
        }
        Proof::AcceptSound {
            accept,
            sound,
            type_arguments,
        } => {
            engine.unfolding(&[accept])?;
            let subject = Engine::last_premise(context)?;
            let sound = sound.clone();
            let type_arguments = type_arguments.clone();
            engine.auto(state, &subject, &mut |engine, here_state, _| {
                // The check's equation is the last split's.
                let checked = here_state
                    .path
                    .last()
                    .filter(|taken| taken.constructor == "True")
                    .ok_or_else(|| fail("an accepted answer lost its check"))?;
                let mut args = values_of(&checked.scrutinee);
                args.push(var(checked.en.clone().unwrap_or_default()));
                Ok(self::term(engine.cite(&sound, &type_arguments, args)?))
            })
        }
        Proof::ConcludeSound {
            conclude,
            accept_sound,
            invariant,
        } => {
            engine.unfolding(&[conclude])?;
            let subject = Engine::last_premise(context)?;
            let before = if *invariant {
                vec![var(Engine::premise(context, 0)?)]
            } else {
                Vec::new()
            };
            let accept_sound = accept_sound.clone();
            engine.auto(state, &subject, &mut |engine, here_state, leaf| {
                let Leaf::Value(values) = leaf else {
                    return Err(fail("a concluded answer reached no value"));
                };
                let accepted = here_state
                    .path
                    .iter()
                    .rev()
                    .find(|taken| taken.constructor == "Some" && taken.en.is_some())
                    .ok_or_else(|| fail("a concluded answer lost its acceptance"))?;
                let mut args = values_of(&accepted.scrutinee);
                args.extend(values);
                args.extend(before.iter().cloned());
                args.push(var(accepted.en.clone().unwrap_or_default()));
                Ok(self::term(engine.own_law(&accept_sound, args)?))
            })
        }
        Proof::ConcludeAccept { conclude } => {
            engine.unfolding(&[conclude])?;
            let subject = Engine::last_premise(context)?;
            engine.auto(state, &subject, &mut |_, here_state, _| {
                // The goal names the acceptance the split generalized; its
                // equation proves it.
                let accepted = here_state
                    .path
                    .iter()
                    .rev()
                    .find(|taken| taken.constructor == "Some" && taken.en.is_some())
                    .ok_or_else(|| fail("a concluded answer lost its acceptance"))?;
                let (left, right, _) = equation(&here_state.goal)?;
                if left == right {
                    return Ok(refl());
                }
                Ok(self::term(var(accepted.en.clone().unwrap_or_default())))
            })
        }
        Proof::VerdictForward {
            verdict,
            saturate,
            conclude_sound,
            saturate_invariant,
        } => {
            engine.unfolding(&[verdict])?;
            let x = engine.parameter(context, 0)?;
            let subject = Engine::last_premise(context)?;
            let mut state = state.clone();
            let mut before = Vec::new();
            if let Some(invariant) = saturate_invariant {
                let (ty, proof) = engine.instance(context, invariant, &[var(x.clone())])?;
                state.have("ll_hj", ty, proof);
                before.push(var("ll_hj"));
            }
            engine.unfold_subject(&mut state, &subject)?;
            let run = engine.own_law(saturate, vec![var(x)])?;
            let run_type = engine.result_type(&run)?;
            let conclude_sound = conclude_sound.clone();
            let proof = engine.generalize(&state, &run, &run_type, &mut |engine, inner| {
                engine.auto(&inner, &subject, &mut |engine, here_state, leaf| {
                    cite_stuck(engine, here_state, &conclude_sound, leaf, &subject, &before)
                })
            })?;
            Ok(self::term(proof))
        }
        Proof::ExplainedForward {
            reasoner,
            run,
            answer,
            run_trace,
            conclude_accept,
            conclude_sound,
            run_invariant,
        } => {
            engine.unfolding(&[reasoner])?;
            let x = engine.parameter(context, 0)?;
            let subject = Engine::last_premise(context)?;
            let mut state = state.clone();
            let (trace_type, trace_proof) =
                engine.instance(context, run_trace, &[var(x.clone())])?;
            state.have("ll_ht", trace_type, trace_proof);
            let mut before = Vec::new();
            if let Some(invariant) = run_invariant {
                let (ty, proof) = engine.instance(context, invariant, &[var(x.clone())])?;
                state.have("ll_hj", ty, proof);
                before.push(var("ll_hj"));
            }
            engine.unfold_subject(&mut state, &subject)?;
            let ran = engine.own_law(run, vec![var(x)])?;
            let run_type = engine.result_type(&ran)?;
            let answer = engine.head(answer)?;
            let conclude_accept = conclude_accept.clone();
            let conclude_sound = conclude_sound.clone();
            let proof = engine.generalize(&state, &ran, &run_type, &mut |engine, inner| {
                engine.auto(&inner, &subject, &mut |engine, here_state, leaf| {
                    explained(
                        engine,
                        here_state,
                        leaf,
                        &answer,
                        &conclude_accept,
                        &conclude_sound,
                        &before,
                    )
                })
            })?;
            Ok(self::term(proof))
        }
        Proof::RunInvariant {
            run_state,
            saturate_invariant,
        } => {
            let x = engine.parameter(context, 0)?;
            let (agree, _) = engine.instance(context, run_state, &[var(x.clone())])?;
            let Some((first, second)) = conjuncts(&agree) else {
                return Err(fail(format!(
                    "a run's agreement is not a conjunction: {}",
                    show(&agree)
                )));
            };
            let (from, to, ty) = equation(&first)?;
            let proof = call(
                "S.Sem.fst",
                vec![
                    first,
                    second,
                    engine.own_law(run_state, vec![var(x.clone())])?,
                ],
            );
            let mut state = state.clone();
            let mut stmts = Vec::new();
            engine.rewrite(&mut state, &mut stmts, &from, &to, proof, &ty);
            Ok(Body {
                stmts,
                tail: Tail::Term(engine.own_law(saturate_invariant, vec![var(x)])?, here()),
            })
        }
        Proof::VerifySound { .. }
        | Proof::TrySound { .. }
        | Proof::TryCount { .. }
        | Proof::VerdictGenerate { .. }
        | Proof::ExplainedGenerate { .. } => {
            super::generate::prove(engine, context, state, &context.theorem.proof)
        }
        Proof::Extend { .. }
        | Proof::SuccessorsFree { .. }
        | Proof::SuccessorsBound { .. }
        | Proof::SearchStep { .. }
        | Proof::SearchPeak { .. }
        | Proof::SearchCount { .. }
        | Proof::SearchGrowth { .. }
        | Proof::ExplainedSearch { .. }
        | Proof::VerdictSearch { .. } => {
            super::search::prove(engine, context, state, &context.theorem.proof)
        }
    }
}

/// A proof term proving `claim`: applied to the theorem's binders and
/// premises, and eta-expanded when the claim is a predicate a citation
/// proves pointwise.
fn proof_term(
    engine: &mut Engine<'_, '_, '_>,
    context: &Context<'_>,
    proof: &ProofTerm,
    claim: &Formula,
    goal: &BTerm,
    hyps: &Hyps,
) -> Result<BTerm, Diagnostic> {
    let mut args: Vec<BTerm> = context
        .values
        .iter()
        .skip(context.theorem.parameters.len())
        .map(|(name, _)| var(name.clone()))
        .collect();
    args.extend(context.premises.iter().map(|p| var(p.clone())));
    let pointwise = match claim {
        Formula::Helper { helper, .. } if matches!(proof, ProofTerm::Theorem { .. }) => {
            match helper {
                Helper::Preserves => 4,
                Helper::Sound | Helper::Complete => 3,
                Helper::Reaches => 2,
                _ => 0,
            }
        }
        _ => 0,
    };
    let names: Vec<String> = (0..pointwise).map(|_| engine.fresh("a")).collect();
    args.extend(names.iter().map(|name| var(name.clone())));
    let mut out = if args.is_empty() {
        engine.proof(context, proof, hyps, Some(goal))?
    } else {
        engine.apply(context, proof, args, hyps, Some(goal))?
    };
    for name in names.into_iter().rev() {
        out = BTerm::Lam(synthetic(name), Box::new(out));
    }
    Ok(out)
}

/// The leaf citing `theorem` at the stuck call's arguments, the subject's
/// right-side payload, `extra`, and the subject equation: `exact thm _ _ _
/// h` after `split at h`.
fn cite_stuck(
    engine: &mut Engine<'_, '_, '_>,
    state: &State,
    theorem: &MemberRef,
    leaf: Leaf,
    subject: &str,
    extra: &[BTerm],
) -> Result<Body, Diagnostic> {
    let Leaf::Opaque(reached) = leaf else {
        return Err(fail("a stuck step reached a value"));
    };
    let (_, right, _) = equation(&state.type_of(subject)?)?;
    let mut args = values_of(&reached);
    args.extend(payload(engine.whnf(&right).term()));
    args.extend(extra.iter().cloned());
    args.push(var(subject.to_owned()));
    Ok(term(engine.own_law(theorem, args)?))
}

/// The last split whose scrutinee was generalized and reached `Some` or
/// `Done`: the step or acceptance the leaf proves from.
fn reached<'s>(
    state: &'s State,
    constructor: &str,
) -> Result<&'s super::engine::Taken, Diagnostic> {
    state
        .path
        .iter()
        .rev()
        .find(|taken| taken.constructor == constructor && taken.en.is_some())
        .ok_or_else(|| {
            fail(format!(
                "a generated proof lost the split reaching `{constructor}`"
            ))
        })
}

/// The step-trace leaf: the step the last split fired extends the trace.
fn step_trace(
    engine: &mut Engine<'_, '_, '_>,
    state: &State,
    follow: &str,
    traced: &str,
    replay_fire: &MemberRef,
) -> Result<Body, Diagnostic> {
    let fired = reached(state, "Some")?.clone();
    let [next] = fired.binders.as_slice() else {
        return Err(fail("a fired step reached no single state"));
    };
    let fire_args = values_of(&fired.scrutinee);
    let [held, step] = fire_args.as_slice() else {
        return Err(fail("a fired step is not `fire s step`"));
    };
    let en = var(fired.en.clone().unwrap_or_default());
    trace_extends(
        engine,
        state,
        follow,
        traced,
        held,
        step,
        &var(next.clone()),
        en,
        replay_fire,
    )
}

/// `follow x (trace ++ [step]) == ok t` from the trace hypothesis `follow
/// x trace == ok s` and the step's equation `fire s step == some t`, by
/// `foldSnoc`, the hypothesis, and `replay_fire`.
#[allow(clippy::too_many_arguments)]
pub(super) fn trace_extends(
    engine: &mut Engine<'_, '_, '_>,
    state: &State,
    follow: &str,
    traced: &str,
    held: &BTerm,
    step: &BTerm,
    next: &BTerm,
    fired_en: BTerm,
    replay_fire: &MemberRef,
) -> Result<Body, Diagnostic> {
    let (followed, done, result_type) = equation(&state.type_of(traced)?)?;
    let BTerm::Call(_, follow_args) = &followed else {
        return Err(fail("a trace hypothesis is not `follow x trace`"));
    };
    let trace = values_of(&followed)
        .last()
        .cloned()
        .ok_or_else(|| fail("a trace hypothesis lost its trace"))?;
    // `follow x tr` is a fold over `tr`: its pieces, read off the
    // definition at a fresh trace.
    let marker = var("\u{0}trace");
    let mut probe_args = follow_args.clone();
    if let Some(last) = probe_args.last_mut() {
        *last = marker.clone();
    }
    engine.unfold.insert(follow.to_owned());
    let folded = engine.whnf(&call(follow, probe_args)).term().clone();
    engine.unfold.remove(follow);
    let BTerm::Call(fold, pieces) = &folded else {
        return Err(fail("`follow` is not a fold"));
    };
    let [element, held_type, env_type, code, env, list, initial] = pieces.as_slice() else {
        return Err(fail("`follow` is not a fold"));
    };
    if fold.text != "S.Sem.listFold" || list != &marker {
        return Err(fail("`follow` is not a fold over its trace"));
    }
    let target = BTerm::Constructor(synthetic("Done"), vec![next.clone()]);
    let mut stmts = Vec::new();
    // `rw [foldSnoc]`: the fold over the extended trace is the step applied
    // to the fold over the trace.
    stmts.push(Stmt::Rewrite {
        proof: call(
            "RS.foldSnoc",
            vec![
                element.clone(),
                held_type.clone(),
                env_type.clone(),
                code.clone(),
                env.clone(),
                trace.clone(),
                step.clone(),
                initial.clone(),
            ],
        ),
        motive: BTerm::Equal(
            Box::new(BTerm::Hole),
            Box::new(target.clone()),
            Box::new(result_type.clone()),
        ),
        source: here(),
    });
    // `rw [llH]`: the fold over the trace is the held state.
    let code_at = |acc: BTerm| {
        super::lemmas::apply_code(
            match code {
                BTerm::Template(inner) => inner,
                other => other,
            },
            vec![env.clone(), acc, step.clone()],
        )
    };
    stmts.push(Stmt::Rewrite {
        proof: call(
            "L.Lean.Eq.symm",
            vec![
                result_type.clone(),
                followed.clone(),
                done.clone(),
                var(traced.to_owned()),
            ],
        ),
        motive: BTerm::Equal(
            Box::new(code_at(BTerm::Hole)),
            Box::new(target),
            Box::new(result_type),
        ),
        source: here(),
    });
    let proof = engine.own_law(
        replay_fire,
        vec![held.clone(), step.clone(), next.clone(), fired_en],
    )?;
    Ok(Body {
        stmts,
        tail: Tail::Term(proof, here()),
    })
}

/// The explained-answer leaf: the answer replays (`answer` over the run's
/// trace is the accepted answer, by the trace hypothesis and
/// `conclude_accept`) and is sound (`conclude_sound`).
fn explained(
    engine: &mut Engine<'_, '_, '_>,
    state: &State,
    leaf: Leaf,
    answer: &str,
    conclude_accept: &MemberRef,
    conclude_sound: &MemberRef,
    extra: &[BTerm],
) -> Result<Body, Diagnostic> {
    let Leaf::Value(_) = leaf else {
        return Err(fail("an explained answer reached no value"));
    };
    let concluded = reached(state, "Done")?.clone();
    let [answered] = concluded.binders.as_slice() else {
        return Err(fail("a concluded answer is not one value"));
    };
    let mut args = values_of(&concluded.scrutinee);
    args.push(var(answered.clone()));
    let en = var(concluded.en.clone().unwrap_or_default());
    let Some((replays, _)) = conjuncts(&state.goal) else {
        return Err(fail(format!(
            "an explained answer's goal is not a pair: {}",
            show(&state.goal)
        )));
    };
    let replays = &replays;
    // The replay part: unfold `answer` to the match on `follow`, rewrite
    // `follow` by the trace hypothesis, and conclude.
    let (left, right, ty) = equation(replays)?;
    engine.unfold.insert(answer.to_owned());
    let unfolded = engine.whnf(&left);
    engine.unfold.remove(answer);
    let Whnf::Stuck {
        term: stuck,
        scrutinee,
        ..
    } = unfolded
    else {
        return Err(fail("an answer does not match on its replay"));
    };
    let (followed, done, result_type) = equation(&state.type_of("ll_ht")?)?;
    if scrutinee != followed {
        return Err(fail("an answer replays another trace than the run's"));
    }
    let mut sub = state.clone();
    sub.goal = BTerm::Equal(Box::new(stuck), Box::new(right), Box::new(ty));
    let mut stmts = Vec::new();
    engine.rewrite(
        &mut sub,
        &mut stmts,
        &followed,
        &done,
        var("ll_ht"),
        &result_type,
    );
    let mut accept_args = args.clone();
    accept_args.push(en.clone());
    let accepted = engine.own_law(conclude_accept, accept_args)?;
    let replay = engine.detached(
        "answer",
        state,
        replays.clone(),
        Body {
            stmts,
            tail: Tail::Term(accepted, here()),
        },
    );
    let mut sound_args = args;
    sound_args.extend(extra.iter().cloned());
    sound_args.push(en);
    let sound = engine.own_law(conclude_sound, sound_args)?;
    Ok(term(BTerm::Pair(Box::new(replay), Box::new(sound))))
}
