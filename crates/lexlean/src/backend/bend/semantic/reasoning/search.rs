//! The search templates: the Bend counterparts of the Lean scripts that
//! prove a search reasoner's successors replay, its frontier invariant and
//! bounds, and its verdicts and explanations correct.

use super::engine::{conjuncts, show, values_of, Engine, State, Whnf};
use super::templates::equation;
use super::Context;
use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Tail};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::reasoning::Proof;
use crate::ir::semantic::MemberRef;

use super::super::{call, here, synthetic, var};

fn term(proof: BTerm) -> Body {
    Body::term(proof, here())
}

/// A list's head and tail, when it is a cons.
fn cons_parts(list: &BTerm) -> Option<(BTerm, BTerm)> {
    match list {
        BTerm::Constructor(name, args) if name.text == "Con" && args.len() == 2 => {
            Some((args[0].clone(), args[1].clone()))
        }
        _ => None,
    }
}

/// The arguments of a call headed `head`.
fn call_args<'t>(term: &'t BTerm, head: &str) -> Result<&'t [BTerm], Diagnostic> {
    match term {
        BTerm::Call(name, args) if name.text == head => Ok(args),
        other => Err(fail(format!(
            "a search proof expected `{head}`, not {}",
            show(other)
        ))),
    }
}

impl Engine<'_, '_, '_> {
    /// Prove `goal` from the halves of `pair : ty` (a conjunction a
    /// definition can match on), in a definition binding every entry of
    /// `state` but `exclude`; `body` proves the goal from the halves' names.
    #[allow(clippy::too_many_arguments)]
    fn destructure(
        &mut self,
        state: &State,
        exclude: &[String],
        ty: BTerm,
        pair: BTerm,
        goal: BTerm,
        body: &mut dyn FnMut(&mut Self, &str, &str) -> Result<Body, Diagnostic>,
    ) -> Result<BTerm, Diagnostic> {
        let name = self.below("pair");
        let first = self.fresh("hp");
        let second = self.fresh("hr");
        let proved = body(self, &first, &second)?;
        let mut params = self.template_params();
        let mut args = self.templates();
        for entry in &state.entries {
            if exclude.contains(&entry.name) {
                continue;
            }
            params.push(crate::backend::bend::syntax::Param {
                quantity: self.quantity(entry),
                name: synthetic(entry.name.clone()),
                ty: entry.ty.clone(),
                source: here(),
            });
            args.push(
                state
                    .given
                    .get(&entry.name)
                    .cloned()
                    .unwrap_or_else(|| var(entry.name.clone())),
            );
        }
        let pair_name = self.fresh("pair");
        params.push(super::lemmas::affine(&pair_name, ty));
        args.push(pair);
        self.push(crate::backend::bend::syntax::Item::Def {
            name: synthetic(name.clone()),
            params,
            result: goal,
            result_source: here(),
            body: Body {
                stmts: Vec::new(),
                tail: Tail::Match {
                    scrutinee: synthetic(pair_name),
                    cases: vec![(
                        crate::backend::bend::syntax::Pattern::Pair(
                            synthetic(first),
                            synthetic(second),
                        ),
                        proved,
                    )],
                    source: here(),
                },
            },
            source: here(),
        });
        Ok(call(name, args))
    }

    /// `foldInvariant` at `P(env, acc) = replays env -> All ok acc` over a
    /// successor fold, whose environment is the parent node: a step keeps
    /// its accumulator or appends one fired successor, and `extended`
    /// proves that successor replays from the branch's state, the node, and
    /// the name of the parent's replay. The theorem's parameters ride in
    /// the invariant's captured environment.
    #[allow(clippy::too_many_arguments, clippy::type_complexity)]
    fn fold_nodes(
        &mut self,
        context: &Context<'_>,
        fold: &super::folds::Fold,
        node: &BTerm,
        ok: &BTerm,
        replays: &BTerm,
        parent: &str,
        unfold: &[&MemberRef],
        extended: &mut dyn FnMut(
            &mut Self,
            &State,
            &Projections,
            &str,
        ) -> Result<BTerm, Diagnostic>,
    ) -> Result<BTerm, Diagnostic> {
        let (k_type, k, mut projections) =
            super::projections(self.lower, context, Some(parent), &var("ll_k"));
        projections.insert(parent.to_owned(), var("ll_e"));
        let replayed = super::engine::subst(replays, &projections);
        let theorem_ok = ok.clone();
        let ok = &super::engine::subst(ok, &projections);
        let motive = |held: BTerm| BTerm::Pi {
            name: Some(synthetic("+ll_h")),
            erased: false,
            domain: Box::new(replayed.clone()),
            codomain: Box::new(super::folds::all(node, ok, held)),
        };
        let (inv, inv_arg) = self.define(
            "inv",
            vec![
                super::lemmas::reusable("ll_k", k_type.clone()),
                super::lemmas::reusable("ll_e", fold.env_type.clone()),
                super::lemmas::reusable("ll_s", fold.held.clone()),
            ],
            BTerm::Kind("Type"),
            Body::term(motive(var("ll_s")), here()),
        );
        let named = |engine: &Self, held: BTerm| {
            let mut all = engine.templates();
            all.extend([var("ll_k"), var("ll_e"), held]);
            call(inv.clone(), all)
        };
        let stepped =
            super::lemmas::apply_code(&fold.code, vec![var("ll_e"), var("ll_s"), var("ll_a")]);
        let mut state = State::new(super::folds::all(node, ok, stepped.clone()));
        state.push_value("ll_e", fold.env_type.clone());
        state.push_value("ll_k", k_type.clone());
        state.push_value("ll_s", fold.held.clone());
        state.push_value("ll_a", fold.element.clone());
        state.push_hypothesis("ll_p", named(self, var("ll_s")));
        state.push_value("ll_h", replayed.clone());
        let previous = BTerm::Apply(Box::new(var("ll_p")), vec![var("ll_h")]);
        let saved = std::mem::take(&mut self.unfold);
        let unfolded = self.unfolding(unfold);
        let proof = unfolded.and_then(|()| {
            self.auto_term(&state, &stepped, &mut |engine, here_state| {
                let [_, _, list] = call_args(&here_state.goal, "R.LexLeanReasoning.All")? else {
                    return Err(fail("a successor fold's goal is not `All`"));
                };
                let reached = engine.whnf(list).term().clone();
                if reached == var("ll_s") {
                    return Ok(term(previous.clone()));
                }
                let appended = call_args(&reached, "R.LexLeanRuntime.append.List")?;
                let (added, _) = appended
                    .get(2)
                    .and_then(cons_parts)
                    .ok_or_else(|| fail("a successor fold appends no single node"))?;
                let single = BTerm::Constructor(
                    synthetic("Con"),
                    vec![
                        added.clone(),
                        BTerm::Constructor(synthetic("Nil"), Vec::new()),
                    ],
                );
                let fresh = extended(engine, here_state, &projections, "ll_h")?;
                Ok(term(super::folds::all_append(
                    node,
                    ok,
                    var("ll_s"),
                    single,
                    previous.clone(),
                    super::folds::all_single(node, ok, added, fresh),
                )))
            })
        });
        self.unfold = saved;
        let proof = proof?;
        let (_, hyp_arg) = self.define(
            "hyp",
            vec![
                super::lemmas::reusable("ll_e", fold.env_type.clone()),
                super::lemmas::reusable("ll_k", k_type.clone()),
                super::lemmas::reusable("ll_s", fold.held.clone()),
                super::lemmas::reusable("ll_a", fold.element.clone()),
                super::lemmas::affine("ll_p", named(self, var("ll_s"))),
                super::lemmas::reusable("ll_h", replayed.clone()),
            ],
            super::folds::all(node, ok, stepped),
            proof,
        );
        let start = BTerm::Lam(
            synthetic("+ll_h"),
            Box::new(call(
                "R.LexLeanReasoning.All.nil",
                vec![node.clone(), theorem_ok],
            )),
        );
        let mut args = fold.templates();
        args.extend([
            super::lemmas::template(k_type),
            inv_arg,
            hyp_arg,
            fold.env.clone(),
            k,
            fold.values.clone(),
            fold.initial.clone(),
            start,
        ]);
        Ok(call("RS.foldInvariant", args))
    }
}

/// Each theorem parameter's term below a definition that captures them.
type Projections = std::collections::BTreeMap<String, BTerm>;

/// The halves of `SearchOk(N, A, ok, accept, frontier, found)`.
fn search_halves(search_ok: &BTerm) -> Result<(BTerm, BTerm), Diagnostic> {
    let [node, answer, ok, accept, frontier, found] = call_args(search_ok, "RS.SearchOk")? else {
        return Err(fail("a search invariant is not `SearchOk`"));
    };
    Ok((
        super::folds::all(node, ok, frontier.clone()),
        call(
            "RS.Found",
            vec![
                node.clone(),
                answer.clone(),
                ok.clone(),
                accept.clone(),
                found.clone(),
            ],
        ),
    ))
}

#[allow(clippy::too_many_lines)]
pub(super) fn prove(
    engine: &mut Engine<'_, '_, '_>,
    context: &Context<'_>,
    state: &State,
    proof: &Proof,
) -> Result<Body, Diagnostic> {
    match proof {
        Proof::Extend {
            follow,
            replay_fire,
        } => {
            let traced = Engine::premise(context, 0)?;
            let fired = Engine::premise(context, 1)?;
            let next = engine.parameter(context, 3)?;
            let (left, _, _) = equation(&state.type_of(&fired)?)?;
            let [held, step] = &values_of(&left)[..] else {
                return Err(fail("an extended step is not `fire s step`"));
            };
            let follow = engine.head(follow)?;
            let [held, step] = [held.clone(), step.clone()];
            super::templates::trace_extends(
                engine,
                state,
                &follow,
                &traced,
                &held,
                &step,
                &var(next),
                var(fired),
                replay_fire,
            )
        }
        Proof::SuccessorsFree { successors, extend } => {
            engine.unfolding(&[successors])?;
            let x = engine.parameter(context, 0)?;
            let parent = engine.parameter(context, 1)?;
            let replays = Engine::premise(context, 0)?;
            let [node, ok, list] = call_args(&state.goal, "R.LexLeanReasoning.All")? else {
                return Err(fail("a rule's successors claim no `All`"));
            };
            let (node, ok, list) = (node.clone(), ok.clone(), list.clone());
            let extend = extend.clone();
            engine.auto_term(state, &list, &mut |engine, here_state| {
                let Some(fired) = here_state
                    .path
                    .last()
                    .filter(|taken| taken.constructor == "Some")
                    .cloned()
                else {
                    return Ok(term(call(
                        "R.LexLeanReasoning.All.nil",
                        vec![node.clone(), ok.clone()],
                    )));
                };
                let [_, step] = &values_of(&fired.scrutinee)[..] else {
                    return Err(fail("a rule's successor is not `fire s step`"));
                };
                let step = step.clone();
                let [_, _, now] = call_args(&here_state.goal, "R.LexLeanReasoning.All")? else {
                    return Err(fail("a rule's successors claim no `All`"));
                };
                let reached = engine.whnf(now).term().clone();
                let (added, _) = cons_parts(&reached)
                    .ok_or_else(|| fail("a rule's successor list is not one node"))?;
                let next = var(fired.binders.first().cloned().unwrap_or_default());
                let extended = engine.own_law(
                    &extend,
                    vec![
                        var(x.clone()),
                        var(parent.clone()),
                        step,
                        next,
                        var(replays.clone()),
                        var(fired.en.clone().unwrap_or_default()),
                    ],
                )?;
                Ok(term(super::folds::all_single(&node, &ok, added, extended)))
            })
        }
        Proof::SuccessorsBound {
            successors,
            collect,
            extend,
            ..
        } => {
            let x = engine.parameter(context, 0)?;
            let parent = engine.parameter(context, 1)?;
            let replays = Engine::premise(context, 0)?;
            engine.unfolding(&[successors])?;
            let [node, ok, list] = call_args(&state.goal, "R.LexLeanReasoning.All")? else {
                return Err(fail("a rule's successors claim no `All`"));
            };
            let (node, ok, list) = (node.clone(), ok.clone(), list.clone());
            let fold = super::folds::Fold::of(engine, &list)?;
            let replay_type = state.type_of(&replays)?;
            let extend = extend.clone();
            let proof = engine.fold_nodes(
                context,
                &fold,
                &node,
                &ok,
                &replay_type,
                &parent,
                &[collect],
                &mut |engine, here_state, projections, replayed| {
                    // The fired rule is the last firing split on; the
                    // successor it appends is the fold's environment node
                    // extended by it.
                    let fired = here_state
                        .path
                        .iter()
                        .rev()
                        .find(|taken| taken.constructor == "Some" && taken.en.is_some())
                        .cloned()
                        .ok_or_else(|| fail("a successor's firing was not split on"))?;
                    let [_, step] = &values_of(&fired.scrutinee)[..] else {
                        return Err(fail("a rule's successor is not `fire s step`"));
                    };
                    let step = step.clone();
                    engine.own_law(
                        &extend,
                        vec![
                            super::engine::subst(&var(x.clone()), projections),
                            var("ll_e"),
                            step,
                            var(fired.binders.first().cloned().unwrap_or_default()),
                            var(replayed),
                            var(fired.en.clone().unwrap_or_default()),
                        ],
                    )
                },
            )?;
            Ok(term(BTerm::Apply(Box::new(proof), vec![var(replays)])))
        }
        Proof::SearchStep {
            search_step,
            successors_ok,
            fresh_ok,
            ..
        } => {
            engine.unfolding(&[search_step])?;
            let x = engine.parameter(context, 0)?;
            let subject = Engine::premise(context, 0)?;
            let held = Engine::premise(context, 1)?;
            let (all_before, found_before) = search_halves(&state.type_of(&held)?)?;
            let successors_ok = successors_ok.clone();
            let fresh_ok = fresh_ok.clone();
            engine.auto(state, &subject, &mut |engine, here_state, _| {
                let popped = here_state
                    .path
                    .iter()
                    .rev()
                    .find(|taken| taken.constructor == "Con")
                    .cloned()
                    .ok_or_else(|| fail("a search step lost the node it popped"))?;
                let [first, rest] = popped.binders.as_slice() else {
                    return Err(fail("a popped frontier is not a cons"));
                };
                let (first, rest) = (var(first.clone()), var(rest.clone()));
                let accepted = here_state
                    .path
                    .last()
                    .cloned()
                    .ok_or_else(|| fail("a search step lost its acceptance"))?;
                let [node, _, ok, _, _, _] = call_args(&here_state.goal, "RS.SearchOk")? else {
                    return Err(fail("a search step's goal is not `SearchOk`"));
                };
                let (node, ok) = (node.clone(), ok.clone());
                let cons = super::folds::all(
                    &node,
                    &ok,
                    BTerm::Constructor(synthetic("Con"), vec![first.clone(), rest.clone()]),
                );
                // The popped node and the rest keep the invariant: the
                // frontier's equation turns the hypothesis's `All` into one
                // over the cons.
                let cast = engine.detached(
                    "cons",
                    here_state,
                    cons.clone(),
                    Body {
                        stmts: vec![crate::backend::bend::syntax::Stmt::Rewrite {
                            proof: var(popped.en.clone().unwrap_or_default()),
                            motive: super::folds::all(&node, &ok, BTerm::Hole),
                            source: here(),
                        }],
                        tail: Tail::Term(
                            call(
                                "RS.andLeft",
                                vec![all_before.clone(), found_before.clone(), var(held.clone())],
                            ),
                            here(),
                        ),
                    },
                );
                let goal = here_state.goal.clone();
                let exclude = [held.clone()];
                let proof = if accepted.constructor == "Some" {
                    let en = accepted.en.clone().unwrap_or_default();
                    engine.destructure(
                        here_state,
                        &exclude,
                        cons,
                        cast,
                        goal,
                        &mut |_, hp, hr| {
                            Ok(term(BTerm::Pair(
                                Box::new(var(hr)),
                                Box::new(BTerm::Pair(Box::new(var(hp)), Box::new(var(en.clone())))),
                            )))
                        },
                    )?
                } else {
                    let [_, _, _, _, frontier, _] = call_args(&here_state.goal, "RS.SearchOk")?
                    else {
                        return Err(fail("a search step's goal is not `SearchOk`"));
                    };
                    let fold = super::folds::Fold::of(engine, frontier)?;
                    let ordered = call_args(&fold.values, "R.LexLeanRuntime.append.List")?.to_vec();
                    let [_, left, right] = ordered.as_slice() else {
                        return Err(fail("a search step orders no append"));
                    };
                    let (left, right) = (left.clone(), right.clone());
                    let x = x.clone();
                    let successors_ok = successors_ok.clone();
                    let fresh_ok = fresh_ok.clone();
                    let (node2, ok2) = (node.clone(), ok.clone());
                    let first2 = first.clone();
                    engine.destructure(
                        here_state,
                        &exclude,
                        cons,
                        cast,
                        goal,
                        &mut |engine, hp, hr| {
                            let expanded = engine.own_law(
                                &successors_ok,
                                vec![var(x.clone()), first2.clone(), var(hp)],
                            )?;
                            let fresh_side = if left == rest { &right } else { &left };
                            let fresh_proof = match &fresh_ok {
                                Some(fresh_ok) => {
                                    let [_, _, filtered] = call_args(fresh_side, "S.Sem.fst")?
                                    else {
                                        return Err(fail("a fresh frontier is not a projection"));
                                    };
                                    let mut args = vec![var(x.clone())];
                                    args.extend(values_of(filtered));
                                    args.push(expanded);
                                    engine.own_law(fresh_ok, args)?
                                }
                                None => expanded,
                            };
                            let (left_ok, right_ok) = if left == rest {
                                (var(hr), fresh_proof)
                            } else {
                                (fresh_proof, var(hr))
                            };
                            let ordered_ok = super::folds::all_append(
                                &node2,
                                &ok2,
                                left.clone(),
                                right.clone(),
                                left_ok,
                                right_ok,
                            );
                            let capped =
                                engine.cap_all(context, &fold, &node2, &ok2, ordered_ok)?;
                            Ok(term(BTerm::Pair(
                                Box::new(capped),
                                Box::new(BTerm::Constructor(synthetic("Unit"), Vec::new())),
                            )))
                        },
                    )?
                };
                Ok(term(proof))
            })
        }
        Proof::SearchPeak { search_step } => {
            engine.unfolding(&[search_step])?;
            let subject = Engine::premise(context, 0)?;
            let held = Engine::premise(context, 1)?;
            engine.auto(state, &subject, &mut |engine, here_state, _| {
                let accepted = here_state
                    .path
                    .last()
                    .is_some_and(|taken| taken.constructor == "Some");
                if accepted {
                    return Ok(term(var(held.clone())));
                }
                let [peak, bound] = call_args(&here_state.goal, "S.Sem.le")? else {
                    return Err(fail("a frontier bound is not `<=`"));
                };
                let (peak, bound) = (peak.clone(), bound.clone());
                let reached = engine.whnf(&peak);
                let Whnf::Stuck { term: chosen, .. } = reached else {
                    return Err(fail("a search step's peak is no maximum"));
                };
                let [_, larger, length, previous] = call_args(&chosen, "S.Sem.ite")? else {
                    return Err(fail("a search step's peak is no maximum"));
                };
                let (larger, length, previous) = (larger.clone(), length.clone(), previous.clone());
                let [_, next] = call_args(&length, "R.LexLeanRuntime.length.List")? else {
                    return Err(fail("a search step's peak is no length"));
                };
                let fold = super::folds::Fold::of(engine, next)?;
                let capped = engine.cap_bound(&fold)?;
                Ok(term(call(
                    "RS.peakBound",
                    vec![larger, previous, length, bound, var(held.clone()), capped],
                )))
            })
        }
        Proof::SearchCount { search_step } => {
            engine.unfolding(&[search_step])?;
            let subject = Engine::premise(context, 0)?;
            engine.auto(state, &subject, &mut |_, _, _| Ok(term(BTerm::Refl)))
        }
        Proof::SearchGrowth { search_step } => {
            engine.unfolding(&[search_step])?;
            let subject = Engine::premise(context, 0)?;
            engine.auto(state, &subject, &mut |engine, here_state, _| {
                let [counted, bound] = call_args(&here_state.goal, "S.Sem.le")? else {
                    return Err(fail("a growth bound is not `<=`"));
                };
                let (counted, bound) = (counted.clone(), bound.clone());
                let reached = engine.whnf(&counted).term().clone();
                if reached == bound {
                    return Ok(term(call("S.Sem.ble_refl", vec![bound])));
                }
                Ok(term(call("RS.le_succ", vec![reached])))
            })
        }
        Proof::ExplainedSearch {
            reasoner,
            answer,
            search_ok,
            accept_sound,
            follow_invariant,
            ..
        } => {
            engine.unfolding(&[reasoner])?;
            let x = engine.parameter(context, 0)?;
            let subject = Engine::last_premise(context)?;
            let mut state = state.clone();
            engine.have_theorem(context, &mut state, "ll_hs", search_ok, &[var(x.clone())])?;
            let answer = engine.head(answer)?;
            let accept_sound = accept_sound.clone();
            let follow_invariant = follow_invariant.clone();
            // The reasoner matches on the search's found answer; the split
            // on it names the answer and rewrites only the hypothesis, so
            // the invariant still speaks of the search's own field.
            engine.auto(&state, &subject, &mut |engine, here_state, _| {
                let found = here_state
                    .path
                    .iter()
                    .rev()
                    .find(|taken| taken.constructor == "Some" && taken.en.is_some())
                    .cloned()
                    .ok_or_else(|| fail("an explanation lost its found answer"))?;
                let [hit] = found.binders.as_slice() else {
                    return Err(fail("a found answer is not one value"));
                };
                let hit = var(hit.clone());
                let (all_found, found_any) = search_halves(&here_state.type_of("ll_hs")?)?;
                let [node, answer_type, ok, accept, _] = call_args(&found_any, "RS.Found")? else {
                    return Err(fail("a search's found answer is not `Found`"));
                };
                let (node, answer_type, ok, accept) = (
                    node.clone(),
                    answer_type.clone(),
                    ok.clone(),
                    accept.clone(),
                );
                let found_at = |found: BTerm| {
                    call(
                        "RS.Found",
                        vec![
                            node.clone(),
                            answer_type.clone(),
                            ok.clone(),
                            accept.clone(),
                            found,
                        ],
                    )
                };
                let reached = call(
                    "S.Sem.snd",
                    vec![answer_type.clone(), node.clone(), hit.clone()],
                );
                let value = call(
                    "S.Sem.fst",
                    vec![answer_type.clone(), node.clone(), hit.clone()],
                );
                let BTerm::Equal(replayed, done, replay_type) = super::folds::beta(&ok, &reached)
                else {
                    return Err(fail("a search's node invariant is not a replay"));
                };
                let held = match *done {
                    BTerm::Constructor(_, ref payload) if payload.len() == 1 => payload[0].clone(),
                    _ => return Err(fail("a node's replay does not reach its state")),
                };
                let goal = here_state.goal.clone();
                let Some((claimed, _)) = conjuncts(&goal) else {
                    return Err(fail("an explanation's goal is not a pair"));
                };
                let BTerm::Equal(answered, wanted, answer_maybe) = claimed else {
                    return Err(fail("an explanation does not claim its answer"));
                };
                // `Found` at the hit, with its predicates applied: a match
                // on the pair would otherwise meet an unannotated redex.
                let hit_found = BTerm::Product(
                    Box::new(BTerm::Equal(
                        replayed.clone(),
                        done.clone(),
                        replay_type.clone(),
                    )),
                    Box::new(BTerm::Equal(
                        Box::new(super::folds::beta(&accept, &reached)),
                        Box::new(BTerm::Constructor(synthetic("Some"), vec![value.clone()])),
                        answer_maybe.clone(),
                    )),
                );
                let cast = engine.detached(
                    "found",
                    here_state,
                    hit_found.clone(),
                    Body {
                        stmts: vec![crate::backend::bend::syntax::Stmt::Rewrite {
                            proof: var(found.en.clone().unwrap_or_default()),
                            motive: found_at(BTerm::Hole),
                            source: here(),
                        }],
                        tail: Tail::Term(
                            call(
                                "RS.andRight",
                                vec![all_found, found_any.clone(), var("ll_hs")],
                            ),
                            here(),
                        ),
                    },
                );
                let traced = values_of(&replayed)
                    .get(1)
                    .cloned()
                    .ok_or_else(|| fail("a replay names no trace"))?;
                let x = x.clone();
                let answer = answer.clone();
                let accept_sound = accept_sound.clone();
                let follow_invariant = follow_invariant.clone();
                engine
                    .destructure(
                        here_state,
                        &["ll_hs".to_owned()],
                        hit_found,
                        cast,
                        goal.clone(),
                        &mut |engine, hf, ha| {
                            // The answer replays the trace to the node's state,
                            // where the acceptance the search recorded holds.
                            engine.unfold.insert(answer.clone());
                            let unfolded = engine.whnf(&answered);
                            engine.unfold.remove(&answer);
                            let Whnf::Stuck { term: stuck, .. } = unfolded else {
                                return Err(fail("an answer does not match on its replay"));
                            };
                            let mut sub = State::new(BTerm::Equal(
                                Box::new(stuck),
                                wanted.clone(),
                                answer_maybe.clone(),
                            ));
                            let mut stmts = Vec::new();
                            engine.rewrite(
                                &mut sub,
                                &mut stmts,
                                &replayed,
                                &done,
                                var(hf),
                                &replay_type,
                            );
                            let replays = BTerm::Block(Box::new(Body {
                                stmts,
                                tail: Tail::Term(var(ha), here()),
                            }));
                            let mut sound = vec![var(x.clone()), held.clone(), value.clone()];
                            if let Some(invariant) = &follow_invariant {
                                sound.push(engine.own_law(
                                    invariant,
                                    vec![var(x.clone()), traced.clone(), held.clone(), var(hf)],
                                )?);
                            }
                            sound.push(var(ha));
                            let sound = engine.own_law(&accept_sound, sound)?;
                            Ok(Body {
                                stmts: [hf, ha]
                                    .into_iter()
                                    .map(|name| crate::backend::bend::syntax::Stmt::Share {
                                        name: synthetic(name.to_owned()),
                                        value: var(name),
                                        source: here(),
                                    })
                                    .collect(),
                                tail: Tail::Term(
                                    BTerm::Pair(Box::new(replays), Box::new(sound)),
                                    here(),
                                ),
                            })
                        },
                    )
                    .map(term)
            })
        }
        Proof::VerdictSearch {
            verdict, explained, ..
        } => {
            engine.unfolding(&[verdict])?;
            let x = engine.parameter(context, 0)?;
            let subject = Engine::last_premise(context)?;
            let explained = explained.clone();
            engine.auto(state, &subject, &mut |engine, here_state, _| {
                let done = here_state
                    .path
                    .iter()
                    .rev()
                    .find(|taken| taken.constructor == "Done" && taken.en.is_some())
                    .cloned()
                    .ok_or_else(|| fail("a verdict lost its explanation"))?;
                let [pair] = done.binders.as_slice() else {
                    return Err(fail("an explanation is not one value"));
                };
                // The explanation is a pair; splitting it names its halves,
                // which the explained theorem takes.
                let ty = here_state.type_of(pair)?;
                let explained = explained.clone();
                let x = x.clone();
                let en = done.en.clone().unwrap_or_default();
                let proof = engine.split(
                    here_state,
                    &var(pair.clone()),
                    &ty,
                    &mut |engine, halves| {
                        let names = halves
                            .path
                            .last()
                            .map(|taken| taken.binders.clone())
                            .unwrap_or_default();
                        let [value, trace] = names.as_slice() else {
                            return Err(fail("an explanation did not split into a pair"));
                        };
                        let (value, trace) = (var(value.clone()), var(trace.clone()));
                        let (claim, _) = engine.instance(context, &explained, &[var(x.clone())])?;
                        let claim = after_binders(&claim, &[value.clone(), trace.clone()])?;
                        let Some((first, second)) = conjuncts(&claim) else {
                            return Err(fail("an explanation's claim is not a pair"));
                        };
                        let cited = engine.own_law(
                            &explained,
                            vec![var(x.clone()), value, trace, var(en.clone())],
                        )?;
                        Ok(term(second_half(&claim, first, second, cited)))
                    },
                )?;
                Ok(term(proof))
            })
        }
        other => Err(fail(format!(
            "`{}` is not a search template",
            other.template()
        ))),
    }
}

/// The second half of `proof : claim`: a projection when the halves are
/// data, `andRight` when they are propositions.
fn second_half(claim: &BTerm, first: BTerm, second: BTerm, proof: BTerm) -> BTerm {
    if matches!(claim, BTerm::Product(..)) {
        call("RS.andRight", vec![first, second, proof])
    } else {
        call("S.Sem.snd", vec![first, second, proof])
    }
}

/// A claim `@v1 -> ... -> premise -> c` at the values `args`, past its
/// premises: `c`.
fn after_binders(claim: &BTerm, args: &[BTerm]) -> Result<BTerm, Diagnostic> {
    let mut current = claim.clone();
    let mut args = args.iter();
    while let BTerm::Pi { name, codomain, .. } = &current {
        current = match name {
            Some(name) => {
                let arg = args
                    .next()
                    .ok_or_else(|| fail("a claim binds more values than it is given"))?;
                super::engine::subst(
                    codomain,
                    &super::one(&super::engine::bound(&name.text), arg.clone()),
                )
            }
            None => (**codomain).clone(),
        };
    }
    Ok(current)
}
