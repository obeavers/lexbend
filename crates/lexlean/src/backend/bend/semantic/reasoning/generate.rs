//! The generate-and-verify templates: the Bend counterparts of the Lean
//! scripts that prove a generate-and-verify reasoner's candidates sound,
//! its trial count bounded, and its verdicts and explanations correct.

use super::engine::{conjuncts, show, values_of, Engine, Leaf, State, Whnf};
use super::templates::{arrow, equation};
use super::Context;
use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Tail};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::reasoning::Proof;

use super::super::{call, here, synthetic, var};

fn term(proof: BTerm) -> Body {
    Body::term(proof, here())
}

/// The proof of `found_accepted` at a hit: the hypothesis applied to the
/// hit and its equation.
fn accepted_at(hypothesis: &str, hit: &BTerm, en: &str) -> BTerm {
    BTerm::Call(synthetic(hypothesis), vec![hit.clone(), var(en)])
}

#[allow(clippy::too_many_lines)]
pub(super) fn prove(
    engine: &mut Engine<'_, '_, '_>,
    context: &Context<'_>,
    state: &State,
    proof: &Proof,
) -> Result<Body, Diagnostic> {
    match proof {
        Proof::VerifySound {
            verify,
            sound,
            type_arguments,
        } => {
            engine.unfolding(&[verify])?;
            let subject = Engine::last_premise(context)?;
            let verify = engine.head(verify)?;
            let sound = sound.clone();
            let type_arguments = type_arguments.clone();
            engine.auto(state, &subject, &mut |engine, here_state, _| {
                let checked = here_state
                    .path
                    .last()
                    .filter(|taken| taken.constructor == "True")
                    .cloned()
                    .ok_or_else(|| fail("a verified candidate lost its check"))?;
                let en = checked.en.clone().unwrap_or_default();
                let Some((verifies, _)) = conjuncts(&here_state.goal) else {
                    return Err(fail(format!(
                        "an accepted candidate's goal is not a pair: {}",
                        show(&here_state.goal)
                    )));
                };
                // It verifies again: `verify` is the check it passed.
                let (left, right, ty) = equation(&verifies)?;
                engine.unfold.insert(verify.clone());
                let unfolded = engine.whnf(&left);
                let Whnf::Stuck { term: stuck, .. } = unfolded else {
                    return Err(fail("a verification is not a check"));
                };
                let mut sub = here_state.clone();
                sub.goal = BTerm::Equal(Box::new(stuck), Box::new(right), Box::new(ty));
                let mut stmts = Vec::new();
                engine.rewrite(
                    &mut sub,
                    &mut stmts,
                    &checked.scrutinee,
                    &BTerm::Constructor(synthetic("True"), Vec::new()),
                    var(en.clone()),
                    &var("Bool"),
                );
                let again = engine.detached(
                    "verified",
                    here_state,
                    verifies.clone(),
                    Body {
                        stmts,
                        tail: Tail::Term(BTerm::Refl, here()),
                    },
                );
                let mut args = values_of(&checked.scrutinee);
                args.push(var(en));
                let sound = engine.cite(&sound, &type_arguments, args)?;
                Ok(term(BTerm::Pair(Box::new(again), Box::new(sound))))
            })
        }
        Proof::TrySound {
            attempt,
            verify_sound,
        } => {
            engine.unfolding(&[attempt])?;
            let held = Engine::last_premise(context)?;
            let mut state = state.clone();
            let bound = engine.intro(&mut state, 2)?;
            let [(v, _), (e, _)] = bound.as_slice() else {
                return Err(fail("a trial's claim lost its binders"));
            };
            let verify_sound = verify_sound.clone();
            let held_name = held.clone();
            let v_name = v.clone();
            let body = engine.auto(&state, e, &mut |engine, here_state, leaf| {
                let checked = here_state
                    .path
                    .last()
                    .is_some_and(|taken| taken.constructor == "True");
                match leaf {
                    // The trial had found its answer already: the hypothesis.
                    Leaf::Opaque(_) if !checked => Ok(term(BTerm::Call(
                        synthetic(held_name.clone()),
                        vec![var(v_name.clone()), var(e.clone())],
                    ))),
                    // It checked the candidate: the verification's law.
                    Leaf::Opaque(reached) => {
                        let mut args = values_of(&reached);
                        args.push(var(v_name.clone()));
                        args.push(var(e.clone()));
                        Ok(term(engine.own_law(&verify_sound, args)?))
                    }
                    Leaf::Value(_) => Err(fail("a trial's answer reached no check")),
                }
            })?;
            let mut out = super::engine::block(body);
            for (name, value) in bound.iter().rev() {
                let binder = if *value {
                    format!("+{name}")
                } else {
                    name.clone()
                };
                out = BTerm::Lam(synthetic(binder), Box::new(out));
            }
            Ok(term(out))
        }
        Proof::TryCount { attempt } => {
            engine.unfolding(&[attempt])?;
            let held = Engine::last_premise(context)?;
            let x = engine.parameter(context, 0)?;
            let trial = engine.parameter(context, 1)?;
            let candidate = engine.parameter(context, 2)?;
            let tried = engine.own_law(attempt, vec![var(x), var(trial), var(candidate)])?;
            engine.auto_term(
                state,
                &tried,
                &mut |_, here_state| match here_state.path.last() {
                    Some(taken) if taken.constructor == "True" => {
                        let mut args = values_of(&taken.scrutinee);
                        args.push(var(taken.en.clone().unwrap_or_default()));
                        Ok(term(call("R.LexLeanReasoning.bltSucc", args)))
                    }
                    _ => Ok(term(var(held.clone()))),
                },
            )
        }
        Proof::VerdictGenerate {
            verdict,
            run,
            run_sound,
        } => {
            engine.unfolding(&[verdict])?;
            let x = engine.parameter(context, 0)?;
            let subject = Engine::last_premise(context)?;
            let mut state = state.clone();
            engine.have_theorem(context, &mut state, "ll_hs", run_sound, &[var(x.clone())])?;
            engine.unfold_subject(&mut state, &subject)?;
            let ran = engine.own_law(run, vec![var(x)])?;
            let run_type = engine.result_type(&ran)?;
            let proof = engine.generalize(&state, &ran, &run_type, &mut |engine, inner| {
                engine.auto(&inner, &subject, &mut |_, here_state, leaf| {
                    let Leaf::Value(values) = leaf else {
                        return Err(fail("a verdict reached no answer"));
                    };
                    let [hit] = values.as_slice() else {
                        return Err(fail("a verdict's answer is not one value"));
                    };
                    let found = here_state
                        .path
                        .iter()
                        .rev()
                        .find(|taken| taken.constructor == "Some" && taken.en.is_some())
                        .ok_or_else(|| fail("a verdict lost its found answer"))?;
                    let accepted = accepted_type(here_state, "ll_hs", hit)?;
                    let Some((first, second)) = conjuncts(&accepted) else {
                        return Err(fail("an accepted answer is not a pair"));
                    };
                    Ok(term(call(
                        "S.Sem.snd",
                        vec![
                            first,
                            second,
                            accepted_at("ll_hs", hit, found.en.as_deref().unwrap_or_default()),
                        ],
                    )))
                })
            })?;
            Ok(term(proof))
        }
        Proof::ExplainedGenerate {
            reasoner,
            run,
            run_sound,
            ..
        } => {
            engine.unfolding(&[reasoner])?;
            let x = engine.parameter(context, 0)?;
            let subject = Engine::last_premise(context)?;
            let mut state = state.clone();
            engine.have_theorem(context, &mut state, "ll_hs", run_sound, &[var(x.clone())])?;
            engine.unfold_subject(&mut state, &subject)?;
            let ran = engine.own_law(run, vec![var(x)])?;
            let run_type = engine.result_type(&ran)?;
            let proof = engine.generalize(&state, &ran, &run_type, &mut |engine, inner| {
                engine.auto(&inner, &subject, &mut |_, here_state, leaf| {
                    let Leaf::Value(_) = leaf else {
                        return Err(fail("an explanation reached no answer"));
                    };
                    let found = here_state
                        .path
                        .iter()
                        .rev()
                        .find(|taken| taken.constructor == "Some" && taken.en.is_some())
                        .ok_or_else(|| fail("an explanation lost its found answer"))?;
                    let [hit] = found.binders.as_slice() else {
                        return Err(fail("a found answer is not one value"));
                    };
                    // The replayed trace verifies the hit again, which is the
                    // first half of its acceptance.
                    Ok(term(accepted_at(
                        "ll_hs",
                        &var(hit.clone()),
                        found.en.as_deref().unwrap_or_default(),
                    )))
                })
            })?;
            Ok(term(proof))
        }
        other => Err(fail(format!(
            "`{}` is not a generate-and-verify template",
            other.template()
        ))),
    }
}

/// The acceptance `ll_hs` promises at `hit`: its statement is `@v -> found
/// == Some{v} -> accepted(v)`.
fn accepted_type(state: &State, hypothesis: &str, hit: &BTerm) -> Result<BTerm, Diagnostic> {
    let ty = state.type_of(hypothesis)?;
    let (binder, _, rest) = arrow(&ty)?;
    let (_, _, accepted) = arrow(&rest)?;
    Ok(match binder {
        Some(binder) => super::engine::subst(&accepted, &super::one(&binder, hit.clone())),
        None => accepted,
    })
}
