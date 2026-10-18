//! The lemmas about one fold a search elaborates to: capping the frontier
//! keeps every node it keeps (`capAll`) and keeps at most the bound
//! (`capBound`), and dropping visited nodes keeps every node it keeps
//! (`freshAll`). Lean proves each once over the fold's lambda; here the
//! lambda is the code definition the elaboration named, so each is an
//! instance of `foldInvariant` or `allFold` whose step hypothesis splits
//! the step's one `if`.

use super::engine::{show, values_of, Engine, State};
use super::lemmas::{affine, reusable, template};
use super::Context;
use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Tail};
use crate::diagnostic::Diagnostic;

use super::super::{call, here, synthetic, var};

/// A fold `listFold(~A, ~St, ~E, ~code, env, values, initial)`.
#[derive(Clone)]
pub(super) struct Fold {
    pub element: BTerm,
    pub held: BTerm,
    pub env_type: BTerm,
    pub code: BTerm,
    pub env: BTerm,
    pub values: BTerm,
    pub initial: BTerm,
}

fn untemplate(term: &BTerm) -> BTerm {
    match term {
        BTerm::Template(inner) => (**inner).clone(),
        other => other.clone(),
    }
}

impl Fold {
    /// The fold a term reduces to, looking through a pair projection.
    pub(super) fn of(engine: &mut Engine<'_, '_, '_>, term: &BTerm) -> Result<Self, Diagnostic> {
        let saved = engine.unfold_all;
        engine.unfold_all = true;
        let mut reduced = engine.whnf(term).term().clone();
        if let BTerm::Call(head, args) = &reduced {
            if (head.text == "S.Sem.fst" || head.text == "S.Sem.snd") && args.len() == 3 {
                reduced = engine.whnf(&args[2]).term().clone();
            }
        }
        engine.unfold_all = saved;
        match &reduced {
            BTerm::Call(head, args) if head.text == "S.Sem.listFold" && args.len() == 7 => {
                Ok(Self {
                    element: untemplate(&args[0]),
                    held: untemplate(&args[1]),
                    env_type: untemplate(&args[2]),
                    code: untemplate(&args[3]),
                    env: args[4].clone(),
                    values: args[5].clone(),
                    initial: args[6].clone(),
                })
            }
            other => Err(fail(format!(
                "a search lemma expected a fold, not {}",
                show(other)
            ))),
        }
    }

    /// The step applied.
    fn step(&self, env: BTerm, held: BTerm, element: BTerm) -> BTerm {
        super::lemmas::apply_code(&self.code, vec![env, held, element])
    }

    /// The fold's template arguments.
    pub(super) fn templates(&self) -> Vec<BTerm> {
        vec![
            template(self.element.clone()),
            template(self.held.clone()),
            template(self.env_type.clone()),
            template(self.code.clone()),
        ]
    }
}

/// A lambda applied to an argument.
pub(super) fn beta(function: &BTerm, argument: &BTerm) -> BTerm {
    match function {
        BTerm::Lam(binder, body) => super::engine::subst(
            body,
            &super::one(&super::engine::bound(&binder.text), argument.clone()),
        ),
        other => BTerm::Apply(Box::new(other.clone()), vec![argument.clone()]),
    }
}

/// `All(N, ok, list)`.
pub(super) fn all(node: &BTerm, ok: &BTerm, list: BTerm) -> BTerm {
    call(
        "R.LexLeanReasoning.All",
        vec![node.clone(), ok.clone(), list],
    )
}

/// `allAppend(N, ok, xs, ys, hx, hy)`.
pub(super) fn all_append(
    node: &BTerm,
    ok: &BTerm,
    xs: BTerm,
    ys: BTerm,
    hx: BTerm,
    hy: BTerm,
) -> BTerm {
    call(
        "R.LexLeanReasoning.allAppend",
        vec![node.clone(), ok.clone(), xs, ys, hx, hy],
    )
}

/// `allSingle(N, ok, a, h)`.
pub(super) fn all_single(node: &BTerm, ok: &BTerm, a: BTerm, h: BTerm) -> BTerm {
    call(
        "R.LexLeanReasoning.allSingle",
        vec![node.clone(), ok.clone(), a, h],
    )
}

/// The one-element list `[a]`.
fn single(a: BTerm) -> BTerm {
    BTerm::Constructor(
        super::super::synthetic("Con"),
        vec![
            a,
            BTerm::Constructor(super::super::synthetic("Nil"), Vec::new()),
        ],
    )
}

/// What one fold step's branch has to prove with: whether the step's `if`
/// held there.
pub(super) struct Branch {
    pub held: bool,
}

impl Engine<'_, '_, '_> {
    /// Every element `ok` holds of survives the fold: `allFold` at `P(acc)
    /// = All ok (project acc)` and `Q(a) = ok a`, the step proved per
    /// branch of its `if` by `branch` (given `ok` as the step's definitions
    /// state it, the step's state, and its element; the proofs of `Q` and
    /// `P` are `ll_q` and `ll_p`).
    #[allow(
        clippy::too_many_arguments,
        clippy::too_many_lines,
        clippy::type_complexity
    )]
    pub(super) fn fold_all(
        &mut self,
        context: &Context<'_>,
        fold: &Fold,
        node: &BTerm,
        ok: &BTerm,
        project: &dyn Fn(BTerm) -> BTerm,
        values_ok: BTerm,
        branch: &mut dyn FnMut(
            &mut Self,
            Branch,
            &BTerm,
            &BTerm,
            &BTerm,
        ) -> Result<BTerm, Diagnostic>,
    ) -> Result<BTerm, Diagnostic> {
        let (k_type, k, projections) = super::projections(self.lower, context, None, &var("ll_k"));
        let theorem_ok = ok.clone();
        let ok = &super::engine::subst(ok, &projections);
        let (inv, inv_arg) = self.define(
            "inv",
            vec![
                reusable("ll_k", k_type.clone()),
                reusable("ll_s", fold.held.clone()),
            ],
            BTerm::Kind("Type"),
            Body::term(all(node, ok, project(var("ll_s"))), here()),
        );
        let (q, q_arg) = self.define(
            "q",
            vec![
                reusable("ll_k", k_type.clone()),
                reusable("ll_a", fold.element.clone()),
            ],
            BTerm::Kind("Type"),
            Body::term(beta(ok, &var("ll_a")), here()),
        );
        let named = |engine: &Self, head: &str, arg: BTerm| {
            let mut all = engine.templates();
            all.push(var("ll_k"));
            all.push(arg);
            call(head.to_owned(), all)
        };
        let stepped = fold.step(var("ll_e"), var("ll_s"), var("ll_a"));
        let mut state = State::new(all(node, ok, project(stepped.clone())));
        state.push_value("ll_e", fold.env_type.clone());
        state.push_value("ll_k", k_type.clone());
        state.push_value("ll_s", fold.held.clone());
        state.push_value("ll_a", fold.element.clone());
        state.push_hypothesis("ll_q", named(self, &q, var("ll_a")));
        state.push_hypothesis("ll_p", named(self, &inv, var("ll_s")));
        let proof = self.auto_term(&state, &stepped, &mut |engine, here_state| {
            let held = here_state
                .path
                .last()
                .is_some_and(|taken| taken.constructor == "True");
            let proof = branch(engine, Branch { held }, ok, &var("ll_s"), &var("ll_a"))?;
            Ok(Body::term(proof, here()))
        })?;
        let result = named(self, &inv, stepped.clone());
        let (_, hyp_arg) = self.define(
            "hyp",
            vec![
                reusable("ll_e", fold.env_type.clone()),
                reusable("ll_k", k_type.clone()),
                reusable("ll_s", fold.held.clone()),
                reusable("ll_a", fold.element.clone()),
                affine("ll_q", named(self, &q, var("ll_a"))),
                affine("ll_p", named(self, &inv, var("ll_s"))),
            ],
            result,
            proof,
        );
        let mut args = fold.templates();
        args.extend([template(k_type), inv_arg, q_arg, hyp_arg]);
        args.extend([
            fold.env.clone(),
            k,
            fold.values.clone(),
            fold.initial.clone(),
            values_ok,
            call("R.LexLeanReasoning.All.nil", vec![node.clone(), theorem_ok]),
        ]);
        Ok(call("RS.allFold", args))
    }

    /// `capAll`: the capped frontier keeps only nodes `ok` holds of.
    pub(super) fn cap_all(
        &mut self,
        context: &Context<'_>,
        fold: &Fold,
        node: &BTerm,
        ok: &BTerm,
        values_ok: BTerm,
    ) -> Result<BTerm, Diagnostic> {
        let node_type = node.clone();
        self.fold_all(
            context,
            fold,
            node,
            ok,
            &|acc| acc,
            values_ok,
            &mut |_, branch, okay, acc, element| {
                if !branch.held {
                    return Ok(var("ll_p"));
                }
                Ok(all_append(
                    &node_type,
                    okay,
                    acc.clone(),
                    single(element.clone()),
                    var("ll_p"),
                    all_single(&node_type, okay, element.clone(), var("ll_q")),
                ))
            },
        )
    }

    /// `freshAll`: dropping visited nodes keeps only nodes `ok` holds of.
    pub(super) fn fresh_all(
        &mut self,
        context: &Context<'_>,
        fold: &Fold,
        node: &BTerm,
        ok: &BTerm,
        values_ok: BTerm,
    ) -> Result<BTerm, Diagnostic> {
        let (first_type, second_type) = super::engine::conjuncts(&fold.held)
            .ok_or_else(|| fail("a fresh fold does not hold a pair"))?;
        let project = |acc: BTerm| {
            call(
                "S.Sem.fst",
                vec![first_type.clone(), second_type.clone(), acc],
            )
        };
        let node_type = node.clone();
        let first = project;
        self.fold_all(
            context,
            fold,
            node,
            ok,
            &project,
            values_ok,
            &mut |_, branch, okay, acc, element| {
                // The step keeps the accumulator when the node was visited.
                if branch.held {
                    return Ok(var("ll_p"));
                }
                Ok(all_append(
                    &node_type,
                    okay,
                    first(acc.clone()),
                    single(element.clone()),
                    var("ll_p"),
                    all_single(&node_type, okay, element.clone(), var("ll_q")),
                ))
            },
        )
    }

    /// `capBound`: the capped frontier is at most the bound long, by
    /// `foldInvariant` at `length acc <= bound`, the bound read off the step's
    /// guard `length acc < bound` over its environment.
    pub(super) fn cap_bound(&mut self, fold: &Fold) -> Result<BTerm, Diagnostic> {
        let element = fold.element.clone();
        let length =
            |list: BTerm| call("R.LexLeanRuntime.length.List", vec![element.clone(), list]);
        let le = |a: BTerm, b: BTerm| call("S.Sem.le", vec![a, b]);
        let stepped = fold.step(var("ll_e"), var("ll_s"), var("ll_a"));
        let saved = self.unfold_all;
        self.unfold_all = true;
        let guard = self.whnf(&stepped);
        self.unfold_all = saved;
        let super::engine::Whnf::Stuck { scrutinee, .. } = guard else {
            return Err(fail("a frontier cap does not test its length"));
        };
        let bound = match values_of(&scrutinee).as_slice() {
            [_, bound] => bound.clone(),
            _ => return Err(fail(format!("a frontier cap tests {}", show(&scrutinee)))),
        };
        let (inv, inv_arg) = self.define(
            "inv",
            vec![
                reusable("ll_k", var("Unit")),
                reusable("ll_e", fold.env_type.clone()),
                reusable("ll_s", fold.held.clone()),
            ],
            BTerm::Kind("Type"),
            Body::term(le(length(var("ll_s")), bound.clone()), here()),
        );
        let named = |engine: &Self, held: BTerm| {
            let mut all = engine.templates();
            all.push(var("ll_k"));
            all.push(var("ll_e"));
            all.push(held);
            call(inv.clone(), all)
        };
        let mut state = State::new(le(length(stepped.clone()), bound.clone()));
        state.push_value("ll_e", fold.env_type.clone());
        state.push_value("ll_k", var("Unit"));
        state.push_value("ll_s", fold.held.clone());
        state.push_value("ll_a", fold.element.clone());
        state.push_hypothesis("ll_p", named(self, var("ll_s")));
        let saved = self.unfold_all;
        self.unfold_all = true;
        let proof = self.auto_term(&state, &stepped, &mut |_, here_state| {
            let Some(taken) = here_state
                .path
                .last()
                .filter(|taken| taken.constructor == "True")
            else {
                return Ok(Body::term(var("ll_p"), here()));
            };
            // `length (acc ++ [a]) = length acc + 1`, and the guard held.
            let extended = length(call(
                "R.LexLeanRuntime.append.List",
                vec![element.clone(), var("ll_s"), single(var("ll_a"))],
            ));
            let sum = call(
                "L.Lean.Nat.add",
                vec![length(var("ll_s")), BTerm::Nat("1".to_owned())],
            );
            let snoc = call(
                "R.LexLeanReasoning.lengthSnoc",
                vec![element.clone(), var("ll_s"), var("ll_a")],
            );
            let stmts = vec![crate::backend::bend::syntax::Stmt::Rewrite {
                proof: call("L.Lean.Eq.symm", vec![var("Nat"), extended, sum, snoc]),
                motive: le(BTerm::Hole, bound.clone()),
                source: here(),
            }];
            let mut args = values_of(&taken.scrutinee);
            args.push(var(taken.en.clone().unwrap_or_default()));
            Ok(Body {
                stmts,
                tail: Tail::Term(call("R.LexLeanReasoning.bltSucc", args), here()),
            })
        });
        self.unfold_all = saved;
        let proof = proof?;
        let result = named(self, stepped.clone());
        let (_, hyp_arg) = self.define(
            "hyp",
            vec![
                reusable("ll_e", fold.env_type.clone()),
                reusable("ll_k", var("Unit")),
                reusable("ll_s", fold.held.clone()),
                reusable("ll_a", fold.element.clone()),
                affine("ll_p", named(self, var("ll_s"))),
            ],
            result,
            proof,
        );
        let start = super::engine::subst(&bound, &super::one("ll_e", fold.env.clone()));
        let mut args = fold.templates();
        args.extend([template(var("Unit")), inv_arg, hyp_arg]);
        args.extend([
            fold.env.clone(),
            BTerm::Constructor(synthetic("Unit"), Vec::new()),
            fold.values.clone(),
            fold.initial.clone(),
            call("RS.zeroLe", vec![start]),
        ]);
        Ok(call("RS.foldInvariant", args))
    }
}
