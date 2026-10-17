//! `congruence` and `boolean_reflection`.
//!
//! Lean closes the first with `congr 1` and the second with a fixed tactic
//! script. Here `congruence` rewrites each differing argument by a premise
//! equating it and leaves the rest to Bend's definitional check, and
//! `boolean_reflection` is proved from `Semantic.bend`'s lemmas relating
//! `&&`, `Nat.beq` and `Nat.blt` to `/\`, `=` and `<`: a record validator in
//! each direction by linear arithmetic, a list validator by two auxiliary
//! inductions on the list, one per direction.

use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Item, Param, Pattern, Quantity, Stmt, Tail};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{
    MemberRef, SemanticProof, SemanticReflection, SemanticReflectionComparison, SemanticTerm,
    SemanticType,
};

use super::super::normal;
use super::super::{call, here, synthetic, var, HOLE};
use super::{Ctx, Prover};

impl Prover<'_, '_, '_> {
    /// `congr 1`: both sides apply the same head; each argument pair that
    /// differs is rewritten by a premise equating it, and Bend checks that
    /// what remains holds by reflexivity.
    pub(super) fn congruence(&mut self, ctx: &Ctx, goal: &SemanticTerm) -> Result<Body, Diagnostic> {
        let SemanticTerm::Eq { left, right } = goal else {
            return Err(fail("`congruence` proves an equation"));
        };
        if left == right {
            return Ok(Body::term(BTerm::Refl, here()));
        }
        let children = |term: &SemanticTerm| {
            let mut out = Vec::new();
            normal::for_each_child(term, &mut |child| out.push(child.clone()));
            out
        };
        let shell = |term: &SemanticTerm| {
            let mut out = term.clone();
            normal::map_children(&mut out, &mut |child| *child = SemanticTerm::Unit);
            out
        };
        let (left_children, right_children) = (children(left), children(right));
        if left_children.is_empty()
            || left_children.len() != right_children.len()
            || shell(left) != shell(right)
        {
            return Err(fail(
                "`congruence` needs both sides of the equation to apply the same head",
            ));
        }
        let ty = self.lower.infer(left, &ctx.scope)?;
        let ty = self.lower.ty(&ty)?;
        let left_term = self.lower.term(left, &ctx.scope)?;
        let mut current = (**right).clone();
        let mut stmts = Vec::new();
        for (index, (a, b)) in left_children.iter().zip(&right_children).enumerate() {
            if a == b {
                continue;
            }
            // `%e : M(_)` with `e : a == b` turns `M(b)` into `M(a)`.
            let mut proof = None;
            for (name, premise) in &ctx.premises {
                let SemanticTerm::Eq { left: p, right: q } = premise else {
                    continue;
                };
                if p.as_ref() == a && q.as_ref() == b {
                    proof = Some(var(name.clone()));
                } else if p.as_ref() == b && q.as_ref() == a {
                    let element = self.lower.infer(a, &ctx.scope)?;
                    let element = self.lower.ty(&element)?;
                    let (p, q) = (
                        self.lower.term(p, &ctx.scope)?,
                        self.lower.term(q, &ctx.scope)?,
                    );
                    proof = Some(call("Equal.sym", vec![element, p, q, var(name.clone())]));
                }
                if proof.is_some() {
                    break;
                }
            }
            // An argument pair no premise equates must agree definitionally,
            // as `congr 1` closes it by `rfl`; the final `{==}` checks that.
            let Some(proof) = proof else {
                continue;
            };
            let hole = SemanticTerm::Var {
                name: HOLE.to_owned(),
            };
            let motive = BTerm::Equal(
                Box::new(left_term.clone()),
                Box::new(
                    self.lower
                        .term(&normal::replace_at(&current, &[index], &hole), &ctx.scope)?,
                ),
                Box::new(ty.clone()),
            );
            stmts.push(Stmt::Rewrite {
                proof,
                motive,
                source: here(),
            });
            current = normal::replace_at(&current, &[index], a);
        }
        Ok(Body {
            stmts,
            tail: Tail::Term(BTerm::Refl, here()),
        })
    }

    /// `boolean_reflection`: `validate .. = true <-> Valid ..`.
    pub(super) fn reflection(
        &mut self,
        ctx: &Ctx,
        goal: &SemanticTerm,
        reflection: &SemanticReflection,
    ) -> Result<Body, Diagnostic> {
        let SemanticTerm::Iff { left, right } = goal else {
            return Err(fail("`boolean_reflection` proves an equivalence"));
        };
        match reflection {
            SemanticReflection::Record {
                boolean_definition,
                proposition_definition,
                ..
            } => {
                // Each direction is linear arithmetic once both definitions
                // unfold to the conjunctions they are.
                let step = SemanticProof::LinearArithmetic {
                    definitions: vec![boolean_definition.clone(), proposition_definition.clone()],
                };
                let mut halves = Vec::new();
                for (premise, conclusion) in [(left, right), (right, left)] {
                    let direction = SemanticTerm::Implies {
                        premise: premise.clone(),
                        conclusion: conclusion.clone(),
                    };
                    let body = self.prove(&mut ctx.clone(), &direction, &step)?;
                    halves.push(BTerm::Block(Box::new(body)));
                }
                let backward = halves.pop().ok_or_else(|| fail("no backward half"))?;
                let forward = halves.pop().ok_or_else(|| fail("no forward half"))?;
                Ok(Body::term(
                    BTerm::Pair(Box::new(forward), Box::new(backward)),
                    here(),
                ))
            }
            SemanticReflection::List {
                parameter,
                values,
                boolean_definition,
                proposition_definition,
                comparison,
            } => {
                let (forward, backward) =
                    self.list_reflection(boolean_definition, proposition_definition, *comparison)?;
                let parameter = var(ctx.scope.get(parameter)?.0.clone());
                let values = var(ctx.scope.get(values)?.0.clone());
                // The validator's equation is `Data`; the proposition, a
                // recursive definition, is not, so its proof is used once.
                let at = |head: &str, binder: &str| {
                    BTerm::Lam(
                        synthetic(binder),
                        Box::new(call(
                            head,
                            vec![values.clone(), parameter.clone(), var("ll_reflected")],
                        )),
                    )
                };
                Ok(Body::term(
                    BTerm::Pair(
                        Box::new(at(&forward, "+ll_reflected")),
                        Box::new(at(&backward, "ll_reflected")),
                    ),
                    here(),
                ))
            }
        }
    }

    /// The two inductions of a list reflection, by name: `forward` from the
    /// validator's success to the proposition, `backward` the converse. Each
    /// assumes what Lean's tactic script does: the validator is `beq p v &&
    /// validate (p + 1) rest` (or `blt v p && validate p rest`) on a cons and
    /// `true` on nil, and the proposition is the matching conjunction.
    #[allow(clippy::too_many_lines)]
    fn list_reflection(
        &mut self,
        boolean: &MemberRef,
        proposition: &MemberRef,
        comparison: SemanticReflectionComparison,
    ) -> Result<(String, String), Diagnostic> {
        self.count += 1;
        let forward = format!("{}.ll_reflect{}.forward", self.owner, self.count);
        let backward = format!("{}.ll_reflect{}.backward", self.owner, self.count);
        let (values, p, v, rest, h, hl, hr) = (
            "ll_values",
            "ll_p",
            "ll_v",
            "ll_rest",
            "ll_h",
            "ll_hl",
            "ll_hr",
        );
        let list = self.lower.ty(&SemanticType::List {
            element: Box::new(SemanticType::Nat),
        })?;
        let beq = self.lower.prelude("Lean.Nat.beq");
        let blt = self.lower.prelude("Lean.Nat.blt");
        let add = self.lower.prelude("Lean.Nat.add");
        let and_left = self.lower.support("and_left");
        let and_right = self.lower.support("and_right");
        let and_intro = self.lower.support("and_intro");
        let beq_eq = self.lower.support("beq_eq");
        let eq_beq = self.lower.support("eq_beq");
        let succeeds = |value: BTerm| {
            BTerm::Equal(
                Box::new(value),
                Box::new(BTerm::Constructor(synthetic("True"), Vec::new())),
                Box::new(var("Bool")),
            )
        };
        let (test, next) = match comparison {
            SemanticReflectionComparison::NatBeq => (
                call(beq, vec![var(p), var(v)]),
                call(add, vec![var(p), BTerm::Nat("1".to_owned())]),
            ),
            SemanticReflectionComparison::NatBlt => (call(blt, vec![var(v), var(p)]), var(p)),
        };
        let rest_validate = self.lower.call_of(boolean, &[], vec![next.clone(), var(rest)])?;
        let validate_all = self.lower.call_of(boolean, &[], vec![var(p), var(values)])?;
        let valid_all = self.lower.call_of(proposition, &[], vec![var(p), var(values)])?;
        let param = |quantity, name: &str, ty| Param {
            quantity,
            name: synthetic(name),
            ty,
            source: here(),
        };
        let nil = Pattern::Constructor(synthetic("Nil"), Vec::new());
        let cons = Pattern::Constructor(synthetic("Con"), vec![synthetic(v), synthetic(rest)]);
        let split = |cases: Vec<(Pattern, Body)>| Body {
            stmts: Vec::new(),
            tail: Tail::Match {
                scrutinee: synthetic(values),
                cases,
                source: here(),
            },
        };

        // forward(values, p, h : validate p values = true) : Valid p values
        let head_holds = call(and_left, vec![test.clone(), rest_validate.clone(), var(h)]);
        let head = match comparison {
            SemanticReflectionComparison::NatBeq => call(beq_eq, vec![var(p), var(v), head_holds]),
            // `blt v p = true` is `v < p` itself.
            SemanticReflectionComparison::NatBlt => head_holds,
        };
        let tail = call(
            forward.clone(),
            vec![
                var(rest),
                next.clone(),
                call(and_right, vec![test.clone(), rest_validate.clone(), var(h)]),
            ],
        );
        self.aux.push(Item::Def {
            name: synthetic(forward.clone()),
            params: vec![
                param(Quantity::Reusable, values, list.clone()),
                param(Quantity::Reusable, p, var("Nat")),
                param(Quantity::Reusable, h, succeeds(validate_all.clone())),
            ],
            result: valid_all.clone(),
            result_source: here(),
            body: split(vec![
                (nil.clone(), Body::term(BTerm::Refl, here())),
                (
                    cons.clone(),
                    Body::term(BTerm::Pair(Box::new(head), Box::new(tail)), here()),
                ),
            ]),
            source: here(),
        });

        // backward(values, p, h : Valid p values) : validate p values = true
        let head = match comparison {
            SemanticReflectionComparison::NatBeq => call(eq_beq, vec![var(p), var(v), var(hl)]),
            SemanticReflectionComparison::NatBlt => var(hl),
        };
        let tail = call(backward.clone(), vec![var(rest), next, var(hr)]);
        self.aux.push(Item::Def {
            name: synthetic(backward.clone()),
            params: vec![
                param(Quantity::Reusable, values, list),
                param(Quantity::Reusable, p, var("Nat")),
                param(Quantity::Affine, h, valid_all),
            ],
            result: succeeds(validate_all),
            result_source: here(),
            body: split(vec![
                (nil, Body::term(BTerm::Refl, here())),
                (
                    cons,
                    Body {
                        stmts: Vec::new(),
                        tail: Tail::Match {
                            scrutinee: synthetic(h),
                            cases: vec![(
                                Pattern::Pair(synthetic(hl), synthetic(hr)),
                                Body::term(
                                    call(and_intro, vec![test, rest_validate, head, tail]),
                                    here(),
                                ),
                            )],
                            source: here(),
                        },
                    },
                ),
            ]),
            source: here(),
        });
        Ok((forward, backward))
    }
}
