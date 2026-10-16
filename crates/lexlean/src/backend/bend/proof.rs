//! Proof synthesis: the closed proof IR (§17.4) lowered to Bend proof
//! terms.
//!
//! Bend has no tactics: a proof is a term of its proposition. Each IR step
//! therefore becomes the term former it stands for against the goal it
//! acts on, and the engine tracks that goal exactly:
//!
//! - `intro` is a lambda (or, at the head of a theorem, a law clause),
//! - `exact`, `apply` are applications whose implicit arguments the engine
//!   solves against the goal,
//! - `rfl` is `{==}`, a witness a dependent pair, a disjunct `Inl`/`Inr`,
//!   `constructor` a pair,
//! - `rw` is a chain of `%e : P` rewrites with the motive computed by
//!   abstracting the rewritten term, closed by `{==}` as Lean's `rw` closes
//!   by `rfl`,
//! - `cases`/`induction` is an auxiliary definition that takes the
//!   scrutinee and the context as parameters and matches on the scrutinee;
//!   a Bend `match` inspects only a parameter, and the induction hypothesis
//!   is the auxiliary definition's own recursive call,
//! - `calc` is an `Equal.trans` chain.
//!
//! Every auxiliary definition is emitted before the law it serves, since a
//! Bend definition calls only definitions above it.

use std::collections::BTreeMap;

use crate::backend::bend::engine::{
    fail, false_term, is_false, mentions, spine, Ctx, Engine,
};
use crate::backend::bend::syntax::{BTerm, Body, Item, Name, Param, Pattern, Quantity, Stmt, Tail};
use crate::backend::EmitSource;
use crate::diagnostic::Diagnostic;
use crate::elaborate::expressions::subst;
use crate::ir::proof::{CaseProof, Proof, RewriteTarget};
use crate::ir::term::{Binder, CoreRef, GlobalRef, LocalId, Term, Universe};
use crate::lexicon::lse::BinderMode;
use crate::source::coverage::Origin;

/// The proof lowering of one theorem.
pub struct ProofLowering<'e, 'a> {
    /// The term engine.
    pub engine: &'e mut Engine<'a>,
    /// The theorem's Bend name, the prefix of its auxiliary definitions.
    pub owner: String,
    /// Auxiliary definitions, in emission order.
    pub auxiliary: Vec<Item>,
    /// The source range of each proof node, by address, in pre-order.
    pub spans: BTreeMap<usize, (usize, usize)>,
    /// The whole proof's range, for synthesized pieces.
    pub whole: (usize, usize),
    /// Locals whose Bend form is a term rather than their name (premise
    /// placeholders of `apply`).
    inline: BTreeMap<LocalId, BTerm>,
    /// Auxiliary definitions named so far; a name is taken before the
    /// definition's own cases lower, so nested ones never collide.
    named: usize,
}

fn address(proof: &Proof) -> usize {
    std::ptr::from_ref(proof) as usize
}

/// Record each non-sequence node's range in pre-order, matching the
/// linker's `steps` (§20.3).
pub fn index_spans(proof: &Proof, steps: &[(usize, usize)], out: &mut BTreeMap<usize, (usize, usize)>) {
    fn walk(
        proof: &Proof,
        steps: &[(usize, usize)],
        next: &mut usize,
        out: &mut BTreeMap<usize, (usize, usize)>,
    ) {
        if !matches!(proof, Proof::Sequence(_)) {
            if let Some(range) = steps.get(*next) {
                out.insert(address(proof), *range);
            }
            *next += 1;
        }
        match proof {
            Proof::Sequence(inner) | Proof::Constructor(inner) => {
                for step in inner {
                    walk(step, steps, next, out);
                }
            }
            Proof::Apply { premises, .. } => {
                for premise in premises {
                    walk(premise, steps, next, out);
                }
            }
            Proof::Have { proof, .. } => walk(proof, steps, next, out),
            Proof::Cases { cases, .. } | Proof::Induction { cases, .. } => {
                for case in cases {
                    walk(&case.proof, steps, next, out);
                }
            }
            _ => {}
        }
    }
    let mut next = 0;
    walk(proof, steps, &mut next, out);
}

/// Flatten nested sequences into one step list.
#[must_use]
pub fn flatten(proof: &Proof) -> Vec<&Proof> {
    let mut out = Vec::new();
    fn walk<'p>(proof: &'p Proof, out: &mut Vec<&'p Proof>) {
        match proof {
            Proof::Sequence(steps) => steps.iter().for_each(|step| walk(step, out)),
            other => out.push(other),
        }
    }
    walk(proof, &mut out);
    out
}

fn app(function: Term, args: Vec<Term>) -> Term {
    Term::App {
        function: Box::new(function),
        explicit_args: args,
        omitted_implicit_binders: Vec::new(),
    }
}

/// Replace every occurrence of `from` in `term` (alpha-equal, no
/// unfolding: Lean's `rw` matches syntactically) with `to`. Returns the
/// count of occurrences replaced.
fn replace(term: &Term, from: &Term, to: &Term, count: &mut usize) -> Term {
    if crate::elaborate::expressions::unify_closed(term, from) {
        *count += 1;
        return to.clone();
    }
    match term {
        Term::App {
            function,
            explicit_args,
            omitted_implicit_binders,
        } => Term::App {
            function: Box::new(replace(function, from, to, count)),
            explicit_args: explicit_args
                .iter()
                .map(|arg| replace(arg, from, to, count))
                .collect(),
            omitted_implicit_binders: omitted_implicit_binders.clone(),
        },
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            let binders: Vec<Binder> = binders
                .iter()
                .map(|binder| Binder {
                    ty: replace(&binder.ty, from, to, count),
                    ..binder.clone()
                })
                .collect();
            let body = Box::new(replace(body, from, to, count));
            if matches!(term, Term::Pi { .. }) {
                Term::Pi { binders, body }
            } else {
                Term::Lambda { binders, body }
            }
        }
        Term::Let {
            binder,
            value,
            body,
        } => Term::Let {
            binder: Box::new(Binder {
                ty: replace(&binder.ty, from, to, count),
                ..(**binder).clone()
            }),
            value: Box::new(replace(value, from, to, count)),
            body: Box::new(replace(body, from, to, count)),
        },
        other => other.clone(),
    }
}

/// The Lean constructor name of a case, last segment (`zero`, `succ`,
/// `inl`, `intro`, `cons`).
fn alternative(case: &CaseProof) -> &str {
    case.lean_name.rsplit('.').next().unwrap_or(&case.lean_name)
}

impl ProofLowering<'_, '_> {
    /// A lowering for one theorem.
    pub fn new<'e, 'a>(
        engine: &'e mut Engine<'a>,
        owner: String,
        spans: BTreeMap<usize, (usize, usize)>,
        whole: (usize, usize),
    ) -> ProofLowering<'e, 'a> {
        ProofLowering {
            engine,
            owner,
            auxiliary: Vec::new(),
            spans,
            whole,
            inline: BTreeMap::new(),
            named: 0,
        }
    }

    fn source(&self, proof: &Proof) -> EmitSource {
        let (start, end) = self
            .spans
            .get(&address(proof))
            .copied()
            .unwrap_or(self.whole);
        EmitSource::File(start, end)
    }

    fn lower_term(&mut self, ctx: &Ctx, term: &Term, expected: Option<&Term>) -> Result<BTerm, Diagnostic> {
        if !self.inline.is_empty() {
            let mut map = BTreeMap::new();
            for id in self.inline.keys() {
                if mentions(term, *id) {
                    map.insert(*id, ());
                }
            }
            if !map.is_empty() {
                // A placeholder stands directly for its premise term.
                if let Term::Local(id) = term {
                    if let Some(found) = self.inline.get(id) {
                        return Ok(found.clone());
                    }
                }
            }
        }
        let lowered = self.engine.lower(ctx, term, expected)?;
        Ok(self.substitute_inline(lowered))
    }

    /// Replace placeholder names in a lowered term by their premise terms.
    fn substitute_inline(&self, term: BTerm) -> BTerm {
        if self.inline.is_empty() {
            return term;
        }
        let names: BTreeMap<String, BTerm> = self
            .inline
            .iter()
            .filter_map(|(id, value)| {
                self.engine
                    .names
                    .get(id)
                    .map(|name| (name.clone(), value.clone()))
            })
            .collect();
        substitute_names(term, &names)
    }

    fn whnf(&mut self, term: &Term) -> Result<Term, Diagnostic> {
        self.engine.whnf(term)
    }

    /// Lower a step list against a goal.
    #[allow(clippy::too_many_lines)]
    pub fn prove(&mut self, ctx: &Ctx, goal: &Term, steps: &[&Proof]) -> Result<Body, Diagnostic> {
        let Some((&step, rest)) = steps.split_first() else {
            return Err(fail("a proof ends before its goal is closed"));
        };
        let source = self.source(step);
        match step {
            Proof::Sequence(_) => {
                let mut flat = flatten(step);
                flat.extend_from_slice(rest);
                self.prove(ctx, goal, &flat)
            }
            Proof::Intro(ids) => {
                let mut inner = ctx.clone();
                let mut current = goal.clone();
                let mut names = Vec::new();
                for id in ids {
                    let (binder, body) = self.peel(&current)?;
                    let mut map = BTreeMap::new();
                    map.insert(binder.id, Term::Local(*id));
                    current = subst(&body, &map);
                    inner.push((*id, binder.ty.clone()));
                    let name = self.engine.proof_binder(*id);
                    names.push(Name::new(
                        name,
                        Origin::Local(usize::try_from(id.0).unwrap_or(usize::MAX)),
                    ));
                }
                let body = self.prove(&inner, &current, rest)?;
                let mut term = body_term(body);
                for name in names.into_iter().rev() {
                    term = BTerm::Lam(name, Box::new(term));
                }
                Ok(Body::term(term, source))
            }
            Proof::Exact(term) => {
                self.require_last(rest)?;
                Ok(Body::term(self.lower_term(ctx, term, Some(goal))?, source))
            }
            Proof::Reflexivity => {
                self.require_last(rest)?;
                Ok(Body::term(BTerm::Refl, source))
            }
            Proof::Witness(witness) => {
                let goal_normal = self.whnf(goal)?;
                let (binder, body) = self.existential(&goal_normal)?;
                let mut map = BTreeMap::new();
                map.insert(binder.id, witness.clone());
                let remaining = subst(&body, &map);
                let witness_b = self.lower_term(ctx, witness, Some(&binder.ty))?;
                let proof = self.prove(ctx, &remaining, rest)?;
                // The second component's type is the predicate applied to
                // the witness; Bend checks a statement block only against a
                // stated type, so a block is annotated with it.
                let second = match body_term(proof) {
                    block @ BTerm::Block(_) => {
                        let ty = self.lower_term(ctx, &remaining, None)?;
                        BTerm::Ann(Box::new(block), Box::new(ty))
                    }
                    other => other,
                };
                Ok(Body::term(
                    BTerm::Pair(Box::new(witness_b), Box::new(second)),
                    source,
                ))
            }
            Proof::SelectLeft | Proof::SelectRight => {
                let goal_normal = self.whnf(goal)?;
                let (left, right) = self.binary(&goal_normal, CoreRef::Or)?;
                let (chosen, constructor) = if matches!(step, Proof::SelectLeft) {
                    (left, "Inl")
                } else {
                    (right, "Inr")
                };
                let proof = self.prove(ctx, &chosen, rest)?;
                Ok(Body::term(
                    BTerm::Constructor(
                        Name::new(constructor, core_or_origin()),
                        vec![body_term(proof)],
                    ),
                    source,
                ))
            }
            Proof::Constructor(branches) => {
                self.require_last(rest)?;
                let goal_normal = self.whnf(goal)?;
                let (head, args) = spine(&goal_normal);
                let goals: Vec<Term> = match (head, args.as_slice()) {
                    (Term::Global(GlobalRef::Core(CoreRef::And), _), [a, b]) => {
                        vec![a.clone(), b.clone()]
                    }
                    (Term::Global(GlobalRef::Core(CoreRef::Iff), _), [a, b]) => vec![
                        self.arrow(a.clone(), b.clone()),
                        self.arrow(b.clone(), a.clone()),
                    ],
                    _ => {
                        return Err(fail(
                            "`constructor` applies to a conjunction or a biconditional goal in the Bend lowering",
                        ))
                    }
                };
                if goals.len() != branches.len() {
                    return Err(fail("`constructor` has a branch count different from its goals"));
                }
                let mut parts = Vec::new();
                for (sub_goal, branch) in goals.iter().zip(branches) {
                    let flat = flatten(branch);
                    parts.push(body_term(self.prove(ctx, sub_goal, &flat)?));
                }
                let mut parts = parts.into_iter();
                let first = parts.next().expect("two goals");
                let second = parts.next().expect("two goals");
                Ok(Body::term(BTerm::Pair(Box::new(first), Box::new(second)), source))
            }
            Proof::Have {
                local,
                proposition,
                proof,
            } => {
                let flat = flatten(proof);
                let value = body_term(self.prove(ctx, proposition, &flat)?);
                let ty = self.lower_term(ctx, proposition, None)?;
                let name = self.engine.proof_binder(*local);
                let mut inner = ctx.clone();
                inner.push((*local, proposition.clone()));
                let mut body = self.prove(&inner, goal, rest)?;
                body.stmts.insert(
                    0,
                    Stmt::Let {
                        name: Name::new(
                            name,
                            Origin::Local(usize::try_from(local.0).unwrap_or(usize::MAX)),
                        ),
                        value: BTerm::Ann(Box::new(value), Box::new(ty)),
                        source,
                    },
                );
                Ok(body)
            }
            Proof::Rewrite {
                target: RewriteTarget::Goal,
                rules,
            } => {
                let mut stmts = Vec::new();
                let mut current = goal.clone();
                for rule in rules {
                    let (ty, from, to, equation) = self.rule(ctx, &rule.term, rule.reverse)?;
                    let hole = self.engine.fresh.next();
                    self.engine.names.insert(hole, "_".to_owned());
                    let mut count = 0;
                    let motive = replace(&current, &from, &Term::Local(hole), &mut count);
                    if count == 0 {
                        return Err(fail(
                            "a rewrite rule's left side does not occur in the goal",
                        ));
                    }
                    let mut hole_ctx = ctx.clone();
                    hole_ctx.push((hole, ty.clone()));
                    let motive_b = self.lower_term(&hole_ctx, &motive, None)?;
                    stmts.push(Stmt::Rewrite {
                        proof: equation,
                        motive: motive_b,
                        source: source.clone(),
                    });
                    let mut map = BTreeMap::new();
                    map.insert(hole, to);
                    current = subst(&motive, &map);
                }
                let mut body = if rest.is_empty() {
                    Body::term(BTerm::Refl, source)
                } else {
                    self.prove(ctx, &current, rest)?
                };
                stmts.append(&mut body.stmts);
                body.stmts = stmts;
                Ok(body)
            }
            Proof::Rewrite {
                target: RewriteTarget::Hypothesis(hypothesis),
                rules,
            } => {
                let original = ctx
                    .iter()
                    .rev()
                    .find(|(id, _)| id == hypothesis)
                    .map(|(_, ty)| ty.clone())
                    .ok_or_else(|| fail("a rewritten hypothesis is not in scope"))?;
                // Compute the rewritten type, then an auxiliary
                // definition whose goal is the new type, rewritten back to
                // the old one and closed by the hypothesis.
                let mut types = vec![original.clone()];
                let mut equations = Vec::new();
                let mut current = original;
                for rule in rules {
                    let (ty, from, to, _) = self.rule(ctx, &rule.term, rule.reverse)?;
                    let hole = self.engine.fresh.next();
                    self.engine.names.insert(hole, "_".to_owned());
                    let mut count = 0;
                    let motive = replace(&current, &from, &Term::Local(hole), &mut count);
                    if count == 0 {
                        return Err(fail(
                            "a rewrite rule's left side does not occur in the hypothesis",
                        ));
                    }
                    let mut map = BTreeMap::new();
                    map.insert(hole, to.clone());
                    let next = subst(&motive, &map);
                    // Going back from `next` to `current` rewrites `to`
                    // into `from`: the equation `{from == to}`.
                    let back = self.equation(ctx, &ty, &from, &to, &rule.term, rule.reverse)?;
                    equations.push((hole, ty, motive, back));
                    types.push(next.clone());
                    current = next;
                }
                let new_type = current;
                let aux_name = self.aux_name("r");
                let (params, args) = self.context_params(ctx, &[])?;
                let mut stmts = Vec::new();
                for (hole, ty, motive, back) in equations.into_iter().rev() {
                    let mut hole_ctx = ctx.clone();
                    hole_ctx.push((hole, ty));
                    let motive_b = self.lower_term(&hole_ctx, &motive, None)?;
                    stmts.push(Stmt::Rewrite {
                        proof: back,
                        motive: motive_b,
                        source: source.clone(),
                    });
                }
                let result = self.lower_term(ctx, &new_type, None)?;
                let hypothesis_name = self.engine.names.get(hypothesis).cloned().unwrap_or_default();
                self.auxiliary.push(Item::Def {
                    name: Name::synthetic(aux_name.clone()),
                    params,
                    result,
                    result_source: source.clone(),
                    body: Body {
                        stmts,
                        tail: Tail::Term(
                            BTerm::Name(Name::new(
                                hypothesis_name.clone(),
                                Origin::Local(usize::try_from(hypothesis.0).unwrap_or(usize::MAX)),
                            )),
                            source.clone(),
                        ),
                    },
                    source: source.clone(),
                });
                let mut inner = ctx.clone();
                if let Some(entry) = inner.iter_mut().rev().find(|(id, _)| id == hypothesis) {
                    entry.1 = new_type;
                }
                let mut body = self.prove(&inner, goal, rest)?;
                body.stmts.insert(
                    0,
                    Stmt::Let {
                        name: Name::new(
                            hypothesis_name,
                            Origin::Local(usize::try_from(hypothesis.0).unwrap_or(usize::MAX)),
                        ),
                        value: BTerm::Call(Name::synthetic(aux_name), args),
                        source,
                    },
                );
                Ok(body)
            }
            Proof::SimplifyOnly { .. } => Err(fail(
                "`simp only` has no Bend lowering in language 1.0 documents: Bend has no simplifier",
            )),
            Proof::ApplyOne(function) => {
                let (function_term, premises) = self.apply_premises(ctx, function, goal)?;
                match premises.len() {
                    0 => {
                        self.require_last(rest)?;
                        let lowered = self.lower_applied(ctx, &function_term, &[], goal)?;
                        Ok(Body::term(lowered, source))
                    }
                    1 => {
                        let (placeholder, premise_goal) = premises[0].clone();
                        let premise = body_term(self.prove(ctx, &premise_goal, rest)?);
                        let lowered = self.lower_applied(
                            ctx,
                            &function_term,
                            &[(placeholder, premise_goal, premise)],
                            goal,
                        )?;
                        Ok(Body::term(lowered, source))
                    }
                    _ => Err(fail(
                        "an `apply` step leaves more than one premise for the steps after it",
                    )),
                }
            }
            Proof::Apply {
                function,
                premises: proofs,
            } => {
                self.require_last(rest)?;
                let (function_term, premises) = self.apply_premises(ctx, function, goal)?;
                if premises.len() != proofs.len() {
                    return Err(fail(format!(
                        "an `apply` step proves {} premise(s), but its function leaves {}",
                        proofs.len(),
                        premises.len()
                    )));
                }
                let mut filled = Vec::new();
                for ((placeholder, premise_goal), proof) in premises.into_iter().zip(proofs) {
                    let flat = flatten(proof);
                    let premise = body_term(self.prove(ctx, &premise_goal, &flat)?);
                    filled.push((placeholder, premise_goal, premise));
                }
                let lowered = self.lower_applied(ctx, &function_term, &filled, goal)?;
                Ok(Body::term(lowered, source))
            }
            Proof::Cases { scrutinee, cases } => {
                self.require_last(rest)?;
                self.case_split(ctx, goal, scrutinee, cases, false, source)
            }
            Proof::Induction { scrutinee, cases } => {
                self.require_last(rest)?;
                self.case_split(ctx, goal, scrutinee, cases, true, source)
            }
            Proof::Calculate {
                relation,
                start,
                steps: chain,
            } => {
                self.require_last(rest)?;
                if !matches!(relation, GlobalRef::Core(CoreRef::Eq)) {
                    return Err(fail(
                        "language 1.0 lowers exactly the equality calculation descriptor",
                    ));
                }
                let ty = self.engine.infer(ctx, start)?;
                let ty_b = self.lower_term(ctx, &ty, None)?;
                let mut points = vec![start.clone()];
                points.extend(chain.iter().map(|step| step.term.clone()));
                let last = points.last().cloned().expect("a start");
                let mut proofs = Vec::new();
                for (index, step) in chain.iter().enumerate() {
                    let expected = app(
                        Term::Global(GlobalRef::Core(CoreRef::Eq), Vec::new()),
                        vec![points[index].clone(), points[index + 1].clone()],
                    );
                    proofs.push(self.lower_term(ctx, &step.proof, Some(&expected))?);
                }
                // trans(p0, p1, pn, step0, trans(p1, p2, pn, step1, ...)).
                let mut term = proofs.pop().ok_or_else(|| fail("an empty calculation"))?;
                for index in (0..proofs.len()).rev() {
                    let a = self.lower_term(ctx, &points[index], Some(&ty))?;
                    let b = self.lower_term(ctx, &points[index + 1], Some(&ty))?;
                    let c = self.lower_term(ctx, &last, Some(&ty))?;
                    term = BTerm::Call(
                        Name::synthetic("Equal.trans"),
                        vec![
                            (false, ty_b.clone()),
                            (false, a),
                            (false, b),
                            (false, c),
                            (false, proofs[index].clone()),
                            (false, term),
                        ],
                    );
                }
                Ok(Body::term(term, source))
            }
        }
    }

    fn require_last(&self, rest: &[&Proof]) -> Result<(), Diagnostic> {
        if rest.is_empty() {
            Ok(())
        } else {
            Err(fail("a proof step follows a step that closes its goal"))
        }
    }

    fn arrow(&mut self, from: Term, to: Term) -> Term {
        Term::Pi {
            binders: vec![Binder {
                id: self.engine.fresh.next(),
                mode: BinderMode::Explicit,
                ty: from,
                spelling: String::new(),
            }],
            body: Box::new(to),
        }
    }

    /// The first binder of a function goal and the rest.
    fn peel(&mut self, goal: &Term) -> Result<(Binder, Term), Diagnostic> {
        let normal = match goal {
            Term::Pi { .. } => goal.clone(),
            other => self.whnf(other)?,
        };
        let Term::Pi { binders, body } = normal else {
            return Err(fail("`intro` acts on a goal that is not a function type"));
        };
        let mut binders = binders.into_iter();
        let first = binders.next().ok_or_else(|| fail("an empty binder group"))?;
        let remaining: Vec<Binder> = binders.collect();
        let rest = if remaining.is_empty() {
            *body
        } else {
            Term::Pi {
                binders: remaining,
                body,
            }
        };
        Ok((first, rest))
    }

    fn binary(&mut self, goal: &Term, core: CoreRef) -> Result<(Term, Term), Diagnostic> {
        let (head, args) = spine(goal);
        match (head, args.as_slice()) {
            (Term::Global(GlobalRef::Core(found), _), [a, b]) if *found == core => {
                Ok((a.clone(), b.clone()))
            }
            _ => Err(fail(format!(
                "the step needs a `{}` goal",
                core.lean_name()
            ))),
        }
    }

    /// The binder and body of an existential goal (unique existence
    /// expanded first, as the Lean lowering does).
    fn existential(&mut self, goal: &Term) -> Result<(Binder, Term), Diagnostic> {
        let (head, args) = spine(goal);
        match (head, args.as_slice()) {
            (Term::Global(GlobalRef::Core(CoreRef::Exists), _), [predicate]) => {
                let predicate = self.whnf(predicate)?;
                let Term::Lambda { binders, body } = predicate else {
                    return Err(fail("an existential's predicate is not a lambda"));
                };
                let mut binders = binders.into_iter();
                let first = binders.next().ok_or_else(|| fail("an empty existential"))?;
                let remaining: Vec<Binder> = binders.collect();
                let body = if remaining.is_empty() {
                    *body
                } else {
                    app(
                        Term::Global(GlobalRef::Core(CoreRef::Exists), Vec::new()),
                        vec![Term::Lambda {
                            binders: remaining,
                            body,
                        }],
                    )
                };
                Ok((first, body))
            }
            (Term::Global(GlobalRef::Core(CoreRef::ExistsUnique), _), [predicate]) => {
                let expanded = self.engine.expand_exists_unique(predicate)?;
                self.existential(&expanded)
            }
            _ => Err(fail("a witness step needs an existential goal")),
        }
    }

    /// A rewrite rule's equation type and sides: `(T, from, to, proof)` where
    /// rewriting replaces `from` by `to` in the goal and `proof` is the
    /// Bend equation `{to == from : T}` that `%` needs.
    fn rule(
        &mut self,
        ctx: &Ctx,
        term: &Term,
        reverse: bool,
    ) -> Result<(Term, Term, Term, BTerm), Diagnostic> {
        let rule_type = self.engine.infer(ctx, term)?;
        let rule_type = self.whnf(&rule_type)?;
        let (head, args) = spine(&rule_type);
        let (Term::Global(GlobalRef::Core(CoreRef::Eq), _), [left, right]) = (head, args.as_slice())
        else {
            return Err(fail("a rewrite rule is not an equation"));
        };
        let ty = self.engine.infer(ctx, left)?;
        let (from, to) = if reverse {
            (right.clone(), left.clone())
        } else {
            (left.clone(), right.clone())
        };
        let proof = self.lower_term(ctx, term, None)?;
        let ty_b = self.lower_term(ctx, &ty, None)?;
        let equation = if reverse {
            // rule : left == right = to == from.
            proof
        } else {
            let left_b = self.lower_term(ctx, left, Some(&ty))?;
            let right_b = self.lower_term(ctx, right, Some(&ty))?;
            BTerm::Call(
                Name::synthetic("Equal.sym"),
                vec![(false, ty_b), (false, left_b), (false, right_b), (false, proof)],
            )
        };
        Ok((ty, from, to, equation))
    }

    /// The equation `{from == to : T}` (the direction that rewrites a
    /// hypothesis back from its new type).
    fn equation(
        &mut self,
        ctx: &Ctx,
        ty: &Term,
        from: &Term,
        to: &Term,
        rule: &Term,
        reverse: bool,
    ) -> Result<BTerm, Diagnostic> {
        let proof = self.lower_term(ctx, rule, None)?;
        if reverse {
            // rule : to == from.
            let ty_b = self.lower_term(ctx, ty, None)?;
            let to_b = self.lower_term(ctx, to, Some(ty))?;
            let from_b = self.lower_term(ctx, from, Some(ty))?;
            Ok(BTerm::Call(
                Name::synthetic("Equal.sym"),
                vec![(false, ty_b), (false, to_b), (false, from_b), (false, proof)],
            ))
        } else {
            Ok(proof)
        }
    }

    fn aux_name(&mut self, kind: &str) -> String {
        let name = format!("{}.{kind}{}", self.owner, self.named);
        self.named += 1;
        name
    }

    /// The context as auxiliary parameters, `first` hoisted to its
    /// earliest legal position, and the arguments that pass it.
    fn context_params(
        &mut self,
        ctx: &Ctx,
        exclude: &[LocalId],
    ) -> Result<(Vec<Param>, Vec<(bool, BTerm)>), Diagnostic> {
        let mut params = Vec::new();
        let mut args = Vec::new();
        for (index, (id, ty)) in ctx.iter().enumerate() {
            if exclude.contains(id) {
                continue;
            }
            let prefix: Ctx = ctx[..index].to_vec();
            let param = self.param(&prefix, *id, ty)?;
            args.push((false, BTerm::Name(param.name.clone())));
            params.push(param);
        }
        Ok((params, args))
    }

    /// One typed parameter for a local.
    pub fn param(&mut self, prefix: &Ctx, id: LocalId, ty: &Term) -> Result<Param, Diagnostic> {
        let normal = self.engine.whnf(ty)?;
        let quantity = if matches!(normal, Term::Sort(Universe::Num(_))) {
            Quantity::Erased
        } else if self.engine.is_data(prefix, ty) {
            Quantity::Reusable
        } else {
            Quantity::Affine
        };
        let name = self
            .engine
            .names
            .get(&id)
            .cloned()
            .unwrap_or_else(|| self.engine.term_binder(id));
        Ok(Param {
            quantity,
            name: Name::new(
                name,
                Origin::Local(usize::try_from(id.0).unwrap_or(usize::MAX)),
            ),
            ty: self.lower_term(prefix, ty, None)?,
            source: EmitSource::File(self.whole.0, self.whole.1),
        })
    }

    /// A `cases` or `induction` step: an auxiliary definition matching on
    /// its scrutinee parameter.
    #[allow(clippy::too_many_lines)]
    fn case_split(
        &mut self,
        ctx: &Ctx,
        goal: &Term,
        scrutinee: &Term,
        cases: &[CaseProof],
        induction: bool,
        source: EmitSource,
    ) -> Result<Body, Diagnostic> {
        let aux_name = self.aux_name(if induction { "i" } else { "c" });
        // The scrutinee is a context local, or a fresh parameter that the
        // call passes the scrutinee term to.
        let (scrutinee_id, scrutinee_type, passed) = match scrutinee {
            Term::Local(id) if ctx.iter().any(|(local, _)| local == id) => {
                let ty = ctx
                    .iter()
                    .rev()
                    .find(|(local, _)| local == id)
                    .map(|(_, ty)| ty.clone())
                    .expect("found above");
                (*id, ty, None)
            }
            other => {
                if induction {
                    return Err(fail("induction is on a context variable in the Bend lowering"));
                }
                let id = self.engine.fresh.next();
                let ty = self.engine.infer(ctx, other)?;
                let name = format!("llc{}", self.named);
                self.engine.names.insert(id, name);
                (id, ty, Some(other.clone()))
            }
        };
        // Parameter order: what the scrutinee's type mentions, the
        // scrutinee, then the rest of the context, each in context order.
        let mut ordered: Ctx = Vec::new();
        let mut later: Ctx = Vec::new();
        for (id, ty) in ctx {
            if *id == scrutinee_id {
                continue;
            }
            if mentions(&scrutinee_type, *id) {
                ordered.push((*id, ty.clone()));
            } else {
                later.push((*id, ty.clone()));
            }
        }
        ordered.push((scrutinee_id, scrutinee_type.clone()));
        let scrutinee_index = ordered.len() - 1;
        ordered.extend(later);
        let mut params = Vec::new();
        let mut call_args = Vec::new();
        for (index, (id, ty)) in ordered.iter().enumerate() {
            let prefix: Ctx = ordered[..index].to_vec();
            let param = self.param(&prefix, *id, ty)?;
            if *id == scrutinee_id {
                if let Some(term) = &passed {
                    call_args.push((false, self.lower_term(ctx, term, Some(&scrutinee_type))?));
                } else {
                    call_args.push((false, BTerm::Name(param.name.clone())));
                }
            } else {
                call_args.push((false, BTerm::Name(param.name.clone())));
            }
            params.push(param);
        }
        let result = self.lower_term(&ordered, goal, None)?;
        let scrutinee_name = params[scrutinee_index].name.clone();
        let normal = self.whnf(&scrutinee_type)?;
        let (head, type_args) = spine(&normal);
        let head = head.clone();
        let mut arms = Vec::new();
        for case in cases {
            let mut case_ctx: Ctx = ordered.clone();
            case_ctx.remove(scrutinee_index);
            let names: Vec<Name> = case
                .binders
                .iter()
                .map(|(id, _)| {
                    let text = self.engine.proof_binder(*id);
                    Name::new(text, Origin::Local(usize::try_from(id.0).unwrap_or(usize::MAX)))
                })
                .collect();
            let (pattern, fields, value): (Pattern, Vec<(LocalId, Term)>, Option<Term>) =
                self.case_shape(&head, &type_args, case, &names)?;
            // A field of `Data` type is bound reusable (`+`), as a proof may
            // need it in a recursive call and in the goal.
            let mut reusable = Vec::new();
            for (offset, (_, field_ty)) in fields.iter().enumerate() {
                let prefix: Ctx = ordered[..scrutinee_index].to_vec();
                if self.engine.is_data(&prefix, field_ty) {
                    reusable.push(offset);
                }
            }
            let pattern = mark_reusable(pattern, &reusable);
            // Bind the fields after the parameters that precede the
            // scrutinee, so their types see those parameters.
            for (offset, field) in fields.iter().enumerate() {
                case_ctx.insert(scrutinee_index + offset, field.clone());
            }
            let mut case_goal = goal.clone();
            if let Some(value) = &value {
                let mut map = BTreeMap::new();
                map.insert(scrutinee_id, value.clone());
                case_goal = subst(goal, &map);
                for entry in &mut case_ctx {
                    entry.1 = subst(&entry.1, &map);
                }
            }
            let mut stmts = Vec::new();
            if induction {
                // The induction hypothesis: the auxiliary definition at the
                // structurally smaller field, the last case binder.
                let recursive = self.recursive_field(&head, case, &fields)?;
                if let (Some(recursive_id), Some((ih_id, _))) = (recursive, case.binders.last()) {
                    let mut map = BTreeMap::new();
                    map.insert(scrutinee_id, Term::Local(recursive_id));
                    let ih_type = subst(goal, &map);
                    let mut args = Vec::new();
                    for (id, _) in &ordered {
                        let target = if *id == scrutinee_id { recursive_id } else { *id };
                        let name = self.engine.names.get(&target).cloned().unwrap_or_default();
                        args.push((
                            false,
                            BTerm::Name(Name::new(
                                name,
                                Origin::Local(usize::try_from(target.0).unwrap_or(usize::MAX)),
                            )),
                        ));
                    }
                    let ih_name = self.engine.names.get(ih_id).cloned().unwrap_or_default();
                    stmts.push(Stmt::Let {
                        name: Name::new(
                            ih_name,
                            Origin::Local(usize::try_from(ih_id.0).unwrap_or(usize::MAX)),
                        ),
                        value: BTerm::Call(Name::synthetic(aux_name.clone()), args),
                        source: source.clone(),
                    });
                    case_ctx.push((*ih_id, ih_type));
                }
            }
            let flat = flatten(&case.proof);
            let mut body = self.prove(&case_ctx, &case_goal, &flat)?;
            stmts.append(&mut body.stmts);
            body.stmts = stmts;
            arms.push((pattern, body));
        }
        // An auxiliary definition takes its index before the cases lower,
        // so nested auxiliaries number after it; it is pushed afterwards
        // and moved ahead of any auxiliary its cases created.
        let item = Item::Def {
            name: Name::synthetic(aux_name.clone()),
            params,
            result,
            result_source: source.clone(),
            body: Body {
                stmts: Vec::new(),
                tail: Tail::Match {
                    scrutinee: scrutinee_name,
                    cases: arms,
                    source: source.clone(),
                },
            },
            source: source.clone(),
        };
        self.auxiliary.push(item);
        Ok(Body::term(
            BTerm::Call(Name::synthetic(aux_name), call_args),
            source,
        ))
    }

    /// A case's pattern, its field locals with types, and the value the
    /// scrutinee takes in the case (for refining a goal that mentions it).
    #[allow(clippy::too_many_lines, clippy::type_complexity)]
    fn case_shape(
        &mut self,
        head: &Term,
        type_args: &[Term],
        case: &CaseProof,
        names: &[Name],
    ) -> Result<(Pattern, Vec<(LocalId, Term)>, Option<Term>), Diagnostic> {
        let ids: Vec<LocalId> = case.binders.iter().map(|(id, _)| *id).collect();
        let shape_error = || {
            fail(format!(
                "a case on `{}` has no Bend pattern for this scrutinee type",
                case.lean_name
            ))
        };
        match head {
            Term::Global(GlobalRef::Core(CoreRef::And | CoreRef::Iff), _) => {
                let [left, right] = type_args else {
                    return Err(shape_error());
                };
                let (left_ty, right_ty) = if matches!(head, Term::Global(GlobalRef::Core(CoreRef::Iff), _)) {
                    (
                        self.arrow(left.clone(), right.clone()),
                        self.arrow(right.clone(), left.clone()),
                    )
                } else {
                    (left.clone(), right.clone())
                };
                let [a, b] = ids.as_slice() else {
                    return Err(shape_error());
                };
                Ok((
                    Pattern::Pair(names[0].clone(), names[1].clone()),
                    vec![(*a, left_ty), (*b, right_ty)],
                    None,
                ))
            }
            Term::Global(GlobalRef::Core(CoreRef::Exists | CoreRef::ExistsUnique), _) => {
                let goal = app(head.clone(), type_args.to_vec());
                let (binder, body) = self.existential(&goal)?;
                let [w, h] = ids.as_slice() else {
                    return Err(shape_error());
                };
                let mut map = BTreeMap::new();
                map.insert(binder.id, Term::Local(*w));
                Ok((
                    Pattern::Pair(names[0].clone(), names[1].clone()),
                    vec![(*w, binder.ty.clone()), (*h, subst(&body, &map))],
                    None,
                ))
            }
            Term::Global(GlobalRef::Core(CoreRef::Or), _) => {
                let [left, right] = type_args else {
                    return Err(shape_error());
                };
                let [h] = ids.as_slice() else {
                    return Err(shape_error());
                };
                let (constructor, ty) = match alternative(case) {
                    "inl" => ("Inl", left.clone()),
                    "inr" => ("Inr", right.clone()),
                    _ => return Err(shape_error()),
                };
                Ok((
                    Pattern::Constructor(Name::new(constructor, core_or_origin()), vec![names[0].clone()]),
                    vec![(*h, ty)],
                    None,
                ))
            }
            Term::Global(GlobalRef::External(external), _) => {
                let constructor_global = self.constructor_global(case)?;
                let alt = alternative(case);
                let lean = external.lean_name.as_str();
                match (lean, alt) {
                    ("Nat", "zero") => Ok((
                        Pattern::Zero,
                        Vec::new(),
                        Some(Term::Global(constructor_global, Vec::new())),
                    )),
                    ("Nat", "succ") => {
                        let Some(p) = ids.first() else {
                            return Err(shape_error());
                        };
                        Ok((
                            Pattern::Succ(names[0].clone()),
                            vec![(*p, app_type(head))],
                            Some(app(
                                Term::Global(constructor_global, Vec::new()),
                                vec![Term::Local(*p)],
                            )),
                        ))
                    }
                    ("List", "nil") => Ok((
                        Pattern::Constructor(Name::synthetic("Nil"), Vec::new()),
                        Vec::new(),
                        Some(Term::Global(constructor_global, Vec::new())),
                    )),
                    ("List", "cons") => {
                        let (Some(h), Some(t)) = (ids.first(), ids.get(1)) else {
                            return Err(shape_error());
                        };
                        let element = type_args.first().cloned().ok_or_else(shape_error)?;
                        let list = app(head.clone(), type_args.to_vec());
                        Ok((
                            Pattern::Constructor(
                                Name::synthetic("Con"),
                                vec![names[0].clone(), names[1].clone()],
                            ),
                            vec![(*h, element), (*t, list)],
                            Some(app(
                                Term::Global(constructor_global, Vec::new()),
                                vec![Term::Local(*h), Term::Local(*t)],
                            )),
                        ))
                    }
                    ("Bool", "true" | "false") => Ok((
                        Pattern::Constructor(
                            Name::synthetic(if alt == "true" { "True" } else { "False" }),
                            Vec::new(),
                        ),
                        Vec::new(),
                        Some(Term::Global(constructor_global, Vec::new())),
                    )),
                    _ => Err(shape_error()),
                }
            }
            _ => Err(shape_error()),
        }
    }

    fn recursive_field(
        &self,
        head: &Term,
        case: &CaseProof,
        fields: &[(LocalId, Term)],
    ) -> Result<Option<LocalId>, Diagnostic> {
        let Term::Global(GlobalRef::External(external), _) = head else {
            return Err(fail("induction is on a natural number or a list in the Bend lowering"));
        };
        Ok(match (external.lean_name.as_str(), alternative(case)) {
            ("Nat", "succ") => fields.first().map(|(id, _)| *id),
            ("List", "cons") => fields.get(1).map(|(id, _)| *id),
            ("Nat", "zero") | ("List", "nil") => None,
            _ => return Err(fail("induction is on a natural number or a list in the Bend lowering")),
        })
    }

    fn constructor_global(&self, case: &CaseProof) -> Result<GlobalRef, Diagnostic> {
        let entry = self
            .engine
            .project
            .closure
            .entry(&case.constructor)
            .ok_or_else(|| fail(format!("`{}` is not in the glossary closure", case.constructor)))?;
        let crate::lexicon::entry::Denotation::Lean { module, name } = &entry.denotation else {
            return Err(fail(format!("`{}` is not a Lean constructor", case.constructor)));
        };
        Ok(GlobalRef::External(crate::ir::term::ExternalConstRef {
            package: case.constructor.package.clone(),
            entry: case.constructor.to_string(),
            lean_module: module.clone(),
            lean_name: name.clone(),
            signature_hash: entry
                .signature_hash
                .ok_or_else(|| fail(format!("`{}` has no signature", case.constructor)))?,
        }))
    }

    /// For `apply f`: the function term and the premises it leaves, each
    /// a placeholder local with its goal.
    fn apply_premises(
        &mut self,
        ctx: &Ctx,
        function: &Term,
        goal: &Term,
    ) -> Result<(Term, Vec<(LocalId, Term)>), Diagnostic> {
        let function_type = self.engine.infer(ctx, function)?;
        let mut binders = Vec::new();
        let mut rest = function_type;
        loop {
            let normal = match &rest {
                Term::Pi { .. } => rest.clone(),
                other => self.whnf(other)?,
            };
            match normal {
                Term::Pi {
                    binders: group,
                    body,
                } => {
                    binders.extend(group);
                    rest = *body;
                }
                _ => break,
            }
            let mut metas = crate::backend::bend::engine::Metas::default();
            for binder in &binders {
                metas.open(binder.id);
            }
            if self.engine.unify(&rest, goal, &mut metas) {
                break;
            }
        }
        let mut metas = crate::backend::bend::engine::Metas::default();
        for binder in &binders {
            metas.open(binder.id);
        }
        let target = if is_false(goal) { false_term() } else { goal.clone() };
        if !self.engine.unify(&rest, &target, &mut metas) {
            return Err(fail(
                "an `apply` step's conclusion does not match the goal in the Bend lowering",
            ));
        }
        let mut premises = Vec::new();
        let mut explicit = Vec::new();
        let mut map = BTreeMap::new();
        for binder in &binders {
            let ty = metas.zonk(&subst(&binder.ty, &map));
            let value = match metas.get(binder.id) {
                Some(solved) => metas.zonk(solved),
                None => {
                    let placeholder = self.engine.fresh.next();
                    let name = format!("llp{}", placeholder.0 - u64::MAX / 2);
                    self.engine.names.insert(placeholder, name);
                    premises.push((placeholder, ty.clone()));
                    Term::Local(placeholder)
                }
            };
            map.insert(binder.id, value.clone());
            if binder.mode == BinderMode::Explicit {
                explicit.push(value);
            }
        }
        let (head, mut given) = spine(function);
        given.extend(explicit);
        Ok((app(head.clone(), given), premises))
    }

    /// Lower an applied function whose premise placeholders are filled by
    /// proof terms.
    fn lower_applied(
        &mut self,
        ctx: &Ctx,
        applied: &Term,
        premises: &[(LocalId, Term, BTerm)],
        goal: &Term,
    ) -> Result<BTerm, Diagnostic> {
        let mut inner = ctx.clone();
        for (placeholder, premise_goal, proof) in premises {
            inner.push((*placeholder, premise_goal.clone()));
            self.inline.insert(*placeholder, proof.clone());
        }
        let expected = if is_false(goal) { None } else { Some(goal) };
        let lowered = self.engine.lower(&inner, applied, expected)?;
        let lowered = self.substitute_inline(lowered);
        for (placeholder, _, _) in premises {
            self.inline.remove(placeholder);
        }
        Ok(lowered)
    }
}

fn mark_reusable(pattern: Pattern, offsets: &[usize]) -> Pattern {
    let mark = |index: usize, name: Name| {
        if offsets.contains(&index) && !name.text.starts_with('+') {
            Name::new(format!("+{}", name.text), name.origin)
        } else {
            name
        }
    };
    match pattern {
        Pattern::Succ(name) => Pattern::Succ(mark(0, name)),
        Pattern::Pair(left, right) => Pattern::Pair(mark(0, left), mark(1, right)),
        Pattern::Constructor(head, fields) => Pattern::Constructor(
            head,
            fields
                .into_iter()
                .enumerate()
                .map(|(index, field)| mark(index, field))
                .collect(),
        ),
        Pattern::Zero => Pattern::Zero,
    }
}

fn app_type(head: &Term) -> Term {
    head.clone()
}

fn core_or_origin() -> Origin {
    Origin::Form {
        package: "lexlean.core".to_owned(),
        entry: "lor".to_owned(),
        form: "denotation".to_owned(),
    }
}

/// A body as a single term: a bare tail, or a parenthesized block.
#[must_use]
pub fn body_term(body: Body) -> BTerm {
    match (&body.tail, body.stmts.is_empty()) {
        (Tail::Term(term, _), true) => term.clone(),
        _ => BTerm::Block(Box::new(body)),
    }
}

fn substitute_names(term: BTerm, names: &BTreeMap<String, BTerm>) -> BTerm {
    let go = |inner: BTerm| substitute_names(inner, names);
    match term {
        BTerm::Name(name) => names.get(&name.text).cloned().unwrap_or(BTerm::Name(name)),
        BTerm::Call(head, args) => BTerm::Call(
            head,
            args.into_iter()
                .map(|(template, arg)| (template, go(arg)))
                .collect(),
        ),
        BTerm::Lam(name, body) => BTerm::Lam(name, Box::new(go(*body))),
        BTerm::Pi {
            name,
            erased,
            domain,
            codomain,
        } => BTerm::Pi {
            name,
            erased,
            domain: Box::new(go(*domain)),
            codomain: Box::new(go(*codomain)),
        },
        BTerm::Sigma {
            name,
            domain,
            codomain,
        } => BTerm::Sigma {
            name,
            domain: Box::new(go(*domain)),
            codomain: Box::new(go(*codomain)),
        },
        BTerm::Product(a, b) => BTerm::Product(Box::new(go(*a)), Box::new(go(*b))),
        BTerm::Datatype(head, quantities, args) => {
            BTerm::Datatype(head, quantities, args.into_iter().map(go).collect())
        }
        BTerm::Pair(a, b) => BTerm::Pair(Box::new(go(*a)), Box::new(go(*b))),
        BTerm::Constructor(head, fields) => {
            BTerm::Constructor(head, fields.into_iter().map(go).collect())
        }
        BTerm::Equal(a, b, t) => BTerm::Equal(Box::new(go(*a)), Box::new(go(*b)), Box::new(go(*t))),
        BTerm::Succ(inner) => BTerm::Succ(Box::new(go(*inner))),
        BTerm::Ann(a, b) => BTerm::Ann(Box::new(go(*a)), Box::new(go(*b))),
        other @ (BTerm::Refl | BTerm::Nat(_) | BTerm::Kind(_) | BTerm::Hole | BTerm::Block(_)) => other,
    }
}
