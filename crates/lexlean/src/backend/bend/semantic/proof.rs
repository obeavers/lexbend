//! Semantic proofs as explicit Bend proof terms.
//!
//! A theorem becomes a `law` whose `for` clauses are its type parameters,
//! its parameters, and the premises of its statement's leading
//! implications: a curried statement is the same proposition, and a Bend
//! `match` refines exactly the parameters after the one it inspects. Each
//! closed proof form has one fixed lowering:
//!
//! - `reflexivity` is `{==}`: both sides compute to one term;
//! - `decide` decides a closed proposition by computation: an equation or
//!   order is `{==}`, a conjunction a pair, and an implication with a false
//!   premise refutes that premise through `false = true`;
//! - `simplify` rewrites with the named hypotheses and theorems, left to
//!   right, wherever unfolding exposes an instance, then closes by `{==}`;
//!   named definitions need no step, since Bend unfolds them itself;
//! - `cases` is a `match` on the parameter; `induction` an auxiliary def
//!   matching its first parameter, whose recursive call on a structurally
//!   smaller field is the induction hypothesis;
//! - `constructor` pairs its branches; `apply` calls the cited law with the
//!   checked arguments and the premises it needs.

use std::collections::BTreeMap;

use super::normal::{self, Normalizer};
use super::{call, here, synthetic, var, Lower, Scope, HOLE};
use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Item, Name, Param, Quantity, Stmt, Tail};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{
    MemberRef, SemanticDeclaration, SemanticParameter, SemanticProof, SemanticTerm, SemanticType,
};
use crate::source::coverage::Origin;

/// A statement split into its leading universal binders, the premises of
/// its leading implications, and the claim after them.
pub struct Peeled {
    /// Universally bound locals after the declared parameters.
    pub binders: Vec<SemanticParameter>,
    /// The premises, in order.
    pub premises: Vec<SemanticTerm>,
    /// What remains.
    pub claim: SemanticTerm,
}

/// Peel a statement's leading universal binders and implications.
#[must_use]
pub fn peel(statement: &SemanticTerm) -> Peeled {
    let mut binders = Vec::new();
    let mut premises = Vec::new();
    let mut claim = statement.clone();
    loop {
        match claim {
            SemanticTerm::Forall { binder, body } if premises.is_empty() => {
                binders.push(binder);
                claim = *body;
            }
            SemanticTerm::Implies {
                premise,
                conclusion,
            } => {
                premises.push(*premise);
                claim = *conclusion;
            }
            other => {
                claim = other;
                break;
            }
        }
    }
    Peeled {
        binders,
        premises,
        claim,
    }
}

/// A rewrite rule: `lhs = rhs` for every instance of `vars`, proved by
/// calling `head` with `args`, where a `RuleArg::Var` is instantiated.
#[derive(Clone)]
struct Rule {
    vars: Vec<String>,
    lhs: SemanticTerm,
    rhs: SemanticTerm,
    head: String,
    args: Vec<RuleArg>,
}

#[derive(Clone)]
enum RuleArg {
    Fixed(BTerm),
    Var(String),
}

/// What a proof may use at one point: its locals, its premises as
/// `(Bend name, proposition)`, and the rules its hypotheses provide.
#[derive(Clone)]
struct Ctx {
    scope: Scope,
    premises: Vec<(String, SemanticTerm)>,
    rules: BTreeMap<String, Rule>,
}

fn reusable_marked(name: &str, data: bool) -> String {
    if data {
        format!("+{name}")
    } else {
        name.to_owned()
    }
}

/// Lower a theorem to its auxiliary definitions and its law.
///
/// # Errors
///
/// `LLB6008` when the proof has no Bend lowering.
pub fn theorem(
    lower: &mut Lower<'_, '_>,
    declaration: &SemanticDeclaration,
) -> Result<Vec<Item>, Diagnostic> {
    let SemanticDeclaration::Theorem {
        name,
        type_parameters,
        parameters,
        statement,
        proof,
        ..
    } = declaration
    else {
        return Err(fail("not a theorem"));
    };
    let spelled = super::names::global(name)?;
    let mut params = lower.type_params(type_parameters)?;
    let peeled = peel(statement);
    let all: Vec<SemanticParameter> = parameters.iter().chain(&peeled.binders).cloned().collect();
    let order: Vec<usize> = (0..all.len()).collect();
    let (values, scope) = lower.value_params(&all, &order)?;
    params.extend(values);
    let mut premises = Vec::new();
    for (index, premise) in peeled.premises.iter().enumerate() {
        let bend = format!("ll_h{index}");
        let ty = lower.term(premise, &scope)?;
        params.push(Param {
            quantity: if lower.prop_is_data(&ty) {
                Quantity::Reusable
            } else {
                Quantity::Affine
            },
            name: synthetic(bend.clone()),
            ty,
            source: here(),
        });
        premises.push((bend, premise.clone()));
    }
    let claim = lower.term(&peeled.claim, &scope)?;
    let mut ctx = Ctx {
        scope,
        premises,
        rules: BTreeMap::new(),
    };
    let mut prover = Prover {
        lower,
        owner: spelled.clone(),
        type_parameters: type_parameters.clone(),
        parameters: all,
        aux: Vec::new(),
        count: 0,
    };
    let body = prover.prove(&mut ctx, &peeled.claim, proof)?;
    let mut items = std::mem::take(&mut prover.aux);
    items.push(Item::Law {
        name: Name::new(
            spelled,
            Origin::Synthetic(super::super::syntax::SYNTAX_ORIGIN.to_owned()),
        ),
        params,
        claim,
        claim_source: here(),
        proof: body,
        source: here(),
    });
    Ok(items)
}

struct Prover<'x, 'p, 'a> {
    lower: &'x mut Lower<'p, 'a>,
    owner: String,
    type_parameters: Vec<String>,
    parameters: Vec<SemanticParameter>,
    aux: Vec<Item>,
    count: usize,
}

impl Prover<'_, '_, '_> {
    fn term_body(term: BTerm) -> Body {
        Body::term(term, here())
    }

    /// Prove `goal` by `proof` in `ctx`.
    #[allow(clippy::too_many_lines)]
    fn prove(
        &mut self,
        ctx: &mut Ctx,
        goal: &SemanticTerm,
        proof: &SemanticProof,
    ) -> Result<Body, Diagnostic> {
        // An implication left in the goal is introduced: its premise joins
        // the context, exactly as a tactic's `intro` does.
        if let SemanticTerm::Implies {
            premise,
            conclusion,
        } = goal
        {
            {
                let name = format!("ll_h{}", ctx.premises.len());
                let ty = self.lower.term(premise, &ctx.scope)?;
                let data = self.lower.prop_is_data(&ty);
                let mut inner = ctx.clone();
                inner.premises.push((name.clone(), (**premise).clone()));
                let body = self.prove(&mut inner, conclusion, proof)?;
                return Ok(Self::term_body(BTerm::Lam(
                    synthetic(reusable_marked(&name, data)),
                    Box::new(BTerm::Block(Box::new(body))),
                )));
            }
        }
        match proof {
            SemanticProof::Reflexivity => Ok(Self::term_body(BTerm::Refl)),
            SemanticProof::Decide => Ok(Self::term_body(self.decide(ctx, goal)?)),
            SemanticProof::Simplify { definitions } => self.simplify(ctx, goal, definitions),
            SemanticProof::Constructor { branches } => {
                let mut normalizer = Normalizer::new(self.lower);
                let unfolded = normalizer.normalize(goal);
                let parts: Vec<SemanticTerm> = match &unfolded {
                    SemanticTerm::PropAnd { left, right } => {
                        vec![(**left).clone(), (**right).clone()]
                    }
                    SemanticTerm::Iff { left, right } => vec![
                        SemanticTerm::Implies {
                            premise: left.clone(),
                            conclusion: right.clone(),
                        },
                        SemanticTerm::Implies {
                            premise: right.clone(),
                            conclusion: left.clone(),
                        },
                    ],
                    other => {
                        return Err(fail(format!(
                            "`constructor` needs a conjunction or equivalence, not `{other:?}`"
                        )))
                    }
                };
                if parts.len() != branches.len() {
                    return Err(fail("`constructor` has the wrong number of branches"));
                }
                let mut lowered = Vec::new();
                for (part, branch) in parts.iter().zip(branches) {
                    let body = self.prove(&mut ctx.clone(), part, branch)?;
                    lowered.push(BTerm::Block(Box::new(body)));
                }
                let right = lowered.pop().ok_or_else(|| fail("no branch"))?;
                let left = lowered.pop().ok_or_else(|| fail("no branch"))?;
                Ok(Self::term_body(BTerm::Pair(
                    Box::new(left),
                    Box::new(right),
                )))
            }
            SemanticProof::Cases {
                scrutinee,
                branches,
            } => self.cases(ctx, goal, scrutinee, branches),
            SemanticProof::Induction {
                scrutinee,
                generalizing,
                branches,
            } => self.induction(ctx, goal, scrutinee, generalizing, branches),
            SemanticProof::Apply {
                theorem,
                type_arguments,
                arguments,
            } => Ok(Self::term_body(self.apply(
                ctx,
                theorem,
                type_arguments,
                arguments,
            )?)),
            SemanticProof::LinearArithmetic { .. } => Err(fail(
                "`linear_arithmetic` has no Bend lowering in this build of language 2.2",
            )),
            SemanticProof::Congruence => Err(fail(
                "`congruence` has no Bend lowering in this build of language 2.2",
            )),
            SemanticProof::BooleanReflection { .. } => Err(fail(
                "`boolean_reflection` has no Bend lowering in this build of language 2.2",
            )),
        }
    }

    /// Decide a closed proposition by computation.
    fn decide(&mut self, ctx: &Ctx, goal: &SemanticTerm) -> Result<BTerm, Diagnostic> {
        let mut normalizer = Normalizer::new(self.lower);
        let unfolded = normalizer.normalize(goal);
        match &unfolded {
            SemanticTerm::Eq { .. } | SemanticTerm::Le { .. } | SemanticTerm::Lt { .. } => {
                // The goal as stated, not as unfolded: Bend unfolds it.
                Ok(BTerm::Refl)
            }
            SemanticTerm::PropAnd { left, right } => Ok(BTerm::Pair(
                Box::new(self.decide(ctx, left)?),
                Box::new(self.decide(ctx, right)?),
            )),
            SemanticTerm::Iff { left, right } => {
                let forward = SemanticTerm::Implies {
                    premise: left.clone(),
                    conclusion: right.clone(),
                };
                let backward = SemanticTerm::Implies {
                    premise: right.clone(),
                    conclusion: left.clone(),
                };
                Ok(BTerm::Pair(
                    Box::new(self.decide(ctx, &forward)?),
                    Box::new(self.decide(ctx, &backward)?),
                ))
            }
            SemanticTerm::Implies {
                premise,
                conclusion,
            } => {
                let name = self.lower.fresh("h");
                let holds = Normalizer::new(self.lower).truth(premise);
                let body = if holds == Some(false) {
                    self.refute(ctx, premise, &name, conclusion)?
                } else {
                    self.decide(ctx, conclusion)?
                };
                Ok(BTerm::Lam(synthetic(name), Box::new(body)))
            }
            other => Err(fail(format!(
                "`decide` has no Bend lowering for the proposition `{other:?}`"
            ))),
        }
    }

    /// From `name : premise`, a closed false proposition, a proof of
    /// `conclusion`.
    fn refute(
        &mut self,
        ctx: &Ctx,
        premise: &SemanticTerm,
        name: &str,
        conclusion: &SemanticTerm,
    ) -> Result<BTerm, Diagnostic> {
        let target = self.lower.term(conclusion, &ctx.scope)?;
        let absurd = self.lower.support("false_ne_true");
        let unfolded = Normalizer::new(self.lower).normalize(premise);
        let clash = match &unfolded {
            // An order is `ble a b = true`; false, it is `false = true`.
            SemanticTerm::Le { .. } | SemanticTerm::Lt { .. } => var(name),
            SemanticTerm::Eq { left, right } => {
                let ty = self.lower.infer(left, &ctx.scope)?;
                match (&ty, left.as_ref(), right.as_ref()) {
                    (SemanticType::Bool, SemanticTerm::Bool { value: false }, _) => var(name),
                    (SemanticType::Bool, SemanticTerm::Bool { value: true }, _) => call(
                        "Equal.sym",
                        vec![
                            var("Bool"),
                            BTerm::Constructor(synthetic("True"), Vec::new()),
                            BTerm::Constructor(synthetic("False"), Vec::new()),
                            var(name),
                        ],
                    ),
                    (SemanticType::Nat, _, _) => {
                        // `beq x r` sends `l` to false and `r` to true.
                        let right_term = self.lower.term(premise_right(premise), &ctx.scope)?;
                        let left_term = self.lower.term(premise_left(premise), &ctx.scope)?;
                        let beq = self.lower.prelude("Lean.Nat.beq");
                        call(
                            "Equal.cong",
                            vec![
                                var("Nat"),
                                var("Bool"),
                                BTerm::Lam(
                                    synthetic("ll_x"),
                                    Box::new(call(beq, vec![var("ll_x"), right_term.clone()])),
                                ),
                                left_term,
                                right_term,
                                var(name),
                            ],
                        )
                    }
                    _ => {
                        return Err(fail(format!(
                            "`decide` cannot refute a false equation over `{ty:?}`"
                        )))
                    }
                }
            }
            other => {
                return Err(fail(format!(
                    "`decide` cannot refute the false premise `{other:?}`"
                )))
            }
        };
        Ok(call(absurd, vec![target, clash]))
    }

    /// Rules for every name a `simplify` lists that is a hypothesis or a
    /// theorem; a definition needs none.
    fn rules_for(&mut self, ctx: &Ctx, definitions: &[MemberRef]) -> Result<Vec<Rule>, Diagnostic> {
        let mut rules = Vec::new();
        for member in definitions {
            if member.module.is_none() {
                if let Some(rule) = ctx.rules.get(&member.name) {
                    rules.push(rule.clone());
                    continue;
                }
            }
            let Ok(declaration) = self.lower.declaration(member) else {
                continue;
            };
            if let SemanticDeclaration::Theorem {
                type_parameters,
                parameters,
                statement,
                ..
            } = declaration
            {
                let home = self.lower.home(member);
                let peeled = peel(&normal::qualify_term(statement, &home));
                if !peeled.premises.is_empty() || !type_parameters.is_empty() {
                    continue;
                }
                let SemanticTerm::Eq { left, right } = peeled.claim else {
                    continue;
                };
                let vars: Vec<String> = parameters
                    .iter()
                    .chain(&peeled.binders)
                    .map(|p| p.name.clone())
                    .collect();
                rules.push(Rule {
                    vars: vars.clone(),
                    lhs: *left,
                    rhs: *right,
                    head: self.lower.member(member)?,
                    args: vars.into_iter().map(RuleArg::Var).collect(),
                });
            }
        }
        Ok(rules)
    }

    fn simplify(
        &mut self,
        ctx: &Ctx,
        goal: &SemanticTerm,
        definitions: &[MemberRef],
    ) -> Result<Body, Diagnostic> {
        let rules = self.rules_for(ctx, definitions)?;
        // The normalized goal names every member by its module, so a rule
        // read from this module must too before it can match.
        // Its arguments are normalized as the goal's are, but not its head,
        // which would unfold the very call the rule rewrites.
        let module = self.lower.module.clone();
        let rules: Vec<Rule> = rules
            .into_iter()
            .map(|rule| {
                let mut lhs = normal::qualify_term(&rule.lhs, &module);
                let mut normalizer = Normalizer::new(self.lower);
                normal::map_children(&mut lhs, &mut |child| *child = normalizer.normalize(child));
                Rule {
                    lhs,
                    rhs: normal::qualify_term(&rule.rhs, &module),
                    ..rule
                }
            })
            .collect();
        let mut current = Normalizer::new(self.lower).normalize(goal);
        let mut stmts = Vec::new();
        for _ in 0..64 {
            let mut found = None;
            'search: for rule in &rules {
                let mut occurrences = Vec::new();
                normal::subterms(&current, &mut Vec::new(), &mut occurrences);
                for (path, subterm) in occurrences {
                    let mut binding = BTreeMap::new();
                    if matches(&rule.lhs, &subterm, &rule.vars, &mut binding)
                        && rule.vars.iter().all(|v| binding.contains_key(v))
                    {
                        found = Some((rule.clone(), path, binding));
                        break 'search;
                    }
                }
            }
            let Some((rule, path, binding)) = found else {
                break;
            };
            let lhs = normal::substitute_all(&rule.lhs, &binding);
            let rhs = normal::substitute_all(&rule.rhs, &binding);
            let motive = normal::replace_at(
                &current,
                &path,
                &SemanticTerm::Var {
                    name: HOLE.to_owned(),
                },
            );
            let ty = self.lower.infer(&lhs, &ctx.scope)?;
            let mut args = Vec::new();
            for arg in &rule.args {
                args.push(match arg {
                    RuleArg::Fixed(term) => term.clone(),
                    RuleArg::Var(name) => {
                        let value = binding
                            .get(name)
                            .ok_or_else(|| fail("a rule variable is unbound"))?;
                        self.lower.term(value, &ctx.scope)?
                    }
                });
            }
            let equation = call(rule.head.clone(), args);
            let flipped = call(
                "Equal.sym",
                vec![
                    self.lower.ty(&ty)?,
                    self.lower.term(&lhs, &ctx.scope)?,
                    self.lower.term(&rhs, &ctx.scope)?,
                    equation,
                ],
            );
            stmts.push(Stmt::Rewrite {
                proof: flipped,
                motive: self.lower.term(&motive, &ctx.scope)?,
                source: here(),
            });
            let rewritten = normal::replace_at(&current, &path, &rhs);
            current = Normalizer::new(self.lower).normalize(&rewritten);
        }
        Ok(Body {
            stmts,
            tail: Tail::Term(BTerm::Refl, here()),
        })
    }

    /// The type of a local the proof splits.
    fn local_type(ctx: &Ctx, name: &str) -> Result<(String, SemanticType), Diagnostic> {
        ctx.scope.get(name).cloned()
    }

    /// The value a proof branch's constructor builds from its binders.
    fn branch_value(
        &self,
        ty: &SemanticType,
        constructor: &MemberRef,
        binders: &[String],
    ) -> SemanticTerm {
        let vars: Vec<SemanticTerm> = binders
            .iter()
            .map(|b| SemanticTerm::Var { name: b.clone() })
            .collect();
        let arguments = match ty {
            SemanticType::Option { value } => vec![(**value).clone()],
            SemanticType::Result { ok, error } => vec![(**ok).clone(), (**error).clone()],
            SemanticType::List { element } => vec![(**element).clone()],
            SemanticType::Product { left, right } => vec![(**left).clone(), (**right).clone()],
            SemanticType::Named { arguments, .. } => arguments.clone(),
            _ => Vec::new(),
        };
        match (ty, constructor.name.as_str()) {
            (SemanticType::Nat, "Nat.zero") => SemanticTerm::Nat {
                value: "0".to_owned(),
            },
            (SemanticType::Bool, "Bool.true") => SemanticTerm::Bool { value: true },
            (SemanticType::Bool, "Bool.false") => SemanticTerm::Bool { value: false },
            (SemanticType::List { element }, "List.nil") => SemanticTerm::Nil {
                element: (**element).clone(),
            },
            (SemanticType::List { .. }, "List.cons") if vars.len() >= 2 => SemanticTerm::Cons {
                head: Box::new(vars[0].clone()),
                tail: Box::new(vars[1].clone()),
            },
            (SemanticType::Product { .. }, _) if vars.len() >= 2 => SemanticTerm::Pair {
                left: Box::new(vars[0].clone()),
                right: Box::new(vars[1].clone()),
            },
            _ => SemanticTerm::Constructor {
                constructor: constructor.clone(),
                type_arguments: arguments,
                arguments: vars,
            },
        }
    }

    fn cases(
        &mut self,
        ctx: &Ctx,
        goal: &SemanticTerm,
        scrutinee: &str,
        branches: &[crate::ir::semantic::SemanticProofBranch],
    ) -> Result<Body, Diagnostic> {
        let (bend, ty) = Self::local_type(ctx, scrutinee)?;
        let mut cases = Vec::new();
        for branch in branches {
            let constructor = self.lower.branch_constructor(&ty, &branch.constructor);
            let fields = self.lower.pattern_fields(&ty, &constructor)?;
            let field_count = fields.len();
            let pattern = self.lower.pattern(
                &ty,
                &constructor,
                &branch.binders[..field_count.min(branch.binders.len())],
            )?;
            let mut inner = ctx.clone();
            for (binder, field) in branch.binders.iter().zip(&fields) {
                inner.scope = inner.scope.with(binder, field.clone())?;
            }
            let value = self.branch_value(&ty, &constructor, &branch.binders);
            let goal = normal::substitute(goal, scrutinee, &value);
            for premise in &mut inner.premises {
                premise.1 = normal::substitute(&premise.1, scrutinee, &value);
            }
            let body = self.prove(&mut inner, &goal, &branch.proof)?;
            cases.push((pattern, body));
        }
        Ok(Body {
            stmts: Vec::new(),
            tail: Tail::Match {
                scrutinee: synthetic(bend),
                cases,
                source: here(),
            },
        })
    }

    /// The positions of a constructor's fields that are structurally
    /// smaller values of the split type.
    fn recursive_fields(
        ty: &SemanticType,
        constructor: &MemberRef,
        fields: &[SemanticType],
    ) -> Vec<usize> {
        match (ty, constructor.name.as_str()) {
            (SemanticType::Nat, "Nat.succ") => vec![0],
            (SemanticType::List { .. }, "List.cons") => vec![1],
            (SemanticType::Named { .. }, _) => fields
                .iter()
                .enumerate()
                .filter(|(_, field)| *field == ty)
                .map(|(index, _)| index)
                .collect(),
            _ => Vec::new(),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn induction(
        &mut self,
        ctx: &Ctx,
        goal: &SemanticTerm,
        scrutinee: &str,
        generalizing: &[String],
        branches: &[crate::ir::semantic::SemanticProofBranch],
    ) -> Result<Body, Diagnostic> {
        self.count += 1;
        let aux = format!("{}.ll_ind{}", self.owner, self.count);
        let (_, scrutinee_type) = Self::local_type(ctx, scrutinee)?;
        // The auxiliary takes the split value first, then every other
        // parameter, then the premises.
        let mut order: Vec<SemanticParameter> = Vec::new();
        order.push(SemanticParameter {
            name: scrutinee.to_owned(),
            r#type: scrutinee_type.clone(),
        });
        for parameter in &self.parameters {
            if parameter.name != scrutinee && ctx.scope.locals.contains_key(&parameter.name) {
                let (_, ty) = Self::local_type(ctx, &parameter.name)?;
                order.push(SemanticParameter {
                    name: parameter.name.clone(),
                    r#type: ty,
                });
            }
        }
        let mut params = Vec::new();
        for type_parameter in &self.type_parameters {
            params.push(Param {
                quantity: Quantity::Template,
                name: synthetic(super::names::local(type_parameter)?),
                ty: BTerm::Kind("Data"),
                source: here(),
            });
        }
        let mut scope = Scope::default();
        for parameter in &order {
            scope = scope.with(&parameter.name, parameter.r#type.clone())?;
            let bend = scope.get(&parameter.name)?.0.clone();
            params.push(self.lower.param(&bend, &parameter.r#type)?);
        }
        for (name, premise) in &ctx.premises {
            let ty = self.lower.term(premise, &scope)?;
            params.push(Param {
                quantity: if self.lower.prop_is_data(&ty) {
                    Quantity::Reusable
                } else {
                    Quantity::Affine
                },
                name: synthetic(name.clone()),
                ty,
                source: here(),
            });
        }
        let result = self.lower.term(goal, &scope)?;
        let (scrutinee_bend, _) = scope.get(scrutinee)?.clone();
        let type_args: Vec<BTerm> = self
            .type_parameters
            .iter()
            .map(|p| super::names::local(p).map(|t| BTerm::Template(Box::new(var(t)))))
            .collect::<Result<_, _>>()?;
        let mut cases = Vec::new();
        for branch in branches {
            let constructor = self
                .lower
                .branch_constructor(&scrutinee_type, &branch.constructor);
            let fields = self.lower.pattern_fields(&scrutinee_type, &constructor)?;
            let recursive = Self::recursive_fields(&scrutinee_type, &constructor, &fields);
            let field_binders = &branch.binders[..fields.len().min(branch.binders.len())];
            let hypotheses = &branch.binders[field_binders.len()..];
            let pattern = self
                .lower
                .pattern(&scrutinee_type, &constructor, field_binders)?;
            let mut inner = Ctx {
                scope: scope.clone(),
                premises: ctx.premises.clone(),
                rules: ctx.rules.clone(),
            };
            for (binder, field) in field_binders.iter().zip(&fields) {
                inner.scope = inner.scope.with(binder, field.clone())?;
            }
            let value = self.branch_value(&scrutinee_type, &constructor, field_binders);
            let branch_goal = normal::substitute(goal, scrutinee, &value);
            for premise in &mut inner.premises {
                premise.1 = normal::substitute(&premise.1, scrutinee, &value);
            }
            // Each hypothesis is the goal at one smaller field, proved by
            // the recursive call; a generalized parameter stays a rule
            // variable, instantiated where the rule is used.
            for (hypothesis, position) in hypotheses.iter().zip(&recursive) {
                let field = &field_binders[*position];
                let at_field = normal::substitute(
                    goal,
                    scrutinee,
                    &SemanticTerm::Var {
                        name: field.clone(),
                    },
                );
                let mut args: Vec<RuleArg> =
                    type_args.iter().cloned().map(RuleArg::Fixed).collect();
                args.push(RuleArg::Fixed(var(inner.scope.get(field)?.0.clone())));
                let mut vars = Vec::new();
                for parameter in order.iter().skip(1) {
                    if generalizing.contains(&parameter.name) {
                        vars.push(parameter.name.clone());
                        args.push(RuleArg::Var(parameter.name.clone()));
                    } else {
                        args.push(RuleArg::Fixed(var(scope.get(&parameter.name)?.0.clone())));
                    }
                }
                if !ctx.premises.is_empty() {
                    return Err(fail(
                        "an induction hypothesis under premises has no Bend lowering in language 2.2",
                    ));
                }
                if let SemanticTerm::Eq { left, right } = &at_field {
                    inner.rules.insert(
                        hypothesis.clone(),
                        Rule {
                            vars,
                            lhs: (**left).clone(),
                            rhs: (**right).clone(),
                            head: aux.clone(),
                            args,
                        },
                    );
                }
            }
            let body = self.prove(&mut inner, &branch_goal, &branch.proof)?;
            cases.push((pattern, body));
        }
        self.aux.push(Item::Def {
            name: synthetic(aux.clone()),
            params,
            result,
            result_source: here(),
            body: Body {
                stmts: Vec::new(),
                tail: Tail::Match {
                    scrutinee: synthetic(scrutinee_bend),
                    cases,
                    source: here(),
                },
            },
            source: here(),
        });
        let mut args = type_args;
        for parameter in &order {
            args.push(var(ctx.scope.get(&parameter.name)?.0.clone()));
        }
        for (name, _) in &ctx.premises {
            args.push(var(name.clone()));
        }
        Ok(Self::term_body(call(aux, args)))
    }

    fn apply(
        &mut self,
        ctx: &Ctx,
        theorem: &MemberRef,
        type_arguments: &[SemanticType],
        arguments: &[SemanticTerm],
    ) -> Result<BTerm, Diagnostic> {
        let SemanticDeclaration::Theorem {
            type_parameters,
            parameters,
            statement,
            ..
        } = self.lower.declaration(theorem)?
        else {
            return Err(fail(format!("`{}` is not a theorem", theorem.name)));
        };
        let home = self.lower.home(theorem);
        let peeled = peel(&normal::qualify_term(statement, &home));
        let lowered = arguments
            .iter()
            .map(|argument| self.lower.term(argument, &ctx.scope))
            .collect::<Result<Vec<_>, _>>()?;
        let type_arguments: Vec<SemanticType> = type_arguments
            .iter()
            .map(|t| self.lower.canonical(t))
            .collect();
        let BTerm::Call(head, mut args) = self.lower.call_of(theorem, &type_arguments, lowered)?
        else {
            return Err(fail("a law call did not lower to a call"));
        };
        // The cited premises, instantiated, must each be a premise here.
        let mut map = BTreeMap::new();
        for (parameter, argument) in parameters.iter().chain(&peeled.binders).zip(arguments) {
            map.insert(parameter.name.clone(), argument.clone());
        }
        let _ = type_parameters;
        for premise in &peeled.premises {
            let wanted =
                Normalizer::new(self.lower).normalize(&normal::substitute_all(premise, &map));
            let found = ctx
                .premises
                .iter()
                .find(|(_, have)| Normalizer::new(self.lower).normalize(have) == wanted);
            match found {
                Some((name, _)) => args.push(var(name.clone())),
                None => {
                    return Err(fail(format!(
                        "`apply {}` needs a premise this goal does not have",
                        theorem.name
                    )))
                }
            }
        }
        Ok(BTerm::Call(head, args))
    }
}

fn premise_left(premise: &SemanticTerm) -> &SemanticTerm {
    match premise {
        SemanticTerm::Eq { left, .. } => left,
        other => other,
    }
}

fn premise_right(premise: &SemanticTerm) -> &SemanticTerm {
    match premise {
        SemanticTerm::Eq { right, .. } => right,
        other => other,
    }
}

/// Match `pattern` against `term`, binding the pattern's `vars`.
fn matches(
    pattern: &SemanticTerm,
    term: &SemanticTerm,
    vars: &[String],
    binding: &mut BTreeMap<String, SemanticTerm>,
) -> bool {
    if let SemanticTerm::Var { name } = pattern {
        if vars.contains(name) {
            return match binding.get(name) {
                Some(bound) => bound == term,
                None => {
                    binding.insert(name.clone(), term.clone());
                    true
                }
            };
        }
    }
    let same_shape = std::mem::discriminant(pattern) == std::mem::discriminant(term);
    if !same_shape {
        return false;
    }
    let (left, right) = (normal::children(pattern), normal::children(term));
    if left.len() != right.len() {
        return false;
    }
    if left.is_empty() {
        return pattern == term;
    }
    // The non-term parts must agree too (the callee, the constructor).
    let mut stripped_pattern = pattern.clone();
    let mut stripped_term = term.clone();
    normal::map_children(&mut stripped_pattern, &mut |c| *c = SemanticTerm::Unit);
    normal::map_children(&mut stripped_term, &mut |c| *c = SemanticTerm::Unit);
    if stripped_pattern != stripped_term {
        return false;
    }
    left.iter()
        .zip(&right)
        .all(|(p, t)| matches(p, t, vars, binding))
}
