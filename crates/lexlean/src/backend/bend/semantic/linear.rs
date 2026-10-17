//! `linear_arithmetic` by reflection over `LinArith.bend`.
//!
//! Lean closes the step with `omega`. Here the goal and the premises, as
//! normalized (so the definitions the step lists are unfolded), are reified
//! into `LinArith`'s syntax over an environment of `Nat` atoms: every
//! maximal subterm that is not a numeral, a sum, or a product with a numeral
//! is one atom, and a truncated subtraction is an atom whose defining fact
//! `t = a - b` is supplied with proof `{==}`. A certificate is searched for
//! in Rust and the proof is one application of the law `sound`; Bend checks
//! the certificate by computation, so a wrong one is refused, never
//! believed. The reified goal denotes the Bend statement definitionally, as
//! `LinArith`'s constructors denote the prelude's own operations.

use crate::backend::bend::engine::fail;
use crate::backend::bend::linarith::{self, BExp, Fact, Problem, Term};
use crate::backend::bend::syntax::{BTerm, Body, Stmt, Tail};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{SemanticPrimitive, SemanticTerm, SemanticType};

use super::support::Support;
use super::{Lower, Scope};

/// The atoms of one obligation, in environment order, and the defining
/// facts of the subtraction atoms.
struct Reifier<'x, 'p, 'a> {
    lower: &'x mut Lower<'p, 'a>,
    scope: &'x Scope,
    atoms: Vec<SemanticTerm>,
    subtractions: Vec<Fact>,
}

impl Reifier<'_, '_, '_> {
    fn atom(&mut self, term: &SemanticTerm) -> Term {
        let index = match self.atoms.iter().position(|atom| atom == term) {
            Some(index) => index,
            None => {
                self.atoms.push(term.clone());
                self.atoms.len() - 1
            }
        };
        Term::Var(u32::try_from(index).unwrap_or(u32::MAX))
    }

    fn literal(term: &SemanticTerm) -> Option<u32> {
        match term {
            SemanticTerm::Nat { value } => value.parse().ok(),
            _ => None,
        }
    }

    fn term(&mut self, term: &SemanticTerm) -> Result<Term, Diagnostic> {
        Ok(match term {
            SemanticTerm::Nat { value } => Term::Lit(value.parse().map_err(|_| {
                fail(format!(
                    "the numeral {value} exceeds what `linear_arithmetic` reifies in Bend"
                ))
            })?),
            SemanticTerm::Add { left, right } => Term::plus(self.term(left)?, self.term(right)?),
            SemanticTerm::Primitive {
                operation: SemanticPrimitive::Multiply,
                arguments,
                result: SemanticType::Nat,
            } if arguments.len() == 2 => {
                if let Some(k) = Self::literal(&arguments[0]) {
                    Term::MulL(k, Box::new(self.term(&arguments[1])?))
                } else if let Some(k) = Self::literal(&arguments[1]) {
                    Term::MulR(Box::new(self.term(&arguments[0])?), k)
                } else {
                    self.atom(term)
                }
            }
            SemanticTerm::Primitive {
                operation: SemanticPrimitive::Subtract,
                arguments,
                result: SemanticType::Nat,
            } if arguments.len() == 2 => {
                let fresh = !self.atoms.contains(term);
                let atom = self.atom(term);
                if fresh {
                    let (a, b) = (self.term(&arguments[0])?, self.term(&arguments[1])?);
                    self.subtractions.push(Fact::Sub {
                        t: atom.clone(),
                        a,
                        b,
                    });
                }
                atom
            }
            _ => self.atom(term),
        })
    }

    fn boolean(&mut self, term: &SemanticTerm) -> Result<Option<BExp>, Diagnostic> {
        Ok(Some(match term {
            SemanticTerm::Ble { left, right } => BExp::Le(self.term(left)?, self.term(right)?),
            SemanticTerm::Blt { left, right } => BExp::Lt(self.term(left)?, self.term(right)?),
            SemanticTerm::Beq { left, right } if self.is_nat(left)? => {
                BExp::Eq(self.term(left)?, self.term(right)?)
            }
            SemanticTerm::And { left, right } => {
                match (self.boolean(left)?, self.boolean(right)?) {
                    (Some(a), Some(b)) => BExp::And(Box::new(a), Box::new(b)),
                    _ => return Ok(None),
                }
            }
            SemanticTerm::Or { left, right } => match (self.boolean(left)?, self.boolean(right)?) {
                (Some(a), Some(b)) => BExp::Or(Box::new(a), Box::new(b)),
                _ => return Ok(None),
            },
            SemanticTerm::Not { value } => match self.boolean(value)? {
                Some(a) => BExp::Not(Box::new(a)),
                None => return Ok(None),
            },
            _ => return Ok(None),
        }))
    }

    fn is_nat(&mut self, term: &SemanticTerm) -> Result<bool, Diagnostic> {
        let ty = self.lower.infer(term, self.scope)?;
        Ok(self.lower.canonical(&ty) == SemanticType::Nat)
    }

    /// `some x = some y` over `Nat` as `x = y`, with its proof from the
    /// premise's.
    fn injective(
        &mut self,
        premise: &SemanticTerm,
        proof: BTerm,
    ) -> Result<Option<(Fact, BTerm)>, Diagnostic> {
        let SemanticTerm::Eq { left, right } = premise else {
            return Ok(None);
        };
        let (
            SemanticTerm::Constructor {
                constructor: some_left,
                arguments: left_arguments,
                ..
            },
            SemanticTerm::Constructor {
                constructor: some_right,
                arguments: right_arguments,
                ..
            },
        ) = (left.as_ref(), right.as_ref())
        else {
            return Ok(None);
        };
        let is_some = |member: &crate::ir::semantic::MemberRef| {
            member.module.is_none() && member.name == "Option.some"
        };
        let ([x], [y]) = (left_arguments.as_slice(), right_arguments.as_slice()) else {
            return Ok(None);
        };
        if !is_some(some_left) || !is_some(some_right) || !self.is_nat(x)? {
            return Ok(None);
        }
        let fact = Fact::Eq(self.term(x)?, self.term(y)?);
        let (x, y) = (
            self.lower.term(x, self.scope)?,
            self.lower.term(y, self.scope)?,
        );
        let head = self.lower.support("some_inj");
        Ok(Some((
            fact,
            super::call(head, vec![super::var("Nat"), x, y, proof]),
        )))
    }

    /// A proposition, or `None` when it is outside linear arithmetic.
    fn fact(&mut self, term: &SemanticTerm) -> Result<Option<Fact>, Diagnostic> {
        Ok(Some(match term {
            SemanticTerm::Le { left, right } if self.is_nat(left)? => {
                Fact::Le(self.term(left)?, self.term(right)?)
            }
            SemanticTerm::Lt { left, right } if self.is_nat(left)? => {
                Fact::Lt(self.term(left)?, self.term(right)?)
            }
            SemanticTerm::Eq { left, right } if self.is_nat(left)? => {
                Fact::Eq(self.term(left)?, self.term(right)?)
            }
            SemanticTerm::Eq { left, right } => {
                let (expression, value) = match (left.as_ref(), right.as_ref()) {
                    (expression, SemanticTerm::Bool { value }) => (expression, *value),
                    (SemanticTerm::Bool { value }, expression) => (expression, *value),
                    _ => return Ok(None),
                };
                match self.boolean(expression)? {
                    Some(expression) => Fact::Is(expression, value),
                    None => return Ok(None),
                }
            }
            SemanticTerm::PropAnd { left, right } => match (self.fact(left)?, self.fact(right)?) {
                (Some(a), Some(b)) => Fact::And(Box::new(a), Box::new(b)),
                _ => return Ok(None),
            },
            SemanticTerm::Implies {
                premise,
                conclusion,
            } => match (self.fact(premise)?, self.fact(conclusion)?) {
                (Some(a), Some(b)) => Fact::Imp(Box::new(a), Box::new(b)),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        }))
    }
}

/// A premise's proof as `LinArith` reads it. `holds` reads every
/// conjunction as an `&` pair; the semantic lowering pairs a conjunction of
/// `Data` propositions as `Lean.Prod`, so a premise holding one, at any
/// depth below conjunctions and implication conclusions, is rebuilt
/// component by component.
fn conjunction(
    lower: &mut Lower<'_, '_>,
    scope: &Scope,
    premise: &SemanticTerm,
    proof: BTerm,
) -> Result<BTerm, Diagnostic> {
    if !reshaped(lower, scope, premise)? {
        return Ok(proof);
    }
    match premise {
        SemanticTerm::PropAnd { left, right } => {
            let (left_type, right_type) = (lower.term(left, scope)?, lower.term(right, scope)?);
            if lower.prop_is_data(&left_type) && lower.prop_is_data(&right_type) {
                // Both projections read the pair, so a computed one is
                // shared first, at its `Data` type.
                let (stmts, pair) = if matches!(proof, BTerm::Name(_)) {
                    (Vec::new(), proof)
                } else {
                    let name = lower.fresh("c");
                    let ty = super::call(
                        lower.prelude("Lean.Prod"),
                        vec![left_type.clone(), right_type.clone()],
                    );
                    let share = Stmt::Share {
                        name: super::synthetic(name.clone()),
                        value: BTerm::Ann(Box::new(proof), Box::new(ty)),
                        source: super::here(),
                    };
                    (vec![share], super::var(name))
                };
                let first = lower.support("fst");
                let second = lower.support("snd");
                let left_proof = super::call(
                    first,
                    vec![left_type.clone(), right_type.clone(), pair.clone()],
                );
                let right_proof = super::call(second, vec![left_type, right_type, pair]);
                let rebuilt = BTerm::Pair(
                    Box::new(conjunction(lower, scope, left, left_proof)?),
                    Box::new(conjunction(lower, scope, right, right_proof)?),
                );
                return Ok(if stmts.is_empty() {
                    rebuilt
                } else {
                    BTerm::Block(Box::new(Body {
                        stmts,
                        tail: Tail::Term(rebuilt, super::here()),
                    }))
                });
            }
            let mut arguments = vec![
                left_type.clone(),
                right_type.clone(),
                holds_type(lower, scope, left)?,
                holds_type(lower, scope, right)?,
            ];
            for (side, ty) in [(left, &left_type), (right, &right_type)] {
                let name = lower.fresh("c");
                let body = conjunction(lower, scope, side, super::var(name.clone()))?;
                let binder = if lower.prop_is_data(ty) {
                    format!("+{name}")
                } else {
                    name
                };
                arguments.push(BTerm::Lam(super::synthetic(binder), Box::new(body)));
            }
            arguments.push(proof);
            Ok(super::call(lower.support("and_map"), arguments))
        }
        SemanticTerm::Implies {
            premise: assumed,
            conclusion,
        } => {
            // `unconjunction` uses the proof it rebuilds once, so the
            // binder is affine, as Bend requires of one whose type it sees
            // only through `holds`.
            let name = lower.fresh("c");
            let given = unconjunction(lower, scope, assumed, super::var(name.clone()))?;
            let applied = BTerm::Apply(Box::new(proof), vec![given]);
            let body = conjunction(lower, scope, conclusion, applied)?;
            Ok(BTerm::Lam(super::synthetic(name), Box::new(body)))
        }
        _ => Ok(proof),
    }
}

/// The inverse of `conjunction`: a proof as `holds` reads it, as the
/// semantic lowering states the premise.
fn unconjunction(
    lower: &mut Lower<'_, '_>,
    scope: &Scope,
    premise: &SemanticTerm,
    proof: BTerm,
) -> Result<BTerm, Diagnostic> {
    if !reshaped(lower, scope, premise)? {
        return Ok(proof);
    }
    match premise {
        SemanticTerm::PropAnd { left, right } => {
            let (left_type, right_type) = (lower.term(left, scope)?, lower.term(right, scope)?);
            let data = lower.prop_is_data(&left_type) && lower.prop_is_data(&right_type);
            let mut arguments = vec![
                holds_type(lower, scope, left)?,
                holds_type(lower, scope, right)?,
                left_type,
                right_type,
            ];
            for side in [left, right] {
                let name = lower.fresh("c");
                let body = unconjunction(lower, scope, side, super::var(name.clone()))?;
                arguments.push(BTerm::Lam(super::synthetic(name), Box::new(body)));
            }
            arguments.push(proof);
            let head = if data { "and_prod" } else { "and_map" };
            Ok(super::call(lower.support(head), arguments))
        }
        SemanticTerm::Implies {
            premise: assumed,
            conclusion,
        } => {
            let name = lower.fresh("c");
            let assumed_type = lower.term(assumed, scope)?;
            let given = conjunction(lower, scope, assumed, super::var(name.clone()))?;
            let applied = BTerm::Apply(Box::new(proof), vec![given]);
            let body = unconjunction(lower, scope, conclusion, applied)?;
            let binder = if lower.prop_is_data(&assumed_type) {
                format!("+{name}")
            } else {
                name
            };
            Ok(BTerm::Lam(super::synthetic(binder), Box::new(body)))
        }
        _ => Ok(proof),
    }
}

/// Whether a premise's lowering differs from what `holds` reads: it holds
/// a conjunction of `Data` propositions below conjunctions and implications.
fn reshaped(
    lower: &mut Lower<'_, '_>,
    scope: &Scope,
    premise: &SemanticTerm,
) -> Result<bool, Diagnostic> {
    Ok(match premise {
        SemanticTerm::PropAnd { left, right } => {
            let (left_type, right_type) = (lower.term(left, scope)?, lower.term(right, scope)?);
            (lower.prop_is_data(&left_type) && lower.prop_is_data(&right_type))
                || reshaped(lower, scope, left)?
                || reshaped(lower, scope, right)?
        }
        SemanticTerm::Implies {
            premise,
            conclusion,
        } => reshaped(lower, scope, premise)? || reshaped(lower, scope, conclusion)?,
        _ => false,
    })
}

/// The type `holds` gives a premise: its lowering with every conjunction an
/// `&` pair.
fn holds_type(
    lower: &mut Lower<'_, '_>,
    scope: &Scope,
    premise: &SemanticTerm,
) -> Result<BTerm, Diagnostic> {
    Ok(match premise {
        SemanticTerm::PropAnd { left, right } => BTerm::Product(
            Box::new(holds_type(lower, scope, left)?),
            Box::new(holds_type(lower, scope, right)?),
        ),
        SemanticTerm::Implies {
            premise,
            conclusion,
        } => BTerm::Pi {
            name: None,
            erased: false,
            domain: Box::new(holds_type(lower, scope, premise)?),
            codomain: Box::new(holds_type(lower, scope, conclusion)?),
        },
        other => lower.term(other, scope)?,
    })
}

/// The proof of `goal` from `premises` (Bend name and proposition, both
/// normalized) by linear arithmetic.
///
/// # Errors
///
/// `LLB6008` when the goal is outside linear arithmetic over `Nat` or no
/// certificate is found.
pub fn prove(
    lower: &mut Lower<'_, '_>,
    scope: &Scope,
    premises: &[(String, SemanticTerm)],
    goal: &SemanticTerm,
) -> Result<BTerm, Diagnostic> {
    let mut reifier = Reifier {
        lower,
        scope,
        atoms: Vec::new(),
        subtractions: Vec::new(),
    };
    let goal_fact = reifier.fact(goal)?.ok_or_else(|| {
        fail("the goal of `linear_arithmetic` is not a linear fact over Nat, which is all Bend's checker decides")
    })?;
    let mut hyps = Vec::new();
    let mut given = Vec::new();
    for (name, premise) in premises {
        // A premise outside linear arithmetic cannot help and is left out;
        // `some x = some y` is read as `x = y`, by injectivity.
        let proof = super::var(name.clone());
        if let Some(fact) = reifier.fact(premise)? {
            hyps.push(fact);
            given.push(conjunction(reifier.lower, scope, premise, proof)?);
        } else if let Some((fact, proof)) = reifier.injective(premise, proof)? {
            hyps.push(fact);
            given.push(proof);
        }
    }
    for fact in std::mem::take(&mut reifier.subtractions) {
        hyps.push(fact);
        given.push(BTerm::Refl);
    }
    let atoms = std::mem::take(&mut reifier.atoms);
    let problem = Problem {
        atoms: u32::try_from(atoms.len()).map_err(|_| fail("too many atoms"))?,
        hyps,
        goal: Some(goal_fact.clone()),
    };
    let proof = linarith::prove(&problem).ok_or_else(|| {
        fail("`linear_arithmetic` found no certificate: the goal does not follow from its premises over the rationals")
    })?;
    let mut env = Vec::new();
    for atom in &atoms {
        env.push(lower.term(atom, scope)?);
    }
    lower.uses_prelude = true;
    lower.supports.insert(Support::LinArith);
    let proved = linarith::proof_bterm(
        Support::LinArith.alias(),
        env,
        Some(&goal_fact),
        &proof,
        &given,
    )
    .ok_or_else(|| fail("a certificate needs a hypothesis with no proof"))?;
    unconjunction(lower, scope, goal, proved)
}
