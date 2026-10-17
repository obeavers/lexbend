//! Linear arithmetic by reflection: certificate search for the prelude's
//! `LinArith.bend` (amendment D4).
//!
//! Lean closes `linear_arithmetic` with `omega`. Bend has no tactics, so the
//! backend reifies the goal and its hypotheses into the closed syntax of
//! `LinArith.bend` over an environment of Nat atoms, this module searches for
//! a certificate, and the emitted proof is one application of the law
//! `sound` (or `refute`), whose premise `check(...) == True{}` Bend closes by
//! computation with `{==}`. The search is untrusted: a wrong certificate
//! only makes `check` compute `False{}`, which the Bend checker refuses.
//!
//! The certificate format is the Bend checker's own. `check` runs a small
//! machine over a queue of facts (the negated goal first, then the
//! hypotheses in order): each fact either contributes inequalities `p >= n`
//! to an accumulator or splits into two cases; a `Fork` certificate node
//! takes the next split, a `Skip` node drops it, and a `Leaf` holds Nat
//! multipliers, one per accumulated inequality (head of the accumulator
//! first), whose combination has equal coefficients on both sides and a
//! smaller constant on the larger side. `fuel` bounds the machine's steps.
//! This module carries an exact replica of that machine ([`check`]), so a
//! certificate is validated here before it is ever printed.
//!
//! Disclosed decisions:
//!
//! - **Arithmetic.** Reified numerals and multipliers are `u32`, because a
//!   Bend Nat literal above `4294967295n` has no spelling. The elimination
//!   works in `i128` with checked operations: rows are combinations of
//!   `u32` data normalized by their gcd after every step, and an overflow
//!   ends the search with no certificate rather than a wrong one. No
//!   bignum crate is needed, and the shipped crate takes no new dependency.
//! - **Search.** Fourier–Motzkin elimination over the rationals, scaled to
//!   integers, so the procedure is complete for rational infeasibility and
//!   not for problems only integrality refutes (`2x = 1`). Variables are
//!   eliminated by the fewest generated rows, ties by atom index; every
//!   choice is a deterministic function of the problem.
//! - **Splits.** A split is taken only when the certificate of its first
//!   case uses that case; otherwise it is skipped, so an irrelevant
//!   disjunction or implication costs one sub-search, not a doubling.
//! - **Atom signs.** Bend's checker has no built-in `x >= 0`; every atom's
//!   `0 <= x` is offered as a hypothesis whose proof is `{==}` (it reduces to
//!   `{True{} == True{}}`), and only the hypotheses the final certificate
//!   uses are emitted.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::backend::bend::syntax::{BTerm, Name};

/// A Nat-valued linear term over environment atoms (`LinArith.Term`). Each
/// constructor denotes the Lean operation the backend emits, so a reified
/// goal is definitionally its Bend statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// `TVar{i}`: the `i`-th atom of the environment.
    Var(u32),
    /// `TLit{n}`: a numeral.
    Lit(u32),
    /// `TAdd{a, b}`: `Lean.Nat.add(a, b)`.
    Add(Box<Term>, Box<Term>),
    /// `TMulL{k, a}`: `Lean.Nat.mul(k, a)`.
    MulL(u32, Box<Term>),
    /// `TMulR{a, k}`: `Lean.Nat.mul(a, k)`.
    MulR(Box<Term>, u32),
}

impl Term {
    /// `a + b`.
    #[must_use]
    pub fn plus(a: Self, b: Self) -> Self {
        Self::Add(Box::new(a), Box::new(b))
    }
}

/// A Bool built from Lean's comparisons and connectives (`LinArith.BExp`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BExp {
    /// `Lean.Nat.ble(a, b)`.
    Le(Term, Term),
    /// `Lean.Nat.blt(a, b)`.
    Lt(Term, Term),
    /// `Lean.Nat.beq(a, b)`.
    Eq(Term, Term),
    /// `Lean.Bool.and(x, y)`.
    And(Box<BExp>, Box<BExp>),
    /// `Lean.Bool.or(x, y)`.
    Or(Box<BExp>, Box<BExp>),
    /// `Lean.Bool.not(x)`.
    Not(Box<BExp>),
}

/// A proposition over atoms (`LinArith.Fact`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fact {
    /// `Lean.Nat.le(a, b)`, which is also `Nat.ble a b = true`.
    Le(Term, Term),
    /// `Lean.Nat.lt(a, b)`, which is also `Nat.blt a b = true`.
    Lt(Term, Term),
    /// `{a == b : Nat}`.
    Eq(Term, Term),
    /// `{e == v : Bool}`.
    Is(BExp, bool),
    /// `{t == Lean.Nat.sub(a, b) : Nat}`: how an atom standing for a
    /// truncated subtraction tells the checker what it is.
    Sub {
        /// The atom term.
        t: Term,
        /// The minuend.
        a: Term,
        /// The subtrahend.
        b: Term,
    },
    /// `p & q`.
    And(Box<Fact>, Box<Fact>),
    /// `Either<&1, &1, p, q>`.
    Or(Box<Fact>, Box<Fact>),
    /// `p -> Empty`; `a != b` is `Not(Eq(a, b))`.
    Not(Box<Fact>),
    /// `p -> q`.
    Imp(Box<Fact>, Box<Fact>),
}

/// A certificate (`LinArith.Cert`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Cert {
    /// Farkas multipliers for the accumulated inequalities, head first;
    /// every further split is dropped.
    Leaf(Vec<u32>),
    /// One certificate per case of the next split.
    Fork(Box<Cert>, Box<Cert>),
    /// The next split dropped.
    Skip(Box<Cert>),
}

/// A reified obligation: hypotheses over `atoms` environment atoms and a
/// goal, or no goal when the hypotheses are to be refuted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Problem {
    /// The environment's length; atoms are `Term::Var(0..atoms)`.
    pub atoms: u32,
    /// The hypotheses, in the order their proofs are supplied.
    pub hyps: Vec<Fact>,
    /// The goal, or `None` to prove `Empty`.
    pub goal: Option<Fact>,
}

/// Where an emitted hypothesis comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HypRef {
    /// The problem's hypothesis at this index; the caller supplies its proof.
    Given(usize),
    /// `0 <= atom`, proved by `{==}`.
    NonNeg(u32),
}

/// A found certificate with the hypotheses it needs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    /// The emitted hypotheses' origins, in emission order.
    pub hyps: Vec<HypRef>,
    /// The emitted hypotheses themselves, aligned with `hyps`.
    pub facts: Vec<Fact>,
    /// The machine's step bound.
    pub fuel: u32,
    /// The certificate.
    pub cert: Cert,
}

// ---------------------------------------------------------------------------
// The Bend machine, replicated exactly
// ---------------------------------------------------------------------------

/// `Ge{p, n}`: `p >= n`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Ge {
    p: Term,
    n: Term,
}

/// `LinArith.Out`, without `OTake`, which the machine loops encode.
enum Out {
    Take,
    Ges(Vec<Ge>),
    Push(Fact, Fact),
    Push1(Fact),
    Split(Fact, Fact),
}

fn neg(fact: &Fact) -> Fact {
    match fact {
        Fact::Le(a, b) => Fact::Lt(b.clone(), a.clone()),
        Fact::Lt(a, b) => Fact::Le(b.clone(), a.clone()),
        Fact::Eq(a, b) => Fact::Or(
            Box::new(Fact::Lt(a.clone(), b.clone())),
            Box::new(Fact::Lt(b.clone(), a.clone())),
        ),
        Fact::Is(e, v) => Fact::Is(e.clone(), !v),
        Fact::Sub { .. } => Fact::Not(Box::new(fact.clone())),
        Fact::And(p, q) => Fact::Or(Box::new(neg(p)), Box::new(neg(q))),
        Fact::Or(p, q) => Fact::And(Box::new(neg(p)), Box::new(neg(q))),
        Fact::Not(p) => (**p).clone(),
        Fact::Imp(p, q) => Fact::And(p.clone(), Box::new(neg(q))),
    }
}

fn is(e: &BExp, v: bool) -> Fact {
    Fact::Is(e.clone(), v)
}

fn step_is(e: &BExp, v: bool) -> Out {
    match (e, v) {
        (BExp::Le(a, b), true) => Out::Push1(Fact::Le(a.clone(), b.clone())),
        (BExp::Le(a, b), false) => Out::Push1(Fact::Lt(b.clone(), a.clone())),
        (BExp::Lt(a, b), true) => Out::Push1(Fact::Lt(a.clone(), b.clone())),
        (BExp::Lt(a, b), false) => Out::Push1(Fact::Le(b.clone(), a.clone())),
        (BExp::Eq(a, b), true) => Out::Push1(Fact::Eq(a.clone(), b.clone())),
        (BExp::Eq(a, b), false) => Out::Push1(Fact::Not(Box::new(Fact::Eq(a.clone(), b.clone())))),
        (BExp::And(x, y), true) => Out::Push(is(x, true), is(y, true)),
        (BExp::And(x, y), false) => Out::Split(is(x, false), is(y, false)),
        (BExp::Or(x, y), true) => Out::Split(is(x, true), is(y, true)),
        (BExp::Or(x, y), false) => Out::Push(is(x, false), is(y, false)),
        (BExp::Not(x), v) => Out::Push1(is(x, !v)),
    }
}

fn step(fact: &Fact) -> Out {
    match fact {
        Fact::Le(a, b) => Out::Ges(vec![Ge {
            p: b.clone(),
            n: a.clone(),
        }]),
        Fact::Lt(a, b) => Out::Ges(vec![Ge {
            p: b.clone(),
            n: Term::plus(a.clone(), Term::Lit(1)),
        }]),
        Fact::Eq(a, b) => Out::Ges(vec![
            Ge {
                p: a.clone(),
                n: b.clone(),
            },
            Ge {
                p: b.clone(),
                n: a.clone(),
            },
        ]),
        Fact::Is(e, v) => step_is(e, *v),
        Fact::Sub { t, a, b } => Out::Split(
            Fact::And(
                Box::new(Fact::Le(b.clone(), a.clone())),
                Box::new(Fact::Eq(Term::plus(t.clone(), b.clone()), a.clone())),
            ),
            Fact::And(
                Box::new(Fact::Lt(a.clone(), b.clone())),
                Box::new(Fact::Eq(t.clone(), Term::Lit(0))),
            ),
        ),
        Fact::And(p, q) => Out::Push((**p).clone(), (**q).clone()),
        Fact::Or(p, q) => Out::Split((**p).clone(), (**q).clone()),
        // A negated subtraction fact says nothing linear; Bend drops it.
        Fact::Not(p) => match **p {
            Fact::Sub { .. } => Out::Ges(Vec::new()),
            _ => Out::Push1(neg(p)),
        },
        Fact::Imp(p, q) => Out::Split(neg(p), (**q).clone()),
    }
}

/// `konst(t)` and the nonzero entries of `coeffs(t)`, exactly.
fn linear(term: &Term) -> Option<(BTreeMap<u32, u128>, u128)> {
    match term {
        Term::Var(i) => Some((BTreeMap::from([(*i, 1)]), 0)),
        Term::Lit(n) => Some((BTreeMap::new(), u128::from(*n))),
        Term::Add(a, b) => {
            let (mut ca, ka) = linear(a)?;
            let (cb, kb) = linear(b)?;
            for (var, c) in cb {
                let slot = ca.entry(var).or_insert(0);
                *slot = slot.checked_add(c)?;
            }
            Some((ca, ka.checked_add(kb)?))
        }
        Term::MulL(k, a) | Term::MulR(a, k) => {
            let (ca, ka) = linear(a)?;
            let k = u128::from(*k);
            let mut scaled = BTreeMap::new();
            for (var, c) in ca {
                let c = c.checked_mul(k)?;
                if c != 0 {
                    scaled.insert(var, c);
                }
            }
            Some((scaled, ka.checked_mul(k)?))
        }
    }
}

/// `farkas(acc, ms)`: multipliers pair with the accumulator from its head,
/// the shorter list bounding the pairing.
fn farkas(acc: &[Ge], ms: &[u32]) -> bool {
    let mut left: BTreeMap<u32, u128> = BTreeMap::new();
    let mut right: BTreeMap<u32, u128> = BTreeMap::new();
    let (mut kl, mut kr) = (0u128, 0u128);
    for (ge, m) in acc.iter().zip(ms) {
        let m = u128::from(*m);
        for (term, side, konst) in [(&ge.p, &mut left, &mut kl), (&ge.n, &mut right, &mut kr)] {
            let Some((coeffs, k)) = linear(term) else {
                return false;
            };
            for (var, c) in coeffs {
                let Some(add) = c.checked_mul(m) else {
                    return false;
                };
                let slot = side.entry(var).or_insert(0);
                let Some(sum) = slot.checked_add(add) else {
                    return false;
                };
                *slot = sum;
            }
            let Some(sum) = k.checked_mul(m).and_then(|add| konst.checked_add(add)) else {
                return false;
            };
            *konst = sum;
        }
    }
    left.retain(|_, c| *c != 0);
    right.retain(|_, c| *c != 0);
    left == right && kl < kr
}

/// The facts `check` queues: the negated goal, then the hypotheses.
fn queue(goal: Option<&Fact>, hyps: &[Fact]) -> VecDeque<Fact> {
    goal.map(neg)
        .into_iter()
        .chain(hyps.iter().cloned())
        .collect()
}

/// `LinArith.check(fuel, goal, hyps, cert)` (or `refutes` when `goal` is
/// `None`), computed as the Bend definitions compute it, so `true` here is
/// `True{}` there.
#[must_use]
pub fn check(fuel: u32, goal: Option<&Fact>, hyps: &[Fact], cert: &Cert) -> bool {
    go(fuel, queue(goal, hyps), Vec::new(), cert)
}

fn go(mut fuel: u32, mut facts: VecDeque<Fact>, mut acc: Vec<Ge>, cert: &Cert) -> bool {
    let mut out = Out::Take;
    loop {
        let Some(rest) = fuel.checked_sub(1) else {
            return false;
        };
        fuel = rest;
        match std::mem::replace(&mut out, Out::Take) {
            Out::Take => match facts.pop_front() {
                None => {
                    return match cert {
                        Cert::Leaf(ms) => farkas(&acc, ms),
                        Cert::Fork(..) | Cert::Skip(_) => false,
                    }
                }
                Some(fact) => out = step(&fact),
            },
            Out::Ges(mut gs) => {
                gs.append(&mut acc);
                acc = gs;
            }
            Out::Push(p, q) => {
                facts.push_front(q);
                facts.push_front(p);
            }
            Out::Push1(p) => facts.push_front(p),
            Out::Split(p, q) => match cert {
                Cert::Leaf(_) => {}
                Cert::Skip(next) => return go(fuel, facts, acc, next),
                Cert::Fork(l, r) => {
                    let mut left = facts.clone();
                    left.push_front(p);
                    facts.push_front(q);
                    return go(fuel, left, acc.clone(), l) && go(fuel, facts, acc, r);
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Search
// ---------------------------------------------------------------------------

/// A queued fact's identity: the path of queue positions and case sides
/// that produced it. Identities survive dropping an unrelated fact, so a
/// certificate found with a case present can be reused without it.
type Id = Vec<u32>;

/// An accumulated inequality's identity: its fact and its position among
/// that fact's inequalities.
type Key = (Id, usize);

#[derive(Clone)]
struct Item {
    fact: Fact,
    id: Id,
}

#[derive(Clone)]
struct State {
    facts: VecDeque<Item>,
    acc: Vec<(Ge, Key)>,
}

/// A certificate under construction, keyed by identities rather than
/// accumulator positions; each split node records the split fact's identity.
enum Plan {
    End(BTreeMap<Key, u128>),
    Fork(Id, Box<Plan>, Box<Plan>),
    Skip(Id, Box<Plan>),
}

enum Stop {
    End,
    Split { p: Box<Item>, q: Box<Item>, sid: Id },
}

/// Search limits: machine steps, sub-searches and elimination rows. They
/// bound the work on any input; reaching one means no certificate.
struct Budget {
    steps: usize,
    searches: usize,
}

const MAX_STEPS: usize = 1 << 20;
const MAX_SEARCHES: usize = 4096;
const MAX_ROWS: usize = 4096;

fn child(id: &Id, side: u32) -> Id {
    let mut id = id.clone();
    id.push(side);
    id
}

/// Run the machine until the queue empties or a split is reached (taken
/// unless `drop_splits`), counting one step per Bend `go` call.
fn run(
    state: &mut State,
    drop_splits: bool,
    steps: &mut usize,
    budget: &mut Budget,
) -> Option<Stop> {
    // `None` is `OTake{}`; otherwise the item being integrated and its
    // fact's identity.
    let mut out: Option<(Out, Id)> = None;
    loop {
        *steps += 1;
        budget.steps += 1;
        if budget.steps > MAX_STEPS {
            return None;
        }
        match out.take() {
            None => match state.facts.pop_front() {
                None => return Some(Stop::End),
                Some(item) => out = Some((step(&item.fact), item.id)),
            },
            Some((Out::Take, _)) => {}
            Some((Out::Ges(gs), id)) => {
                let mut next: Vec<(Ge, Key)> = gs
                    .into_iter()
                    .enumerate()
                    .map(|(index, ge)| (ge, (id.clone(), index)))
                    .collect();
                next.append(&mut state.acc);
                state.acc = next;
            }
            Some((Out::Push(p, q), id)) => {
                state.facts.push_front(Item {
                    fact: q,
                    id: child(&id, 1),
                });
                state.facts.push_front(Item {
                    fact: p,
                    id: child(&id, 0),
                });
            }
            Some((Out::Push1(p), id)) => state.facts.push_front(Item {
                fact: p,
                id: child(&id, 0),
            }),
            Some((Out::Split(p, q), id)) => {
                if !drop_splits {
                    return Some(Stop::Split {
                        p: Box::new(Item {
                            fact: p,
                            id: child(&id, 0),
                        }),
                        q: Box::new(Item {
                            fact: q,
                            id: child(&id, 1),
                        }),
                        sid: id,
                    });
                }
            }
        }
    }
}

fn uses(plan: &Plan, prefix: &Id) -> bool {
    match plan {
        Plan::End(map) => map.keys().any(|(id, _)| id.starts_with(prefix)),
        Plan::Fork(sid, l, r) => sid.starts_with(prefix) || uses(l, prefix) || uses(r, prefix),
        Plan::Skip(_, next) => uses(next, prefix),
    }
}

/// The plan with the skipped splits that a dropped fact produced removed.
fn without(plan: Plan, prefix: &Id) -> Plan {
    match plan {
        Plan::End(map) => Plan::End(map),
        Plan::Fork(sid, l, r) => Plan::Fork(
            sid,
            Box::new(without(*l, prefix)),
            Box::new(without(*r, prefix)),
        ),
        Plan::Skip(sid, next) => {
            if sid.starts_with(prefix) {
                without(*next, prefix)
            } else {
                Plan::Skip(sid, Box::new(without(*next, prefix)))
            }
        }
    }
}

fn solve(mut state: State, budget: &mut Budget) -> Option<Plan> {
    budget.searches += 1;
    if budget.searches > MAX_SEARCHES {
        return None;
    }
    let mut steps = 0;
    match run(&mut state, false, &mut steps, budget)? {
        Stop::End => eliminate(&state.acc).map(Plan::End),
        Stop::Split { p, q, sid } => {
            let mut left_state = state.clone();
            left_state.facts.push_front((*p).clone());
            let left = solve(left_state, budget)?;
            if !uses(&left, &p.id) {
                return Some(Plan::Skip(sid, Box::new(without(left, &p.id))));
            }
            state.facts.push_front((*q).clone());
            let right = solve(state, budget)?;
            if !uses(&right, &q.id) {
                return Some(Plan::Skip(sid, Box::new(without(right, &q.id))));
            }
            Some(Plan::Fork(sid, Box::new(left), Box::new(right)))
        }
    }
}

/// One row `coeffs . x + c >= 0`, a nonnegative combination `mult` of the
/// accumulated inequalities.
#[derive(Clone)]
struct Row {
    coeffs: BTreeMap<u32, i128>,
    c: i128,
    mult: BTreeMap<usize, i128>,
}

fn gcd(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn normalize(row: &mut Row) {
    let g = row
        .coeffs
        .values()
        .chain(row.mult.values())
        .fold(row.c, |g, v| gcd(g, *v));
    if g > 1 {
        row.c /= g;
        row.coeffs.values_mut().for_each(|v| *v /= g);
        row.mult.values_mut().for_each(|v| *v /= g);
    }
}

/// `a * x + b * y`, entrywise, or `None` on overflow.
fn combine<K: Ord + Copy>(
    a: i128,
    x: &BTreeMap<K, i128>,
    b: i128,
    y: &BTreeMap<K, i128>,
) -> Option<BTreeMap<K, i128>> {
    let mut out = BTreeMap::new();
    for key in x.keys().chain(y.keys()) {
        if out.contains_key(key) {
            continue;
        }
        let left = a.checked_mul(x.get(key).copied().unwrap_or(0))?;
        let right = b.checked_mul(y.get(key).copied().unwrap_or(0))?;
        let value = left.checked_add(right)?;
        if value != 0 {
            out.insert(*key, value);
        }
    }
    Some(out)
}

fn signed(term: &Term) -> Option<(BTreeMap<u32, i128>, i128)> {
    let (coeffs, k) = linear(term)?;
    let mut out = BTreeMap::new();
    for (var, c) in coeffs {
        out.insert(var, i128::try_from(c).ok()?);
    }
    Some((out, i128::try_from(k).ok()?))
}

/// Fourier–Motzkin: Farkas multipliers by identity, if the accumulated
/// inequalities are rationally infeasible.
fn eliminate(acc: &[(Ge, Key)]) -> Option<BTreeMap<Key, u128>> {
    let mut rows = Vec::new();
    for (index, (ge, _)) in acc.iter().enumerate() {
        let (pc, pk) = signed(&ge.p)?;
        let (nc, nk) = signed(&ge.n)?;
        let mut row = Row {
            coeffs: combine(1, &pc, -1, &nc)?,
            c: pk.checked_sub(nk)?,
            mult: BTreeMap::from([(index, 1)]),
        };
        normalize(&mut row);
        rows.push(row);
    }
    loop {
        if let Some(row) = rows.iter().find(|row| row.coeffs.is_empty() && row.c < 0) {
            let mut map = BTreeMap::new();
            for (index, m) in &row.mult {
                let (_, key) = acc.get(*index)?;
                map.insert(key.clone(), u128::try_from(*m).ok()?);
            }
            return Some(map);
        }
        let vars: BTreeSet<u32> = rows
            .iter()
            .flat_map(|row| row.coeffs.keys().copied())
            .collect();
        // The variable generating the fewest rows; ties by index.
        let var = vars.into_iter().min_by_key(|var| {
            let pos = rows
                .iter()
                .filter(|r| r.coeffs.get(var).is_some_and(|c| *c > 0))
                .count();
            let neg = rows
                .iter()
                .filter(|r| r.coeffs.get(var).is_some_and(|c| *c < 0))
                .count();
            pos * neg
        })?;
        let (mut pos, mut neg, mut next) = (Vec::new(), Vec::new(), Vec::new());
        for row in rows {
            match row.coeffs.get(&var).copied().unwrap_or(0) {
                c if c > 0 => pos.push((c, row)),
                c if c < 0 => neg.push((-c, row)),
                _ => next.push(row),
            }
        }
        for (a, p) in &pos {
            for (b, n) in &neg {
                let mut row = Row {
                    coeffs: combine(*b, &p.coeffs, *a, &n.coeffs)?,
                    c: b.checked_mul(p.c)?.checked_add(a.checked_mul(n.c)?)?,
                    mult: combine(*b, &p.mult, *a, &n.mult)?,
                };
                normalize(&mut row);
                next.push(row);
            }
        }
        let mut seen = BTreeSet::new();
        next.retain(|row| seen.insert((row.coeffs.clone(), row.c)));
        if next.len() > MAX_ROWS {
            return None;
        }
        rows = next;
    }
}

fn skip_chain(plan: &Plan) -> Option<&BTreeMap<Key, u128>> {
    match plan {
        Plan::End(map) => Some(map),
        Plan::Skip(_, next) => skip_chain(next),
        Plan::Fork(..) => None,
    }
}

/// Lower a plan to a positional certificate by replaying the machine, with
/// the steps the deepest path takes.
fn materialize(plan: &Plan, mut state: State, budget: &mut Budget) -> Option<(Cert, usize)> {
    let mut steps = 0;
    if let Some(map) = skip_chain(plan) {
        // A `Leaf` drops the remaining splits itself.
        let Stop::End = run(&mut state, true, &mut steps, budget)? else {
            return None;
        };
        let mut ms = Vec::with_capacity(state.acc.len());
        for (_, key) in &state.acc {
            ms.push(u32::try_from(map.get(key).copied().unwrap_or(0)).ok()?);
        }
        while ms.last() == Some(&0) {
            ms.pop();
        }
        return Some((Cert::Leaf(ms), steps));
    }
    let Stop::Split { p, q, .. } = run(&mut state, false, &mut steps, budget)? else {
        return None;
    };
    match plan {
        Plan::Fork(_, l, r) => {
            let mut left_state = state.clone();
            left_state.facts.push_front(*p);
            state.facts.push_front(*q);
            let (left, sl) = materialize(l, left_state, budget)?;
            let (right, sr) = materialize(r, state, budget)?;
            Some((
                Cert::Fork(Box::new(left), Box::new(right)),
                steps + sl.max(sr),
            ))
        }
        Plan::Skip(_, next) => {
            let (next, sn) = materialize(next, state, budget)?;
            Some((Cert::Skip(Box::new(next)), steps + sn))
        }
        Plan::End(_) => None,
    }
}

fn initial(goal: Option<&Fact>, hyps: &[Fact]) -> State {
    let mut facts: VecDeque<Item> = hyps
        .iter()
        .zip(1u32..)
        .map(|(fact, index)| Item {
            fact: fact.clone(),
            id: vec![index],
        })
        .collect();
    if let Some(goal) = goal {
        facts.push_front(Item {
            fact: neg(goal),
            id: vec![0],
        });
    }
    State {
        facts,
        acc: Vec::new(),
    }
}

/// Top-level queue positions a plan relies on.
fn relied(plan: &Plan, out: &mut BTreeSet<u32>) {
    match plan {
        Plan::End(map) => out.extend(map.keys().filter_map(|(id, _)| id.first().copied())),
        Plan::Fork(sid, l, r) => {
            out.extend(sid.first().copied());
            relied(l, out);
            relied(r, out);
        }
        Plan::Skip(_, next) => relied(next, out),
    }
}

fn certify(goal: Option<&Fact>, hyps: &[Fact]) -> Option<(Plan, u32, Cert)> {
    let mut budget = Budget {
        steps: 0,
        searches: 0,
    };
    let plan = solve(initial(goal, hyps), &mut budget)?;
    let (cert, steps) = materialize(&plan, initial(goal, hyps), &mut budget)?;
    let fuel = u32::try_from(steps).ok()?;
    check(fuel, goal, hyps, &cert).then_some((plan, fuel, cert))
}

/// Search for a certificate. `None` when the problem is rationally feasible
/// (or only integrality refutes it), or a search limit is reached; the
/// caller reports that as the obligation having no Bend lowering.
#[must_use]
pub fn prove(problem: &Problem) -> Option<Proof> {
    let mut offered: Vec<(HypRef, Fact)> = (0..problem.atoms)
        .map(|atom| {
            (
                HypRef::NonNeg(atom),
                Fact::Le(Term::Lit(0), Term::Var(atom)),
            )
        })
        .collect();
    offered.extend(
        problem
            .hyps
            .iter()
            .enumerate()
            .map(|(index, fact)| (HypRef::Given(index), fact.clone())),
    );
    let goal = problem.goal.as_ref();
    let facts: Vec<Fact> = offered.iter().map(|(_, fact)| fact.clone()).collect();
    let (plan, fuel, cert) = certify(goal, &facts)?;
    let mut needed = BTreeSet::new();
    relied(&plan, &mut needed);
    // Queue position `i + 1` is offered hypothesis `i`.
    let kept: Vec<(HypRef, Fact)> = offered
        .iter()
        .zip(1u32..)
        .filter(|(_, position)| needed.contains(position))
        .map(|(hyp, _)| hyp.clone())
        .collect();
    let kept_facts: Vec<Fact> = kept.iter().map(|(_, fact)| fact.clone()).collect();
    // Re-certify on the hypotheses used; the full list stays the answer if
    // the smaller search hits a limit the larger one did not.
    let (hyps, facts, fuel, cert) = match certify(goal, &kept_facts) {
        Some((_, fuel, cert)) => (kept, kept_facts, fuel, cert),
        None => (offered, facts, fuel, cert),
    };
    Some(Proof {
        hyps: hyps.into_iter().map(|(hyp, _)| hyp).collect(),
        facts,
        fuel,
        cert,
    })
}

// ---------------------------------------------------------------------------
// Printing
// ---------------------------------------------------------------------------

fn ctor(alias: &str, name: &str, fields: Vec<BTerm>) -> BTerm {
    BTerm::Constructor(Name::synthetic(format!("{alias}.{name}")), fields)
}

fn base(name: &str, fields: Vec<BTerm>) -> BTerm {
    BTerm::Constructor(Name::synthetic(name), fields)
}

fn nat(n: u32) -> BTerm {
    BTerm::Nat(n.to_string())
}

fn list(items: Vec<BTerm>) -> BTerm {
    items
        .into_iter()
        .rev()
        .fold(base("Nil", Vec::new()), |tail, head| {
            base("Con", vec![head, tail])
        })
}

fn boolean(v: bool) -> BTerm {
    base(if v { "True" } else { "False" }, Vec::new())
}

/// A term in `LinArith.bend`'s syntax, under the alias the module is
/// imported as.
#[must_use]
pub fn term_bterm(alias: &str, term: &Term) -> BTerm {
    match term {
        Term::Var(i) => ctor(alias, "TVar", vec![nat(*i)]),
        Term::Lit(n) => ctor(alias, "TLit", vec![nat(*n)]),
        Term::Add(a, b) => ctor(
            alias,
            "TAdd",
            vec![term_bterm(alias, a), term_bterm(alias, b)],
        ),
        Term::MulL(k, a) => ctor(alias, "TMulL", vec![nat(*k), term_bterm(alias, a)]),
        Term::MulR(a, k) => ctor(alias, "TMulR", vec![term_bterm(alias, a), nat(*k)]),
    }
}

fn bexp_bterm(alias: &str, e: &BExp) -> BTerm {
    let two = |name: &str, a: &Term, b: &Term| {
        ctor(
            alias,
            name,
            vec![term_bterm(alias, a), term_bterm(alias, b)],
        )
    };
    match e {
        BExp::Le(a, b) => two("BLe", a, b),
        BExp::Lt(a, b) => two("BLt", a, b),
        BExp::Eq(a, b) => two("BEq", a, b),
        BExp::And(x, y) => ctor(
            alias,
            "BAnd",
            vec![bexp_bterm(alias, x), bexp_bterm(alias, y)],
        ),
        BExp::Or(x, y) => ctor(
            alias,
            "BOr",
            vec![bexp_bterm(alias, x), bexp_bterm(alias, y)],
        ),
        BExp::Not(x) => ctor(alias, "BNot", vec![bexp_bterm(alias, x)]),
    }
}

/// A fact in `LinArith.bend`'s syntax.
#[must_use]
pub fn fact_bterm(alias: &str, fact: &Fact) -> BTerm {
    let two = |name: &str, a: &Term, b: &Term| {
        ctor(
            alias,
            name,
            vec![term_bterm(alias, a), term_bterm(alias, b)],
        )
    };
    let pair = |name: &str, p: &Fact, q: &Fact| {
        ctor(
            alias,
            name,
            vec![fact_bterm(alias, p), fact_bterm(alias, q)],
        )
    };
    match fact {
        Fact::Le(a, b) => two("FLe", a, b),
        Fact::Lt(a, b) => two("FLt", a, b),
        Fact::Eq(a, b) => two("FEq", a, b),
        Fact::Is(e, v) => ctor(alias, "FIs", vec![bexp_bterm(alias, e), boolean(*v)]),
        Fact::Sub { t, a, b } => ctor(
            alias,
            "FSub",
            vec![
                term_bterm(alias, t),
                term_bterm(alias, a),
                term_bterm(alias, b),
            ],
        ),
        Fact::And(p, q) => pair("FAnd", p, q),
        Fact::Or(p, q) => pair("FOr", p, q),
        Fact::Not(p) => ctor(alias, "FNot", vec![fact_bterm(alias, p)]),
        Fact::Imp(p, q) => pair("FImp", p, q),
    }
}

/// A certificate in `LinArith.bend`'s syntax.
#[must_use]
pub fn cert_bterm(alias: &str, cert: &Cert) -> BTerm {
    match cert {
        Cert::Leaf(ms) => ctor(
            alias,
            "Leaf",
            vec![list(ms.iter().map(|m| nat(*m)).collect())],
        ),
        Cert::Fork(l, r) => ctor(
            alias,
            "Fork",
            vec![cert_bterm(alias, l), cert_bterm(alias, r)],
        ),
        Cert::Skip(next) => ctor(alias, "Skip", vec![cert_bterm(alias, next)]),
    }
}

/// The proof term `sound(env, goal, hyps, fuel, cert, {==}, proofs)`, or
/// `refute(...)` for a problem without a goal. `env` holds the Bend terms
/// the atoms stand for, in order; `given[i]` proves the problem's
/// hypothesis `i`. `None` when a needed hypothesis has no supplied proof.
#[must_use]
pub fn proof_bterm(
    alias: &str,
    env: Vec<BTerm>,
    goal: Option<&Fact>,
    proof: &Proof,
    given: &[BTerm],
) -> Option<BTerm> {
    let mut proofs = Vec::with_capacity(proof.hyps.len());
    for hyp in &proof.hyps {
        proofs.push(match hyp {
            HypRef::Given(index) => given.get(*index)?.clone(),
            HypRef::NonNeg(_) => BTerm::Refl,
        });
    }
    let proofs = proofs
        .into_iter()
        .rev()
        .fold(base("Unit", Vec::new()), |rest, head| {
            BTerm::Pair(Box::new(head), Box::new(rest))
        });
    let hyps = list(
        proof
            .facts
            .iter()
            .map(|fact| fact_bterm(alias, fact))
            .collect(),
    );
    let tail = [
        nat(proof.fuel),
        cert_bterm(alias, &proof.cert),
        BTerm::Refl,
        proofs,
    ];
    let (head, mut args) = match goal {
        Some(goal) => ("sound", vec![list(env), fact_bterm(alias, goal), hyps]),
        None => ("refute", vec![list(env), hyps]),
    };
    args.extend(tail);
    Some(BTerm::Call(
        Name::synthetic(format!("{alias}.{head}")),
        args,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::bend::syntax::{print_module, Body, Import, Item, Module, Param, Quantity};
    use crate::backend::{EmitSource, Emitter};
    use std::path::PathBuf;
    use std::process::Command;

    fn v(i: u32) -> Term {
        Term::Var(i)
    }

    fn n(k: u32) -> Term {
        Term::Lit(k)
    }

    fn not(fact: Fact) -> Fact {
        Fact::Not(Box::new(fact))
    }

    fn imp(p: Fact, q: Fact) -> Fact {
        Fact::Imp(Box::new(p), Box::new(q))
    }

    fn problem(atoms: u32, hyps: Vec<Fact>, goal: Fact) -> Problem {
        Problem {
            atoms,
            hyps,
            goal: Some(goal),
        }
    }

    /// Atoms 0 = used, 1 = cost, 2 = total - 64, 3 = total - (total - 64),
    /// the unfolded `Models.Session.SessionStep`.
    fn session(goal: Fact) -> Problem {
        let total = Term::plus(v(0), v(1));
        problem(
            4,
            vec![
                Fact::Le(v(0), n(64)),
                Fact::Le(v(1), n(16)),
                Fact::Sub {
                    t: v(2),
                    a: total.clone(),
                    b: n(64),
                },
                Fact::Sub {
                    t: v(3),
                    a: total,
                    b: v(2),
                },
            ],
            goal,
        )
    }

    fn session_preserves() -> Problem {
        session(Fact::Le(v(3), n(64)))
    }

    fn session_conserves() -> Problem {
        session(Fact::Eq(Term::plus(v(3), v(2)), Term::plus(v(0), v(1))))
    }

    fn proves(problem: &Problem) -> Proof {
        let proof = prove(problem).expect("a certificate");
        assert!(check(
            proof.fuel,
            problem.goal.as_ref(),
            &proof.facts,
            &proof.cert
        ));
        proof
    }

    #[test]
    fn linarith_closes_bounds_and_refuses_false_ones() {
        let hyps = vec![Fact::Le(v(0), n(64))];
        proves(&problem(1, hyps.clone(), Fact::Lt(v(0), n(65))));
        assert_eq!(prove(&problem(1, hyps, Fact::Lt(v(0), n(64)))), None);
    }

    #[test]
    fn linarith_session_goals_with_truncated_subtraction() {
        let preserves = proves(&session_preserves());
        assert!(matches!(preserves.cert, Cert::Fork(..) | Cert::Skip(_)));
        proves(&session_conserves());
        // used = 64, cost = 0 refutes the tighter bound.
        let mut wrong = session_preserves();
        wrong.goal = Some(Fact::Le(v(3), n(63)));
        assert_eq!(prove(&wrong), None);
    }

    #[test]
    fn linarith_bool_bridges_and_disequality() {
        // Recursion.Main.search_decreases.
        let low_high = Fact::Is(BExp::Lt(v(1), v(2)), true);
        let far = Fact::Is(BExp::Le(v(0), Term::plus(v(1), v(1))), false);
        let goal = Fact::Lt(v(3), v(4));
        let subs = vec![
            Fact::Sub {
                t: v(3),
                a: v(2),
                b: Term::plus(v(1), n(1)),
            },
            Fact::Sub {
                t: v(4),
                a: v(2),
                b: v(1),
            },
        ];
        let mut hyps = vec![low_high, far];
        hyps.extend(subs);
        proves(&problem(5, hyps, goal));
        // beq x y = false, x <= y |- x < y.
        let hyps = vec![Fact::Is(BExp::Eq(v(0), v(1)), false), Fact::Le(v(0), v(1))];
        proves(&problem(2, hyps, Fact::Lt(v(0), v(1))));
        // Budget.burn_sound's hypothesis: ble k s && blt 0 k = true |- s - k < s.
        let both = Fact::Is(
            BExp::And(
                Box::new(BExp::Le(v(0), v(1))),
                Box::new(BExp::Lt(n(0), v(0))),
            ),
            true,
        );
        let sub = Fact::Sub {
            t: v(2),
            a: v(1),
            b: v(0),
        };
        proves(&problem(3, vec![both, sub], Fact::Lt(v(2), v(1))));
        // A negated goal: a < b |- a != b.
        proves(&problem(
            2,
            vec![Fact::Lt(v(0), v(1))],
            not(Fact::Eq(v(0), v(1))),
        ));
    }

    #[test]
    fn linarith_skips_irrelevant_cases() {
        // Twelve implications the goal never needs, then the one it does.
        let mut hyps: Vec<Fact> = (0..12)
            .map(|k| imp(Fact::Eq(v(0), n(k + 10)), Fact::Le(v(1), n(k))))
            .collect();
        hyps.push(Fact::Eq(v(0), n(1)));
        hyps.push(imp(Fact::Eq(v(0), n(1)), Fact::Eq(v(1), n(1))));
        let proof = proves(&problem(2, hyps, Fact::Le(v(1), n(1))));
        assert!(
            proof.hyps.len() <= 4,
            "only the needed hypotheses: {:?}",
            proof.hyps
        );
    }

    #[test]
    fn linarith_refutation_and_integrality_limit() {
        let contradictory = Problem {
            atoms: 1,
            hyps: vec![Fact::Lt(v(0), n(3)), Fact::Lt(n(5), v(0))],
            goal: None,
        };
        let proof = prove(&contradictory).expect("a refutation");
        assert!(check(proof.fuel, None, &proof.facts, &proof.cert));
        // 2x = 1 is rationally feasible: outside the procedure, honestly.
        let parity = Problem {
            atoms: 1,
            hyps: vec![Fact::Eq(Term::MulL(2, Box::new(v(0))), n(1))],
            goal: None,
        };
        assert_eq!(prove(&parity), None);
    }

    #[test]
    fn linarith_rejects_planted_certificates() {
        let problem = session_preserves();
        let proof = proves(&problem);
        let goal = problem.goal.as_ref();
        assert!(!check(
            proof.fuel,
            goal,
            &proof.facts,
            &Cert::Leaf(Vec::new())
        ));
        assert!(!check(1, goal, &proof.facts, &proof.cert));
        let swapped = match &proof.cert {
            Cert::Fork(l, r) => Cert::Fork(r.clone(), l.clone()),
            other => Cert::Fork(Box::new(other.clone()), Box::new(other.clone())),
        };
        assert!(!check(proof.fuel, goal, &proof.facts, &swapped));
    }

    // -----------------------------------------------------------------
    // End to end through the Bend checker
    // -----------------------------------------------------------------

    fn find_bend() -> Option<PathBuf> {
        let path = std::env::var_os("PATH")?;
        std::env::split_paths(&path)
            .map(|dir| dir.join("bend"))
            .find(|candidate| candidate.is_file())
    }

    fn synthetic() -> EmitSource {
        EmitSource::Synthetic("core:bend-linarith-test/1".to_owned())
    }

    fn name(text: &str) -> BTerm {
        BTerm::Name(Name::synthetic(text))
    }

    fn call(head: &str, args: Vec<BTerm>) -> BTerm {
        BTerm::Call(Name::synthetic(head), args)
    }

    fn lean(op: &str, args: Vec<BTerm>) -> BTerm {
        call(&format!("L.Lean.Nat.{op}"), args)
    }

    fn param(quantity: Quantity, text: &str, ty: BTerm) -> Param {
        Param {
            quantity,
            name: Name::synthetic(text),
            ty,
            source: synthetic(),
        }
    }

    fn law(name_text: &str, params: Vec<Param>, claim: BTerm, proof: BTerm) -> Item {
        Item::Law {
            name: Name::synthetic(name_text),
            params,
            claim,
            claim_source: synthetic(),
            proof: Body::term(proof, synthetic()),
            source: synthetic(),
        }
    }

    /// `session_preserves` and `session_conserves` as Bend laws over
    /// `used`/`cost`, each proved by one `LA.sound` application.
    fn session_module(preserves: &Proof, conserves: &Proof) -> String {
        let total = || lean("add", vec![name("x"), name("c")]);
        let over = || lean("sub", vec![total(), nat(64)]);
        let used = || lean("sub", vec![total(), over()]);
        let env = || vec![name("x"), name("c"), over(), used()];
        let given = [name("h1"), name("h2"), BTerm::Refl, BTerm::Refl];
        let params = || {
            vec![
                param(Quantity::Reusable, "x", name("Nat")),
                param(Quantity::Reusable, "c", name("Nat")),
                param(Quantity::Affine, "h1", lean("le", vec![name("x"), nat(64)])),
                param(Quantity::Affine, "h2", lean("le", vec![name("c"), nat(16)])),
            ]
        };
        let preserves_goal = session_preserves().goal.expect("a goal");
        let conserves_goal = session_conserves().goal.expect("a goal");
        let module = Module {
            imports: vec![
                Import {
                    path: "./LexLean.bend".to_owned(),
                    alias: "L".to_owned(),
                },
                Import {
                    path: "./LinArith.bend".to_owned(),
                    alias: "LA".to_owned(),
                },
            ],
            items: vec![
                law(
                    "session_preserves",
                    params(),
                    lean("le", vec![used(), nat(64)]),
                    proof_bterm("LA", env(), Some(&preserves_goal), preserves, &given)
                        .expect("every proof supplied"),
                ),
                law(
                    "session_conserves",
                    params(),
                    BTerm::Equal(
                        Box::new(lean("add", vec![used(), over()])),
                        Box::new(total()),
                        Box::new(name("Nat")),
                    ),
                    proof_bterm("LA", env(), Some(&conserves_goal), conserves, &given)
                        .expect("every proof supplied"),
                ),
            ],
        };
        let mut emitter = Emitter::new();
        print_module(&module, &mut emitter);
        emitter.text().to_owned()
    }

    /// Run `bend --check-only` on `text` beside the prelude modules: `None`
    /// when no `bend` is on PATH, else whether it printed exactly the
    /// success lines, and its output.
    fn bend_check(label: &str, text: &str) -> Option<(bool, String)> {
        let bend = find_bend()?;
        let prelude = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../language/bend-prelude");
        let dir =
            std::env::temp_dir().join(format!("lexlean-linarith-{}-{label}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("scratch directory");
        for module in ["LexLean.bend", "LinArith.bend"] {
            std::fs::copy(prelude.join(module), dir.join(module)).expect("prelude module");
        }
        std::fs::write(dir.join("Test.bend"), text).expect("test module");
        let output = Command::new(bend)
            .arg("Test.bend")
            .arg("--check-only")
            .current_dir(&dir)
            .env("BEND_NO_TELEMETRY", "1")
            .output()
            .expect("bend runs");
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        let _ = std::fs::remove_dir_all(&dir);
        let ok = output.status.success()
            && stdout == "ALL PROOFS CHECK\nUse --verdict for mathematical validity.\n";
        Some((ok, format!("{stdout}{stderr}")))
    }

    #[test]
    fn linarith_end_to_end_through_bend() {
        let preserves = proves(&session_preserves());
        let conserves = proves(&session_conserves());
        let text = session_module(&preserves, &conserves);
        let Some((ok, output)) = bend_check("good", &text) else {
            println!("bend is not on PATH: the end-to-end Bend check was skipped");
            return;
        };
        assert!(ok, "Bend refused the certificate:\n{output}\n{text}");
        // A planted wrong certificate must be refused by Bend itself.
        let planted = Proof {
            cert: Cert::Leaf(Vec::new()),
            ..preserves
        };
        let text = session_module(&planted, &conserves);
        let (ok, output) = bend_check("planted", &text).expect("bend was found above");
        assert!(!ok, "Bend accepted a wrong certificate:\n{output}");
        assert!(output.starts_with("SOME PROOFS FAIL"), "{output}");
    }
}
