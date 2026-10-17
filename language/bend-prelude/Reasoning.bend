# LexLean reasoning support: the predicates and lemmas the theorems a
# language-2.2 reasoning declaration generates are stated with and proved by.
# They mirror the Lean runtime's LexLeanReasoning over the forms the semantic
# lowering produces: `if` is Semantic.bend's Sem.ite, a fold is Sem.listFold,
# a bounded loop is Sem.iterateUntil, a pair is projected by Sem.fst/Sem.snd
# and an order on Nat is Sem.le/Sem.lt. The closure Star, All and Reaches are
# the runtime's (Runtime.bend), which the lowering reaches unchanged.
#
# The generic laws take their step, predicate and hypothesis as closed
# templates over an environment of their own, as a converted function
# parameter is (SPEC.md §18.11.2), so each is proved once and every reasoner
# instantiates it. The kernel checks a template definition against a model
# that gives every template its default, so a template hypothesis must hold
# there: each concludes a template predicate (Unit by default), never an
# equation on Nat. The arithmetic a theorem adds on top of a law is the
# first-order lemmas of the third section.

import Base
import ./LexLean.bend as L
import ./Semantic.bend as S
import ./Runtime.bend as R

# ---------------------------------------------------------------------------
# Predicates over the semantic forms.
# ---------------------------------------------------------------------------

# A found answer's node satisfies ok and is accepted with that answer.
def Found(-N: Data, -A: Data, ok: N -> Type, accept: N -> Maybe<&2, A>, found: Maybe<&2, L.Lean.Prod(A, N)>) -> Type:
  match found:
    case None{}:
      Unit
    case Some{hit}:
      ok(S.Sem.snd(A, N, hit)) & {accept(S.Sem.snd(A, N, hit)) == Some{S.Sem.fst(A, N, hit)} : Maybe<&2, A>}

# Every frontier node satisfies ok, and a found answer is accepted.
def SearchOk(-N: Data, -A: Data, ok: N -> Type, accept: N -> Maybe<&2, A>, frontier: List<&2, N>, found: Maybe<&2, L.Lean.Prod(A, N)>) -> Type:
  R.LexLeanReasoning.All(N, ok, frontier) & Found(N, A, ok, accept, found)

def searchStart(-N: Data, -A: Data, -ok: N -> Type, -accept: N -> Maybe<&2, A>, -frontier: List<&2, N>, h: R.LexLeanReasoning.All(N, ok, frontier)) -> SearchOk(N, A, ok, accept, frontier, None{}):
  (h, Unit{})

# ---------------------------------------------------------------------------
# Constructor clashes and injectivity, which a split refutes or reads.
# ---------------------------------------------------------------------------

def noneDisc(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def someDisc(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def failDisc(-E: Data, -A: Data, m: Result<&2, &2, E, A>) -> Type:
  match m:
    case Fail{x}:
      Unit
    case Done{x}:
      Empty

def doneDisc(-E: Data, -A: Data, m: Result<&2, &2, E, A>) -> Type:
  match m:
    case Fail{x}:
      Empty
    case Done{x}:
      Unit

def zeroDisc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def noneSome.empty(-A: Data, -v: A, e: {None{} == Some{v} : Maybe<&2, A>}) -> Empty:
  %e : someDisc(A, _)
  Unit{}

def noneSome(-A: Data, -B: Type, -v: A, e: {None{} == Some{v} : Maybe<&2, A>}) -> B:
  L.Lean.Empty.elim(B, noneSome.empty(A, v, e))

def someNone.empty(-A: Data, -v: A, e: {Some{v} == None{} : Maybe<&2, A>}) -> Empty:
  %e : noneDisc(A, _)
  Unit{}

def someNone(-A: Data, -B: Type, -v: A, e: {Some{v} == None{} : Maybe<&2, A>}) -> B:
  L.Lean.Empty.elim(B, someNone.empty(A, v, e))

def failDone.empty(-E: Data, -A: Data, -x: E, -v: A, e: {Fail{x} == Done{v} : Result<&2, &2, E, A>}) -> Empty:
  %e : failDisc(E, A, _)
  Unit{}

def failDone(-E: Data, -A: Data, -B: Type, -x: E, -v: A, e: {Fail{x} == Done{v} : Result<&2, &2, E, A>}) -> B:
  L.Lean.Empty.elim(B, failDone.empty(E, A, x, v, e))

def doneFail.empty(-E: Data, -A: Data, -x: E, -v: A, e: {Done{v} == Fail{x} : Result<&2, &2, E, A>}) -> Empty:
  %e : doneDisc(E, A, _)
  Unit{}

def doneFail(-E: Data, -A: Data, -B: Type, -x: E, -v: A, e: {Done{v} == Fail{x} : Result<&2, &2, E, A>}) -> B:
  L.Lean.Empty.elim(B, doneFail.empty(E, A, x, v, e))

def succZero.empty(-p: Nat, e: {1n+p == 0n : Nat}) -> Empty:
  %e : zeroDisc(_)
  Unit{}

# A clash read off the scrutinee itself: the generated proofs refute a
# branch whose equation's left side evaluates to the other constructor
# without naming its payload.
def notSome.empty(-A: Data, +m: Maybe<&2, A>, -v: A, e: {m == Some{v} : Maybe<&2, A>}, h: someDisc(A, m)) -> Empty:
  %e : someDisc(A, _)
  h

def notSome(-A: Data, -B: Type, +m: Maybe<&2, A>, -v: A, e: {m == Some{v} : Maybe<&2, A>}, h: someDisc(A, m)) -> B:
  L.Lean.Empty.elim(B, notSome.empty(A, m, v, e, h))

def notNone.empty(-A: Data, +m: Maybe<&2, A>, e: {m == None{} : Maybe<&2, A>}, h: noneDisc(A, m)) -> Empty:
  %e : noneDisc(A, _)
  h

def notNone(-A: Data, -B: Type, +m: Maybe<&2, A>, e: {m == None{} : Maybe<&2, A>}, h: noneDisc(A, m)) -> B:
  L.Lean.Empty.elim(B, notNone.empty(A, m, e, h))

def notDone.empty(-E: Data, -A: Data, +m: Result<&2, &2, E, A>, -v: A, e: {m == Done{v} : Result<&2, &2, E, A>}, h: failDisc(E, A, m)) -> Empty:
  %e : failDisc(E, A, _)
  h

def notDone(-E: Data, -A: Data, -B: Type, +m: Result<&2, &2, E, A>, -v: A, e: {m == Done{v} : Result<&2, &2, E, A>}, h: failDisc(E, A, m)) -> B:
  L.Lean.Empty.elim(B, notDone.empty(E, A, m, v, e, h))

def someInj(-A: Data, +a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  R.LexLeanReasoning.someInj(A, a, b, e)

def doneInj(-E: Data, -A: Data, +a: A, -b: A, e: {Done{a} == Done{b} : Result<&2, &2, E, A>}) -> {a == b : A}:
  Equal.cong(Result<&2, &2, E, A>, A, m => R.LexLeanReasoning.doneValue(E, A, a, m), Done{a}, Done{b}, e)

# What a value inside a `some`, or a `done`, satisfies, read off the equation
# that names it: a theorem about the record a step built is a theorem about
# the step's result.
def SomeAll(-A: Data, g: A -> Type, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      g(x)

def someCase(-A: Data, -g: A -> Type, +m: Maybe<&2, A>, -q: A, e: {m == Some{q} : Maybe<&2, A>}, h: SomeAll(A, g, m)) -> g(q):
  match m:
    case None{}:
      noneSome(A, g(q), q, e)
    case Some{x}:
      %someInj(A, x, q, e) : g(_)
      h

def DoneAll(-E: Data, -A: Data, g: A -> Type, m: Result<&2, &2, E, A>) -> Type:
  match m:
    case Fail{x}:
      Unit
    case Done{x}:
      g(x)

def doneCase(-E: Data, -A: Data, -g: A -> Type, +m: Result<&2, &2, E, A>, -q: A, e: {m == Done{q} : Result<&2, &2, E, A>}, h: DoneAll(E, A, g, m)) -> g(q):
  match m:
    case Fail{x}:
      failDone(E, A, g(q), x, q, e)
    case Done{x}:
      %doneInj(E, A, x, q, e) : g(_)
      h

# ---------------------------------------------------------------------------
# A rule's application `if g then some c else none`, and an accepted answer.
# ---------------------------------------------------------------------------

def guarded.go(-A: Data, -r: A -> A -> Type, -s: A, -c: A, -t: A, h: r(s, c), ct: {c == t : A}) -> r(s, t):
  %ct : r(s, _)
  h

def guarded(-A: Data, -r: A -> A -> Type, -s: A, g: Bool, +c: A, h: {g == True{} : Bool} -> r(s, c), -t: A) -> {S.Sem.ite(Maybe<&2, A>, g, Some{c}, None{}) == Some{t} : Maybe<&2, A>} -> r(s, t):
  match g:
    case False{}:
      e => noneSome(A, r(s, t), t, e)
    case True{}:
      e => guarded.go(A, r, s, c, t, h({==}), someInj(A, c, t, e))

def guardedRank.go(-A: Data, -mu: A -> Nat, -s: A, -c: A, -t: A, h: S.Sem.lt(mu(c), mu(s)), ct: {c == t : A}) -> S.Sem.lt(mu(t), mu(s)):
  %ct : S.Sem.lt(mu(_), mu(s))
  h

def guardedRank(-A: Data, -mu: A -> Nat, -s: A, g: Bool, +c: A, h: {g == True{} : Bool} -> S.Sem.lt(mu(c), mu(s)), -t: A) -> {S.Sem.ite(Maybe<&2, A>, g, Some{c}, None{}) == Some{t} : Maybe<&2, A>} -> S.Sem.lt(mu(t), mu(s)):
  match g:
    case False{}:
      e => noneSome(A, S.Sem.lt(mu(t), mu(s)), t, e)
    case True{}:
      e => guardedRank.go(A, mu, s, c, t, h({==}), someInj(A, c, t, e))

def checked(-A: Data, b: Bool, +a: A, -c: A) -> {S.Sem.ite(Maybe<&2, A>, b, Some{a}, None{}) == Some{c} : Maybe<&2, A>} -> L.Lean.Prod({b == True{} : Bool}, {a == c : A}):
  match b:
    case False{}:
      e => noneSome(A, L.Lean.Prod({False{} == True{} : Bool}, {a == c : A}), c, e)
    case True{}:
      e => ({==}, someInj(A, a, c, e))

# The same, continuing with the check's equation: what holds of the answer
# a holds of the c it reached.
def checkedThen(-A: Data, -g: A -> Type, b: Bool, +a: A, -c: A, e: {S.Sem.ite(Maybe<&2, A>, b, Some{a}, None{}) == Some{c} : Maybe<&2, A>}, k: {b == True{} : Bool} -> g(a)) -> g(c):
  match b:
    case False{}:
      noneSome(A, g(c), c, e)
    case True{}:
      %someInj(A, a, c, e) : g(_)
      k({==})

# ---------------------------------------------------------------------------
# Arithmetic a theorem adds to a law: counters against fuel, a decreasing
# measure, and the peak of a frontier.
# ---------------------------------------------------------------------------

def zeroLe(n: Nat) -> S.Sem.le(0n, n):
  {==}

def le_succ(+n: Nat) -> S.Sem.le(n, 1n+n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_succ(p)

def le_add(+n: Nat, +m: Nat) -> S.Sem.le(n, L.Lean.Nat.add(n, m)):
  match m:
    case 0n:
      S.Sem.ble_refl(n)
    case 1n+p:
      S.Sem.ble_trans(n, L.Lean.Nat.add(n, p), 1n+L.Lean.Nat.add(n, p), le_add(n, p), le_succ(L.Lean.Nat.add(n, p)))

def le_add_mono(-a: Nat, -b: Nat, +r: Nat, h: S.Sem.le(a, b)) -> S.Sem.le(L.Lean.Nat.add(a, r), L.Lean.Nat.add(b, r)):
  match r:
    case 0n:
      h
    case 1n+p:
      le_add_mono(a, b, p, h)

def zero_add(+n: Nat) -> {L.Lean.Nat.add(0n, n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %zero_add(p) : {1n+L.Lean.Nat.add(0n, p) == 1n+_ : Nat}
      {==}

# The fuel a loop starts with bounds a counter that starts at zero.
def fuelStart(+fuel: Nat) -> S.Sem.le(L.Lean.Nat.add(0n, fuel), fuel):
  %L.Lean.Eq.symm(Nat, L.Lean.Nat.add(0n, fuel), fuel, zero_add(fuel)) : S.Sem.le(_, fuel)
  S.Sem.ble_refl(fuel)

# A counter plus the fuel left stays within the starting fuel: one step
# raises the counter by one, or by at most one, as it spends one unit.
def succAddLe(+fa: Nat, +n: Nat, -t: Nat, h: S.Sem.le(L.Lean.Nat.add(fa, 1n+n), t)) -> S.Sem.le(L.Lean.Nat.add(L.Lean.Nat.add(fa, 1n), n), t):
  %L.Lean.Eq.symm(Nat, L.Lean.Nat.add(1n+fa, n), 1n+L.Lean.Nat.add(fa, n), L.Lean.Nat.succ_add(fa, n)) : S.Sem.le(_, t)
  h

def countPres(+fa: Nat, +fb: Nat, +n: Nat, +t: Nat, e: {fb == L.Lean.Nat.add(fa, 1n) : Nat}, h: S.Sem.le(L.Lean.Nat.add(fa, 1n+n), t)) -> S.Sem.le(L.Lean.Nat.add(fb, n), t):
  %L.Lean.Eq.symm(Nat, fb, L.Lean.Nat.add(fa, 1n), e) : S.Sem.le(L.Lean.Nat.add(_, n), t)
  succAddLe(fa, n, t, h)

def growPres(+fa: Nat, +fb: Nat, +n: Nat, +t: Nat, e: S.Sem.le(fb, L.Lean.Nat.add(fa, 1n)), h: S.Sem.le(L.Lean.Nat.add(fa, 1n+n), t)) -> S.Sem.le(L.Lean.Nat.add(fb, n), t):
  S.Sem.ble_trans(L.Lean.Nat.add(fb, n), L.Lean.Nat.add(L.Lean.Nat.add(fa, 1n), n), t, le_add_mono(fb, L.Lean.Nat.add(fa, 1n), n, e), succAddLe(fa, n, t, h))

def fuelLe(+a: Nat, +n: Nat, +t: Nat, h: S.Sem.le(L.Lean.Nat.add(a, n), t)) -> S.Sem.le(a, t):
  S.Sem.ble_trans(a, L.Lean.Nat.add(a, n), t, le_add(a, n), h)

# A measure below the fuel left, decreasing at each step, stays below it.
def stopsPres(+mb: Nat, +ma: Nat, +n: Nat, hb: S.Sem.lt(mb, ma), ha: S.Sem.lt(ma, 1n+n)) -> S.Sem.lt(mb, n):
  S.Sem.lt_fuel(mb, ma, n, hb, ha)

# How a loop ended: stopped by its step, or out of fuel with none left.
def Halted(n: Nat, stopped: Bool) -> Type:
  match stopped:
    case True{}:
      Unit
    case False{}:
      {n == 0n : Nat}

def stopsStep.go(-PB: Data, +mb: Nat, +ma: Nat, +n: Nat, la: S.Sem.lt(ma, 1n+n), hb: L.Lean.Prod(PB, S.Sem.lt(mb, ma))) -> L.Lean.Prod(PB, S.Sem.lt(mb, n)):
  match hb:
    case (pb, lb):
      (pb, stopsPres(mb, ma, n, lb, la))

# A measure below the fuel left at the end means the step stopped the loop.
def stopsFinish(stopped: Bool, +n: Nat, +m: Nat, h: Halted(n, stopped), hl: S.Sem.lt(m, n)) -> {stopped == True{} : Bool}:
  match stopped n:
    case True{} _:
      {==}
    case False{} 0n:
      S.Sem.lt_zero({False{} == True{} : Bool}, m, hl)
    case False{} 1n+p:
      L.Lean.Empty.elim({False{} == True{} : Bool}, succZero.empty(p, h))

# One step of a terminating loop: the invariant holds after it, and the
# measure, below the fuel left before, is below the fuel left after.
def stopsStep(-PA: Data, -PB: Data, +mb: Nat, +ma: Nat, +n: Nat, hp: L.Lean.Prod(PA, S.Sem.lt(ma, 1n+n)), h: PA -> L.Lean.Prod(PB, S.Sem.lt(mb, ma))) -> L.Lean.Prod(PB, S.Sem.lt(mb, n)):
  match hp:
    case (pa, la):
      stopsStep.go(PB, mb, ma, n, la, h(pa))

def peakBound(b: Bool, -p: Nat, -len: Nat, -k: Nat, hp: S.Sem.le(p, k), hl: S.Sem.le(len, k)) -> S.Sem.le(S.Sem.ite(Nat, b, len, p), k):
  match b:
    case True{}:
      hl
    case False{}:
      hp

# ---------------------------------------------------------------------------
# The generic laws.
# ---------------------------------------------------------------------------

# A predicate a relation preserves holds along its closure.
def starPreserves(~A: Data, ~r: A -> A -> Type, ~j: A -> Type, ~hp: @-s: A -> @-t: A -> j(s) -> r(s, t) -> j(t), -a: A, -c: A, h: R.LexLeanReasoning.Star<A, r, a, c>, ha: j(a)) -> j(c):
  match h:
    case R.LexLeanReasoning.Star.refl.mk{e}:
      %e : j(_)
      ha
    case R.LexLeanReasoning.Star.tail.mk{b, rest, step}:
      hp(b, c, starPreserves(~A, ~r, ~j, ~hp, a, b, rest, ha), step)

# A fold keeps any invariant its step keeps.
def foldInvariant(~A: Data, ~St: Data, ~E: Data, ~step: @+e: E -> @+s: St -> @+a: A -> St, ~K: Data, ~P: @+k: K -> @+s: St -> Type, ~h: @+e: E -> @+k: K -> @+s: St -> @+a: A -> P(k, s) -> P(k, step(e, s, a)), +e: E, +k: K, +values: List<&2, A>, +initial: St, hi: P(k, initial)) -> P(k, S.Sem.listFold(~A, ~St, ~E, ~step, e, values, initial)):
  match values:
    case Nil{}:
      hi
    case Con{head, tail}:
      foldInvariant(~A, ~St, ~E, ~step, ~K, ~P, ~h, e, k, tail, step(e, initial, head), h(e, k, initial, head, hi))

# The same, for a step that keeps it only on elements satisfying q.
def allFold(~A: Data, ~St: Data, ~E: Data, ~step: @+e: E -> @+s: St -> @+a: A -> St, ~K: Data, ~P: @+k: K -> @+s: St -> Type, ~Q: @+k: K -> @+a: A -> Type, ~h: @+e: E -> @+k: K -> @+s: St -> @+a: A -> Q(k, a) -> P(k, s) -> P(k, step(e, s, a)), +e: E, +k: K, +values: List<&2, A>, +initial: St, hq: R.LexLeanReasoning.All(A, (+a => Q(k, a)), values), hi: P(k, initial)) -> P(k, S.Sem.listFold(~A, ~St, ~E, ~step, e, values, initial)):
  match values:
    case Nil{}:
      hi
    case Con{head, tail}:
      match hq:
        case (qh, qt):
          allFold(~A, ~St, ~E, ~step, ~K, ~P, ~Q, ~h, e, k, tail, step(e, initial, head), qt, h(e, k, initial, head, qh, hi))

# Folding one more element is one more step; stated the way a rewrite of the
# longer fold uses it.
def foldSnoc(~A: Data, ~St: Data, ~E: Data, ~step: @+e: E -> @+s: St -> @+a: A -> St, +e: E, +values: List<&2, A>, +last: A, +initial: St) -> {step(e, S.Sem.listFold(~A, ~St, ~E, ~step, e, values, initial), last) == S.Sem.listFold(~A, ~St, ~E, ~step, e, R.LexLeanRuntime.append.List(A, values, Con{last, Nil{}}), initial) : St}:
  match values:
    case Nil{}:
      {==}
    case Con{head, tail}:
      foldSnoc(~A, ~St, ~E, ~step, e, tail, last, step(e, initial, head))

# A bounded loop keeps any invariant its step keeps.
def iterateUntilInvariant.go(~A: Data, ~E: Data, ~step: @+e: E -> @+s: A -> Maybe<&2, A>, ~K: Data, ~P: @+k: K -> @+s: A -> Type, ~h: @+e: E -> @+k: K -> @+a: A -> @+b: A -> {step(e, a) == Some{b} : Maybe<&2, A>} -> P(k, a) -> P(k, b), +e: E, +k: K, +fuel: Nat, +next: Maybe<&2, A>, +state: A, en: {step(e, state) == next : Maybe<&2, A>}, hs: P(k, state)) -> P(k, S.Sem.fst(A, Bool, S.Sem.iterateUntil.go(~A, ~E, ~step, e, fuel, next, state))):
  match fuel:
    case 0n:
      hs
    case 1n+rest:
      match next:
        case None{}:
          hs
        case Some{after}:
          iterateUntilInvariant.go(~A, ~E, ~step, ~K, ~P, ~h, e, k, rest, step(e, after), after, {==}, h(e, k, state, after, en, hs))

def iterateUntilInvariant(~A: Data, ~E: Data, ~step: @+e: E -> @+s: A -> Maybe<&2, A>, ~K: Data, ~P: @+k: K -> @+s: A -> Type, ~h: @+e: E -> @+k: K -> @+a: A -> @+b: A -> {step(e, a) == Some{b} : Maybe<&2, A>} -> P(k, a) -> P(k, b), +e: E, +k: K, +fuel: Nat, +initial: A, hi: P(k, initial)) -> P(k, S.Sem.fst(A, Bool, S.Sem.iterateUntil(~A, ~E, ~step, e, fuel, initial))):
  iterateUntilInvariant.go(~A, ~E, ~step, ~K, ~P, ~h, e, k, fuel, step(e, initial), initial, {==}, hi)

# A bounded loop keeps an invariant indexed by the fuel left; the fuel left at
# the end is zero unless the step stopped it. The counter, growth and
# termination theorems are this law with an arithmetic invariant.
def iterateUntilFuel.go(~A: Data, ~E: Data, ~step: @+e: E -> @+s: A -> Maybe<&2, A>, ~K: Data, ~P: @+k: K -> @+n: Nat -> @+s: A -> Type, ~h: @+e: E -> @+k: K -> @+n: Nat -> @+a: A -> @+b: A -> {step(e, a) == Some{b} : Maybe<&2, A>} -> P(k, 1n+n, a) -> P(k, n, b), +e: E, +k: K, +fuel: Nat, +next: Maybe<&2, A>, +state: A, en: {step(e, state) == next : Maybe<&2, A>}, hs: P(k, fuel, state)) -> &n: Nat -> P(k, n, S.Sem.fst(A, Bool, S.Sem.iterateUntil.go(~A, ~E, ~step, e, fuel, next, state))) & Halted(n, S.Sem.snd(A, Bool, S.Sem.iterateUntil.go(~A, ~E, ~step, e, fuel, next, state))):
  match fuel:
    case 0n:
      (0n, (hs, {==}))
    case 1n+rest:
      match next:
        case None{}:
          (1n+rest, (hs, Unit{}))
        case Some{after}:
          iterateUntilFuel.go(~A, ~E, ~step, ~K, ~P, ~h, e, k, rest, step(e, after), after, {==}, h(e, k, rest, state, after, en, hs))

def iterateUntilFuel(~A: Data, ~E: Data, ~step: @+e: E -> @+s: A -> Maybe<&2, A>, ~K: Data, ~P: @+k: K -> @+n: Nat -> @+s: A -> Type, ~h: @+e: E -> @+k: K -> @+n: Nat -> @+a: A -> @+b: A -> {step(e, a) == Some{b} : Maybe<&2, A>} -> P(k, 1n+n, a) -> P(k, n, b), +e: E, +k: K, +fuel: Nat, +initial: A, hi: P(k, fuel, initial)) -> &n: Nat -> P(k, n, S.Sem.fst(A, Bool, S.Sem.iterateUntil(~A, ~E, ~step, e, fuel, initial))) & Halted(n, S.Sem.snd(A, Bool, S.Sem.iterateUntil(~A, ~E, ~step, e, fuel, initial))):
  iterateUntilFuel.go(~A, ~E, ~step, ~K, ~P, ~h, e, k, fuel, step(e, initial), initial, {==}, hi)

# Two steps in lockstep: both stop, or both move to related states.
def Lock(-A: Data, -B: Data, rel: A -> B -> Data, na: Maybe<&2, A>, nb: Maybe<&2, B>) -> Data:
  match na nb:
    case None{} None{}:
      Unit
    case None{} Some{y}:
      Empty
    case Some{x} None{}:
      Empty
    case Some{x} Some{y}:
      rel(x, y)

# Two bounded loops whose steps keep a relation in lockstep end related, with
# the same flag.
def iterateUntilLockstep.go(~A: Data, ~B: Data, ~E: Data, ~F: Data, ~stepA: @+e: E -> @+s: A -> Maybe<&2, A>, ~stepB: @+f: F -> @+t: B -> Maybe<&2, B>, ~K: Data, ~Rel: @+k: K -> @+s: A -> @+t: B -> Data, ~h: @+e: E -> @+f: F -> @+k: K -> @+a: A -> @+b: B -> Rel(k, a, b) -> Lock(A, B, (+x => +y => Rel(k, x, y)), stepA(e, a), stepB(f, b)), +e: E, +f: F, +k: K, +fuel: Nat, +na: Maybe<&2, A>, +a: A, +nb: Maybe<&2, B>, +b: B, +hr: Rel(k, a, b), +hn: Lock(A, B, (+x => +y => Rel(k, x, y)), na, nb)) -> L.Lean.Prod(Rel(k, S.Sem.fst(A, Bool, S.Sem.iterateUntil.go(~A, ~E, ~stepA, e, fuel, na, a)), S.Sem.fst(B, Bool, S.Sem.iterateUntil.go(~B, ~F, ~stepB, f, fuel, nb, b))), {S.Sem.snd(A, Bool, S.Sem.iterateUntil.go(~A, ~E, ~stepA, e, fuel, na, a)) == S.Sem.snd(B, Bool, S.Sem.iterateUntil.go(~B, ~F, ~stepB, f, fuel, nb, b)) : Bool}):
  match fuel na nb:
    case 0n _ _:
      (hr, {==})
    case 1n+rest None{} None{}:
      (hr, {==})
    case 1n+rest None{} Some{y}:
      L.Lean.Empty.elim(L.Lean.Prod(Rel(k, a, S.Sem.fst(B, Bool, S.Sem.iterateUntil.go(~B, ~F, ~stepB, f, rest, stepB(f, y), y))), {True{} == S.Sem.snd(B, Bool, S.Sem.iterateUntil.go(~B, ~F, ~stepB, f, rest, stepB(f, y), y)) : Bool}), hn)
    case 1n+rest Some{x} None{}:
      L.Lean.Empty.elim(L.Lean.Prod(Rel(k, S.Sem.fst(A, Bool, S.Sem.iterateUntil.go(~A, ~E, ~stepA, e, rest, stepA(e, x), x)), b), {S.Sem.snd(A, Bool, S.Sem.iterateUntil.go(~A, ~E, ~stepA, e, rest, stepA(e, x), x)) == True{} : Bool}), hn)
    case 1n+rest Some{x} Some{y}:
      iterateUntilLockstep.go(~A, ~B, ~E, ~F, ~stepA, ~stepB, ~K, ~Rel, ~h, e, f, k, rest, stepA(e, x), x, stepB(f, y), y, hn, h(e, f, k, x, y, hn))

def iterateUntilLockstep(~A: Data, ~B: Data, ~E: Data, ~F: Data, ~stepA: @+e: E -> @+s: A -> Maybe<&2, A>, ~stepB: @+f: F -> @+t: B -> Maybe<&2, B>, ~K: Data, ~Rel: @+k: K -> @+s: A -> @+t: B -> Data, ~h: @+e: E -> @+f: F -> @+k: K -> @+a: A -> @+b: B -> Rel(k, a, b) -> Lock(A, B, (+x => +y => Rel(k, x, y)), stepA(e, a), stepB(f, b)), +e: E, +f: F, +k: K, +fuel: Nat, +a: A, +b: B, +hr: Rel(k, a, b)) -> L.Lean.Prod(Rel(k, S.Sem.fst(A, Bool, S.Sem.iterateUntil(~A, ~E, ~stepA, e, fuel, a)), S.Sem.fst(B, Bool, S.Sem.iterateUntil(~B, ~F, ~stepB, f, fuel, b))), {S.Sem.snd(A, Bool, S.Sem.iterateUntil(~A, ~E, ~stepA, e, fuel, a)) == S.Sem.snd(B, Bool, S.Sem.iterateUntil(~B, ~F, ~stepB, f, fuel, b)) : Bool}):
  iterateUntilLockstep.go(~A, ~B, ~E, ~F, ~stepA, ~stepB, ~K, ~Rel, ~h, e, f, k, fuel, stepA(e, a), a, stepB(f, b), b, hr, h(e, f, k, a, b, hr))

# A counter plus the fuel left within the starting fuel bounds the counter.
def fuelBound(+a: Nat, +t: Nat, -stopped: Bool, p: &n: Nat -> S.Sem.le(L.Lean.Nat.add(a, n), t) & Halted(n, stopped)) -> S.Sem.le(a, t):
  match p:
    case (n, q):
      match q:
        case (bound, halted):
          fuelLe(a, n, t, bound)

# A measure below the fuel left at the end: the loop stopped.
def fuelStops(-PI: Data, stopped: Bool, +m: Nat, p: &n: Nat -> L.Lean.Prod(PI, S.Sem.lt(m, n)) & Halted(n, stopped)) -> {stopped == True{} : Bool}:
  match p:
    case (n, q):
      match q:
        case (inv, halted):
          match inv:
            case (pi, lt):
              stopsFinish(stopped, n, m, halted, lt)
