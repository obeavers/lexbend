# LexLean semantic support: the forms language 2.2 lowers the language-1.2
# semantic surface through, over the Lean denotations of `LexLean.bend`.
# Nothing here is a Lean name; each def is the Bend reading of one fixed
# semantic construct, so a goal Lean closes by `rfl` or `decide` on a closed
# value closes here by `{==}`.

import Base
import ./LexLeanPrelude.bend as L

# `if c then a else b`. Lean's `ite` on a Bool condition selects a branch by
# matching the condition; so does this.
def Sem.ite(-A: Type, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def Sem.fst(-A: Data, -B: Data, p: L.Lean.Prod(A, B)) -> A:
  match p:
    case (a, b):
      a

def Sem.snd(-A: Data, -B: Data, p: L.Lean.Prod(A, B)) -> B:
  match p:
    case (a, b):
      b

# Lean's `Nat.le a b` is `Nat.ble a b = true` here, as in `LexLean.bend`,
# but returned at kind `Data`, so a semantic proof may reuse a hypothesis
# of order as often as Lean's proofs do.
def Sem.le(a: Nat, b: Nat) -> Data:
  {L.Lean.Nat.ble(a, b) == True{} : Bool}

def Sem.lt(a: Nat, b: Nat) -> Data:
  Sem.le(L.Lean.Nat.add(a, 1n), b)

# The four refusals of a model contract and of a reasoner, as their own
# datatypes; Lean spells each as a pair of Booleans.
type Sem.ContractViolation is Data:
  Sem.ContractViolation.precondition{}
  Sem.ContractViolation.input_invariant{}
  Sem.ContractViolation.postcondition{}
  Sem.ContractViolation.output_invariant{}

type Sem.ReasoningFailure is Data:
  Sem.ReasoningFailure.exhausted{}
  Sem.ReasoningFailure.unsolved{}
  Sem.ReasoningFailure.rejected{}
  Sem.ReasoningFailure.invalid_step{}

# `false = true` is absurd: the clash every refutation of a closed Boolean
# fact ends in.
def Sem.false_ne_true(-B: Type, e: {False{} == True{} : Bool}) -> B:
  L.Lean.Empty.elim(B, L.Lean.Bool.false_ne_true(e))

# The higher-order collection primitives, closure-converted as every
# function parameter of language 2.2 is: the step is a closed template
# taking its environment `e` first, so it may run once per element. Each
# computes what Lean's runtime definition does (`List.foldl` for the folds).
def Sem.listFold(~A: Data, ~S: Data, ~E: Data, ~step: @+e: E -> @+s: S -> @+a: A -> S, +e: E, +values: List<&2, A>, +initial: S) -> S:
  match values:
    case Nil{}:
      initial
    case Con{head, tail}:
      Sem.listFold(~A, ~S, ~E, ~step, e, tail, step(e, initial, head))

def Sem.mapFold(~K: Data, ~V: Data, ~S: Data, ~E: Data, ~step: @+e: E -> @+s: S -> @+k: K -> @+v: V -> S, +e: E, +entries: List<&2, L.Lean.Prod(K, V)>, +initial: S) -> S:
  match entries:
    case Nil{}:
      initial
    case Con{head, tail}:
      match head:
        case (key, value):
          Sem.mapFold(~K, ~V, ~S, ~E, ~step, e, tail, step(e, initial, key, value))

def Sem.iterate(~S: Data, ~E: Data, ~step: @+e: E -> @+s: S -> S, +e: E, +count: Nat, +state: S) -> S:
  match count:
    case 0n:
      state
    case 1n+rest:
      Sem.iterate(~S, ~E, ~step, e, rest, step(e, state))

# Lean matches on `step state` before recurring; Bend matches only on a
# parameter, so the step's result is computed one call ahead and passed in.
def Sem.iterateUntil.go(~S: Data, ~E: Data, ~step: @+e: E -> @+s: S -> Maybe<&2, S>, +e: E, +fuel: Nat, +next: Maybe<&2, S>, +state: S) -> L.Lean.Prod(S, Bool):
  match fuel:
    case 0n:
      (state, False{})
    case 1n+rest:
      match next:
        case None{}:
          (state, True{})
        case Some{after}:
          Sem.iterateUntil.go(~S, ~E, ~step, e, rest, step(e, after), after)

def Sem.iterateUntil(~S: Data, ~E: Data, ~step: @+e: E -> @+s: S -> Maybe<&2, S>, +e: E, +fuel: Nat, +state: S) -> L.Lean.Prod(S, Bool):
  Sem.iterateUntil.go(~S, ~E, ~step, e, fuel, step(e, state), state)

# Equalities `linear_arithmetic` preprocesses, as Lean's `omega` does:
# injectivity of `some`, and an equation of pairs from its components.
def Sem.some_value(-A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def Sem.some_inj(-A: Data, +x: A, +y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  %e : {x == Sem.some_value(A, x, _) : A}
  {==}

def Sem.pair_eq(-A: Data, -B: Data, +a: A, +b: B, +c: A, +d: B, p: {a == c : A}, q: {b == d : B}) -> {(a, b) == (c, d) : L.Lean.Prod(A, B)}:
  %p : {(a, b) == (_, d) : L.Lean.Prod(A, B)}
  %q : {(a, b) == (a, _) : L.Lean.Prod(A, B)}
  {==}

# The shape of an embedded tensor, as its artifact check states it: a level
# of nesting has `n` rows of `m` entries when it has `n` rows and each row has
# `m` entries; the next level down is the rows concatenated.
def Sem.flatten(-A: Data, xss: List<&2, List<&2, A>>) -> List<&2, A>:
  match xss:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      L.Lean.List.append(A, h, Sem.flatten(A, t))

def Sem.lengthsAre(-A: Data, xss: List<&2, List<&2, A>>, +m: Nat) -> Bool:
  match xss:
    case Nil{}:
      True{}
    case Con{h, t}:
      L.Lean.Bool.and(L.Lean.Nat.beq(L.Lean.List.length(A, h), m), Sem.lengthsAre(A, t, m))

# Well-founded recursion by proof-carrying fuel. A well-founded definition's
# helper recurses on a fuel and carries `measure < fuel`: `lt_succ` starts it
# at `measure + 1`, `lt_fuel` re-establishes it for the smaller fuel from the
# evidence that the measure decreased, and `lt_zero` makes fuel zero absurd.
def Sem.ble_trans(a: Nat, b: Nat, c: Nat, h1: {L.Lean.Nat.ble(a, b) == True{} : Bool}, h2: {L.Lean.Nat.ble(b, c) == True{} : Bool}) -> {L.Lean.Nat.ble(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      {==}
    case 1n+ap 0n _:
      Sem.false_ne_true({L.Lean.Nat.ble(1n+ap, c) == True{} : Bool}, h1)
    case 1n+ap 1n+bp 0n:
      Sem.false_ne_true({False{} == True{} : Bool}, h2)
    case 1n+ap 1n+bp 1n+cp:
      Sem.ble_trans(ap, bp, cp, h1, h2)

def Sem.ble_refl(m: Nat) -> {L.Lean.Nat.ble(m, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Sem.ble_refl(p)

def Sem.lt_succ(+m: Nat) -> Sem.lt(m, 1n+m):
  Sem.ble_refl(m)

def Sem.lt_fuel(+smaller: Nat, +m: Nat, +p: Nat, decreases: Sem.lt(smaller, m), bound: Sem.lt(m, 1n+p)) -> Sem.lt(smaller, p):
  Sem.ble_trans(L.Lean.Nat.add(smaller, 1n), m, p, decreases, bound)

def Sem.lt_zero(-B: Type, +m: Nat, bound: Sem.lt(m, 0n)) -> B:
  Sem.false_ne_true(B, bound)

# `if c then t else f` where each arm receives its condition's equation, as
# the evidence of a recursive call under it needs.
def Sem.iteDep(-A: Type, +c: Bool, t: {c == True{} : Bool} -> A, f: {c == False{} : Bool} -> A) -> A:
  match c:
    case True{}:
      t({==})
    case False{}:
      f({==})

# Boolean reflection: a validator's `&&` of `Nat.beq` and `Nat.blt` tests
# against a proposition's `/\` of equations and orders, piece by piece.
def Sem.and_left(+a: Bool, +b: Bool, h: {L.Lean.Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      Sem.false_ne_true({False{} == True{} : Bool}, h)
    case True{}:
      {==}

def Sem.and_right(+a: Bool, +b: Bool, h: {L.Lean.Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      Sem.false_ne_true({b == True{} : Bool}, h)
    case True{}:
      h

def Sem.and_intro(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {L.Lean.Bool.and(a, b) == True{} : Bool}:
  match a:
    case False{}:
      Sem.false_ne_true({False{} == True{} : Bool}, ha)
    case True{}:
      hb

def Sem.beq_refl(a: Nat) -> {L.Lean.Nat.beq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Sem.beq_refl(p)

def Sem.beq_eq(a: Nat, b: Nat, h: {L.Lean.Nat.beq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Sem.false_ne_true({0n == 1n+bp : Nat}, h)
    case 1n+ap 0n:
      Sem.false_ne_true({1n+ap == 0n : Nat}, h)
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, x => 1n+x, ap, bp, Sem.beq_eq(ap, bp, h))

def Sem.eq_beq(+a: Nat, +b: Nat, h: {a == b : Nat}) -> {L.Lean.Nat.beq(a, b) == True{} : Bool}:
  %h : {L.Lean.Nat.beq(a, _) == True{} : Bool}
  Sem.beq_refl(a)
