# LinArith: linear arithmetic over Nat by reflection. Bend has no tactics, so
# the backend lowers `linear_arithmetic` (Lean's `omega`) to one application of
# the law `sound`: the goal and hypotheses are reified into the closed syntax
# below over an environment of Nat atoms, the Rust compiler searches for a
# certificate, and `check` re-validates that certificate by computation, so
# `{==}` proves `check(...) == True{}` on closed data. `sound` turns that
# Bool into the goal, for every environment, with no axiom and no template.
#
# The certificate is a Farkas certificate per branch of the case splits the
# checker performs itself (disjunctions, `!=`, `beq = false`, truncated
# subtraction): Nat multipliers whose combination of the accumulated
# inequalities `p >= n` has equal coefficients on both sides and a smaller
# constant on the larger side, which no valuation can satisfy.

import Base
import ./LexLeanPrelude.bend as L

# ---------------------------------------------------------------------------
# Reified syntax
# ---------------------------------------------------------------------------

# A Nat-valued linear term. Each constructor denotes the exact Lean operation
# the backend emits, so a reified goal is definitionally its Bend statement.
type Term is Data:
  TVar{i: Nat}
  TLit{n: Nat}
  TAdd{a: Term, b: Term}
  TMulL{k: Nat, a: Term}
  TMulR{a: Term, k: Nat}

# A Bool built from Lean's comparison and connective functions.
type BExp is Data:
  BLe{a: Term, b: Term}
  BLt{a: Term, b: Term}
  BEq{a: Term, b: Term}
  BAnd{x: BExp, y: BExp}
  BOr{x: BExp, y: BExp}
  BNot{x: BExp}

# A proposition. `FIs` is a Bool equation `e = v`; `FSub` states that a term
# is the truncated difference of two others, which is how an atom standing
# for a `Nat.sub` application tells the checker what it is.
type Fact is Data:
  FLe{a: Term, b: Term}
  FLt{a: Term, b: Term}
  FEq{a: Term, b: Term}
  FIs{e: BExp, v: Bool}
  FSub{t: Term, a: Term, b: Term}
  FAnd{p: Fact, q: Fact}
  FOr{p: Fact, q: Fact}
  FNot{p: Fact}
  FImp{p: Fact, q: Fact}

# The inequality `p >= n`.
type Ge is Data:
  Ge{p: Term, n: Term}

# What processing one fact yields: inequalities, facts to queue, or a split.
type Out is Data:
  OTake{}
  OGes{gs: List<&2, Ge>}
  OPush{p: Fact, q: Fact}
  OPush1{p: Fact}
  OSplit{p: Fact, q: Fact}

# A certificate: a Farkas multiplier list for the inequalities accumulated
# once the queue is empty (every further split dropped), one certificate for
# each side of the next split, or the next split dropped.
type Cert is Data:
  Leaf{ms: List<&2, Nat>}
  Fork{l: Cert, r: Cert}
  Skip{c: Cert}

# ---------------------------------------------------------------------------
# Semantics
# ---------------------------------------------------------------------------

# An index past the environment reads 0, so every term has a value.
def nth(env: List<&2, Nat>, i: Nat) -> Nat:
  match env:
    case Nil{}:
      0n
    case Con{x, xs}:
      match i:
        case 0n:
          x
        case 1n+j:
          nth(xs, j)

def denote(+env: List<&2, Nat>, t: Term) -> Nat:
  match t:
    case TVar{i}:
      nth(env, i)
    case TLit{n}:
      n
    case TAdd{a, b}:
      L.Lean.Nat.add(denote(env, a), denote(env, b))
    case TMulL{k, a}:
      L.Lean.Nat.mul(k, denote(env, a))
    case TMulR{a, k}:
      L.Lean.Nat.mul(denote(env, a), k)

def beval(+env: List<&2, Nat>, e: BExp) -> Bool:
  match e:
    case BLe{a, b}:
      L.Lean.Nat.ble(denote(env, a), denote(env, b))
    case BLt{a, b}:
      L.Lean.Nat.blt(denote(env, a), denote(env, b))
    case BEq{a, b}:
      L.Lean.Nat.beq(denote(env, a), denote(env, b))
    case BAnd{x, y}:
      L.Lean.Bool.and(beval(env, x), beval(env, y))
    case BOr{x, y}:
      L.Lean.Bool.or(beval(env, x), beval(env, y))
    case BNot{x}:
      L.Lean.Bool.not(beval(env, x))

def holds(+env: List<&2, Nat>, f: Fact) -> Type:
  match f:
    case FLe{a, b}:
      L.Lean.Nat.le(denote(env, a), denote(env, b))
    case FLt{a, b}:
      L.Lean.Nat.lt(denote(env, a), denote(env, b))
    case FEq{a, b}:
      {denote(env, a) == denote(env, b) : Nat}
    case FIs{e, v}:
      {beval(env, e) == v : Bool}
    case FSub{t, a, b}:
      {denote(env, t) == L.Lean.Nat.sub(denote(env, a), denote(env, b)) : Nat}
    case FAnd{p, q}:
      holds(env, p) & holds(env, q)
    case FOr{p, q}:
      Either<&1, &1, holds(env, p), holds(env, q)>
    case FNot{p}:
      holds(env, p) -> Empty
    case FImp{p, q}:
      holds(env, p) -> holds(env, q)

def all_holds(+env: List<&2, Nat>, fs: List<&2, Fact>) -> Type:
  match fs:
    case Nil{}:
      Unit
    case Con{f, rest}:
      holds(env, f) & all_holds(env, rest)

def ge_holds(+env: List<&2, Nat>, g: Ge) -> Type:
  match g:
    case Ge{p, n}:
      L.Lean.Nat.le(denote(env, n), denote(env, p))

def all_ge(+env: List<&2, Nat>, gs: List<&2, Ge>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, rest}:
      ge_holds(env, g) & all_ge(env, rest)

def out_holds(+env: List<&2, Nat>, o: Out) -> Type:
  match o:
    case OTake{}:
      Unit
    case OGes{gs}:
      all_ge(env, gs)
    case OPush{p, q}:
      holds(env, p) & holds(env, q)
    case OPush1{p}:
      holds(env, p)
    case OSplit{p, q}:
      Either<&1, &1, holds(env, p), holds(env, q)>

# The classical negation, written so that it is again a fact the checker
# reads: over Nat every comparison is decidable, so this is exact.
def neg(f: Fact) -> Fact:
  match f:
    case FLe{a, b}:
      FLt{b, a}
    case FLt{a, b}:
      FLe{b, a}
    case FEq{+a, +b}:
      FOr{FLt{a, b}, FLt{b, a}}
    case FIs{e, v}:
      FIs{e, L.Lean.Bool.not(v)}
    case FSub{t, a, b}:
      FNot{FSub{t, a, b}}
    case FAnd{p, q}:
      FOr{neg(p), neg(q)}
    case FOr{p, q}:
      FAnd{neg(p), neg(q)}
    case FNot{p}:
      p
    case FImp{p, q}:
      FAnd{p, neg(q)}

# ---------------------------------------------------------------------------
# The checker
# ---------------------------------------------------------------------------

def step_is(e: BExp, v: Bool) -> Out:
  match e:
    case BLe{a, b}:
      match v:
        case True{}:
          OPush1{FLe{a, b}}
        case False{}:
          OPush1{FLt{b, a}}
    case BLt{a, b}:
      match v:
        case True{}:
          OPush1{FLt{a, b}}
        case False{}:
          OPush1{FLe{b, a}}
    case BEq{a, b}:
      match v:
        case True{}:
          OPush1{FEq{a, b}}
        case False{}:
          OPush1{FNot{FEq{a, b}}}
    case BAnd{x, y}:
      match v:
        case True{}:
          OPush{FIs{x, True{}}, FIs{y, True{}}}
        case False{}:
          OSplit{FIs{x, False{}}, FIs{y, False{}}}
    case BOr{x, y}:
      match v:
        case True{}:
          OSplit{FIs{x, True{}}, FIs{y, True{}}}
        case False{}:
          OPush{FIs{x, False{}}, FIs{y, False{}}}
    case BNot{x}:
      OPush1{FIs{x, L.Lean.Bool.not(v)}}

# A negated subtraction fact says nothing linear, so it is dropped: dropping
# a hypothesis is always sound.
def step_not(p: Fact) -> Out:
  match p:
    case FLe{a, b}:
      OPush1{neg(FLe{a, b})}
    case FLt{a, b}:
      OPush1{neg(FLt{a, b})}
    case FEq{a, b}:
      OPush1{neg(FEq{a, b})}
    case FIs{e, v}:
      OPush1{neg(FIs{e, v})}
    case FSub{t, a, b}:
      OGes{Nil{}}
    case FAnd{x, y}:
      OPush1{neg(FAnd{x, y})}
    case FOr{x, y}:
      OPush1{neg(FOr{x, y})}
    case FNot{x}:
      OPush1{neg(FNot{x})}
    case FImp{x, y}:
      OPush1{neg(FImp{x, y})}

def step(f: Fact) -> Out:
  match f:
    case FLe{a, b}:
      OGes{Con{Ge{b, a}, Nil{}}}
    case FLt{a, b}:
      OGes{Con{Ge{b, TAdd{a, TLit{1n}}}, Nil{}}}
    case FEq{+a, +b}:
      OGes{Con{Ge{a, b}, Con{Ge{b, a}, Nil{}}}}
    case FIs{e, v}:
      step_is(e, v)
    case FSub{+t, +a, +b}:
      OSplit{FAnd{FLe{b, a}, FEq{TAdd{t, b}, a}}, FAnd{FLt{a, b}, FEq{t, TLit{0n}}}}
    case FAnd{p, q}:
      OPush{p, q}
    case FOr{p, q}:
      OSplit{p, q}
    case FNot{p}:
      step_not(p)
    case FImp{p, q}:
      OSplit{neg(p), q}

def app(gs: List<&2, Ge>, acc: List<&2, Ge>) -> List<&2, Ge>:
  match gs:
    case Nil{}:
      acc
    case Con{g, rest}:
      Con{g, app(rest, acc)}

# Linear normal form: a dense coefficient list over the environment and a
# constant, with `denote(t) = konst(t) + dot(coeffs(t), env)`.
def unit(i: Nat) -> List<&2, Nat>:
  match i:
    case 0n:
      Con{1n, Nil{}}
    case 1n+j:
      Con{0n, unit(j)}

def vadd(u: List<&2, Nat>, v: List<&2, Nat>) -> List<&2, Nat>:
  match u:
    case Nil{}:
      v
    case Con{a, ur}:
      match v:
        case Nil{}:
          Con{a, ur}
        case Con{b, vr}:
          Con{L.Lean.Nat.add(a, b), vadd(ur, vr)}

def vscale(+k: Nat, u: List<&2, Nat>) -> List<&2, Nat>:
  match u:
    case Nil{}:
      Nil{}
    case Con{c, r}:
      Con{L.Lean.Nat.mul(k, c), vscale(k, r)}

def coeffs(t: Term) -> List<&2, Nat>:
  match t:
    case TVar{i}:
      unit(i)
    case TLit{n}:
      Nil{}
    case TAdd{a, b}:
      vadd(coeffs(a), coeffs(b))
    case TMulL{k, a}:
      vscale(k, coeffs(a))
    case TMulR{a, k}:
      vscale(k, coeffs(a))

def konst(t: Term) -> Nat:
  match t:
    case TVar{i}:
      0n
    case TLit{n}:
      n
    case TAdd{a, b}:
      L.Lean.Nat.add(konst(a), konst(b))
    case TMulL{k, a}:
      L.Lean.Nat.mul(k, konst(a))
    case TMulR{a, k}:
      L.Lean.Nat.mul(k, konst(a))

def dot(cs: List<&2, Nat>, env: List<&2, Nat>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{c, r}:
      match env:
        case Nil{}:
          0n
        case Con{x, xs}:
          L.Lean.Nat.add(dot(r, xs), L.Lean.Nat.mul(x, c))

# Coefficient lists compare equal up to trailing zeros.
def allz(v: List<&2, Nat>) -> Bool:
  match v:
    case Nil{}:
      True{}
    case Con{c, r}:
      L.Lean.Bool.and(L.Lean.Nat.beq(c, 0n), allz(r))

def veq(u: List<&2, Nat>, v: List<&2, Nat>) -> Bool:
  match u:
    case Nil{}:
      allz(v)
    case Con{a, ur}:
      match v:
        case Nil{}:
          L.Lean.Bool.and(L.Lean.Nat.beq(a, 0n), allz(ur))
        case Con{b, vr}:
          L.Lean.Bool.and(L.Lean.Nat.beq(a, b), veq(ur, vr))

# The two sides of the Farkas combination: the sums of m_i * p_i and of
# m_i * n_i over the accumulated inequalities p_i >= n_i.
def lhs(acc: List<&2, Ge>, ms: List<&2, Nat>) -> Term:
  match acc:
    case Nil{}:
      TLit{0n}
    case Con{g, rest}:
      match g:
        case Ge{p, n}:
          match ms:
            case Nil{}:
              TLit{0n}
            case Con{m, mr}:
              TAdd{TMulL{m, p}, lhs(rest, mr)}

def rhs(acc: List<&2, Ge>, ms: List<&2, Nat>) -> Term:
  match acc:
    case Nil{}:
      TLit{0n}
    case Con{g, rest}:
      match g:
        case Ge{p, n}:
          match ms:
            case Nil{}:
              TLit{0n}
            case Con{m, mr}:
              TAdd{TMulL{m, n}, rhs(rest, mr)}

# The combination says lhs >= rhs; equal coefficients and a smaller constant
# on the left make that impossible.
def farkas(+acc: List<&2, Ge>, +ms: List<&2, Nat>) -> Bool:
  L.Lean.Bool.and(veq(coeffs(lhs(acc, ms)), coeffs(rhs(acc, ms))), L.Lean.Nat.blt(konst(lhs(acc, ms)), konst(rhs(acc, ms))))

# A small-step machine: `o` is the item being integrated, `facts` the queue,
# `acc` the inequalities so far. Fuel bounds the steps, because queueing the
# halves of a conjunction does not shrink the queue structurally; running out
# answers False, which is always safe. A `Leaf` drops every further split
# and checks its multipliers once the queue is empty; a `Fork` takes the next
# split and a `Skip` drops it.
def go(+fuel: Nat, o: Out, +facts: List<&2, Fact>, +acc: List<&2, Ge>, cert: Cert) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+k:
      match o:
        case OTake{}:
          match facts:
            case Nil{}:
              match cert:
                case Leaf{ms}:
                  farkas(acc, ms)
                case Fork{l, r}:
                  False{}
                case Skip{c}:
                  False{}
            case Con{f, rest}:
              go(k, step(f), rest, acc, cert)
        case OGes{gs}:
          go(k, OTake{}, facts, app(gs, acc), cert)
        case OPush{p, q}:
          go(k, OTake{}, Con{p, Con{q, facts}}, acc, cert)
        case OPush1{p}:
          go(k, OTake{}, Con{p, facts}, acc, cert)
        case OSplit{p, q}:
          match cert:
            case Leaf{ms}:
              go(k, OTake{}, facts, acc, Leaf{ms})
            case Fork{l, r}:
              L.Lean.Bool.and(go(k, OTake{}, Con{p, facts}, acc, l), go(k, OTake{}, Con{q, facts}, acc, r))
            case Skip{c}:
              go(k, OTake{}, facts, acc, c)

# The hypotheses and the negated goal are jointly infeasible.
def check(fuel: Nat, goal: Fact, hyps: List<&2, Fact>, cert: Cert) -> Bool:
  go(fuel, OTake{}, Con{neg(goal), hyps}, Nil{}, cert)

# The hypotheses alone are infeasible.
def refutes(fuel: Nat, hyps: List<&2, Fact>, cert: Cert) -> Bool:
  go(fuel, OTake{}, hyps, Nil{}, cert)

# ---------------------------------------------------------------------------
# Equality, Bool and Nat lemmas
# ---------------------------------------------------------------------------

law eqt:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for ab: {a == b : Nat}
  for bc: {b == c : Nat}
  {a == c : Nat}

def eqt(a, b, c, ab, bc):
  Equal.trans(Nat, a, b, c, ab, bc)

law eqs:
  for -a: Nat
  for -b: Nat
  for e: {a == b : Nat}
  {b == a : Nat}

def eqs(a, b, e):
  Equal.sym(Nat, a, b, e)

law succ_cong:
  for -x: Nat
  for -y: Nat
  for e: {x == y : Nat}
  {1n+x == 1n+y : Nat}

def succ_cong(x, y, e):
  %e : {1n+x == 1n+_ : Nat}
  {==}

law succ_inj:
  for -x: Nat
  for -y: Nat
  for e: {1n+x == 1n+y : Nat}
  {x == y : Nat}

def succ_inj(x, y, e):
  Equal.cong(Nat, Nat, L.Lean.Nat.pred, 1n+x, 1n+y, e)

law cong_add2:
  for -x: Nat
  for -x2: Nat
  for -y: Nat
  for -y2: Nat
  for ex: {x == x2 : Nat}
  for ey: {y == y2 : Nat}
  {L.Lean.Nat.add(x, y) == L.Lean.Nat.add(x2, y2) : Nat}

def cong_add2(x, x2, y, y2, ex, ey):
  %ex : {L.Lean.Nat.add(x, y) == L.Lean.Nat.add(_, y2) : Nat}
  %ey : {L.Lean.Nat.add(x, y) == L.Lean.Nat.add(x, _) : Nat}
  {==}

law cong_mul_r:
  for -k: Nat
  for -x: Nat
  for -y: Nat
  for e: {x == y : Nat}
  {L.Lean.Nat.mul(k, x) == L.Lean.Nat.mul(k, y) : Nat}

def cong_mul_r(k, x, y, e):
  %e : {L.Lean.Nat.mul(k, x) == L.Lean.Nat.mul(k, _) : Nat}
  {==}

law true_ne_false:
  for e: {True{} == False{} : Bool}
  Empty

def true_ne_false(e):
  L.Lean.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e))

law bool_and_true:
  for x: Bool
  for y: Bool
  for e: {L.Lean.Bool.and(x, y) == True{} : Bool}
  {x == True{} : Bool} & {y == True{} : Bool}

def bool_and_true(x, y, e):
  match x:
    case True{}:
      ({==}, e)
    case False{}:
      L.Lean.Empty.elim({False{} == True{} : Bool} & {y == True{} : Bool}, L.Lean.Bool.false_ne_true(e))

law and_l:
  for x: Bool
  for y: Bool
  for e: {L.Lean.Bool.and(x, y) == True{} : Bool}
  {x == True{} : Bool}

def and_l(x, y, e):
  match x:
    case True{}:
      {==}
    case False{}:
      L.Lean.Empty.elim({False{} == True{} : Bool}, L.Lean.Bool.false_ne_true(e))

law and_r:
  for x: Bool
  for y: Bool
  for e: {L.Lean.Bool.and(x, y) == True{} : Bool}
  {y == True{} : Bool}

def and_r(x, y, e):
  match x:
    case True{}:
      e
    case False{}:
      L.Lean.Empty.elim({y == True{} : Bool}, L.Lean.Bool.false_ne_true(e))

law bool_and_false:
  for x: Bool
  for y: Bool
  for e: {L.Lean.Bool.and(x, y) == False{} : Bool}
  Either<&1, &1, {x == False{} : Bool}, {y == False{} : Bool}>

def bool_and_false(x, y, e):
  match x:
    case True{}:
      Inr{e}
    case False{}:
      Inl{{==}}

law bool_or_true:
  for x: Bool
  for y: Bool
  for e: {L.Lean.Bool.or(x, y) == True{} : Bool}
  Either<&1, &1, {x == True{} : Bool}, {y == True{} : Bool}>

def bool_or_true(x, y, e):
  match x:
    case True{}:
      Inl{{==}}
    case False{}:
      Inr{e}

law bool_or_false:
  for x: Bool
  for y: Bool
  for e: {L.Lean.Bool.or(x, y) == False{} : Bool}
  {x == False{} : Bool} & {y == False{} : Bool}

def bool_or_false(x, y, e):
  match x:
    case True{}:
      L.Lean.Empty.elim({True{} == False{} : Bool} & {y == False{} : Bool}, true_ne_false(e))
    case False{}:
      ({==}, e)

law bool_not_eq:
  for x: Bool
  for v: Bool
  for e: {L.Lean.Bool.not(x) == v : Bool}
  {x == L.Lean.Bool.not(v) : Bool}

def bool_not_eq(x, v, e):
  match x v:
    case True{} True{}:
      L.Lean.Empty.elim({True{} == False{} : Bool}, L.Lean.Bool.false_ne_true(e))
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      L.Lean.Empty.elim({False{} == True{} : Bool}, true_ne_false(e))

law bool_dec:
  for b: Bool
  for v: Bool
  Either<&1, &1, {b == v : Bool}, {b == L.Lean.Bool.not(v) : Bool}>

def bool_dec(b, v):
  match b v:
    case True{} True{}:
      Inl{{==}}
    case True{} False{}:
      Inr{{==}}
    case False{} True{}:
      Inr{{==}}
    case False{} False{}:
      Inl{{==}}

law bool_excl:
  for b: Bool
  for v: Bool
  for h: {b == v : Bool}
  for n: {b == L.Lean.Bool.not(v) : Bool}
  Empty

def bool_excl(b, v, h, n):
  match b v:
    case True{} True{}:
      true_ne_false(n)
    case True{} False{}:
      true_ne_false(h)
    case False{} True{}:
      L.Lean.Bool.false_ne_true(h)
    case False{} False{}:
      L.Lean.Bool.false_ne_true(n)

law lt_irrefl:
  for n: Nat
  for h: L.Lean.Nat.lt(n, n)
  Empty

def lt_irrefl(n, h):
  match n:
    case 0n:
      L.Lean.Bool.false_ne_true(h)
    case 1n+p:
      lt_irrefl(p, h)

law lt_of_ble_false:
  for a: Nat
  for b: Nat
  for h: {L.Lean.Nat.ble(a, b) == False{} : Bool}
  L.Lean.Nat.lt(b, a)

def lt_of_ble_false(a, b, h):
  match a b:
    case 0n _:
      L.Lean.Empty.elim(L.Lean.Nat.lt(b, 0n), true_ne_false(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lt_of_ble_false(p, q, h)

law eq_of_beq_true:
  for a: Nat
  for b: Nat
  for h: {L.Lean.Nat.beq(a, b) == True{} : Bool}
  {a == b : Nat}

def eq_of_beq_true(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      L.Lean.Empty.elim({0n == 1n+q : Nat}, L.Lean.Bool.false_ne_true(h))
    case 1n+p 0n:
      L.Lean.Empty.elim({1n+p == 0n : Nat}, L.Lean.Bool.false_ne_true(h))
    case 1n+p 1n+q:
      succ_cong(p, q, eq_of_beq_true(p, q, h))

law beq_refl:
  for a: Nat
  {L.Lean.Nat.beq(a, a) == True{} : Bool}

def beq_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      beq_refl(p)

law ne_of_eq_beq:
  for +a: Nat
  for -b: Nat
  for e: {a == b : Nat}
  {L.Lean.Nat.beq(a, b) == False{} : Bool} -> Empty

def ne_of_eq_beq(a, b, e):
  %e : {L.Lean.Nat.beq(a, _) == False{} : Bool} -> Empty
  h => true_ne_false(Equal.trans(Bool, True{}, L.Lean.Nat.beq(a, a), False{}, Equal.sym(Bool, L.Lean.Nat.beq(a, a), True{}, beq_refl(a)), h))

law ne_of_beq_false:
  for +a: Nat
  for -b: Nat
  for h: {L.Lean.Nat.beq(a, b) == False{} : Bool}
  {a == b : Nat} -> Empty

def ne_of_beq_false(a, b, h):
  e => ne_of_eq_beq(a, b, e)(h)

law le_of_eq:
  for +x: Nat
  for -y: Nat
  for e: {x == y : Nat}
  L.Lean.Nat.le(x, y)

def le_of_eq(x, y, e):
  %e : L.Lean.Nat.le(x, _)
  L.Lean.Nat.le_refl(x)

law le_dec:
  for a: Nat
  for b: Nat
  Either<&1, &1, L.Lean.Nat.le(a, b), L.Lean.Nat.lt(b, a)>

def le_dec(a, b):
  match a b:
    case 0n _:
      Inl{{==}}
    case 1n+p 0n:
      Inr{{==}}
    case 1n+p 1n+q:
      le_dec(p, q)

def swap(-X: Type, -Y: Type, d: Either<&1, &1, X, Y>) -> Either<&1, &1, Y, X>:
  match d:
    case Inl{x}:
      Inr{x}
    case Inr{y}:
      Inl{y}

def tri_succ(-p: Nat, -q: Nat, t: Either<&1, &1, {p == q : Nat}, Either<&1, &1, L.Lean.Nat.lt(p, q), L.Lean.Nat.lt(q, p)>>) -> Either<&1, &1, {1n+p == 1n+q : Nat}, Either<&1, &1, L.Lean.Nat.lt(1n+p, 1n+q), L.Lean.Nat.lt(1n+q, 1n+p)>>:
  match t:
    case Inl{e}:
      Inl{succ_cong(p, q, e)}
    case Inr{r}:
      Inr{r}

law tri:
  for a: Nat
  for b: Nat
  Either<&1, &1, {a == b : Nat}, Either<&1, &1, L.Lean.Nat.lt(a, b), L.Lean.Nat.lt(b, a)>>

def tri(a, b):
  match a b:
    case 0n 0n:
      Inl{{==}}
    case 0n 1n+q:
      Inr{Inl{{==}}}
    case 1n+p 0n:
      Inr{Inr{{==}}}
    case 1n+p 1n+q:
      tri_succ(p, q, tri(p, q))

law lt_ne:
  for +x: Nat
  for -y: Nat
  for e: {x == y : Nat}
  L.Lean.Nat.lt(x, y) -> Empty

def lt_ne(x, y, e):
  %e : L.Lean.Nat.lt(x, _) -> Empty
  h => lt_irrefl(x, h)

law eq_lt_absurd:
  for +x: Nat
  for +y: Nat
  for e: {x == y : Nat}
  for n: Either<&1, &1, L.Lean.Nat.lt(x, y), L.Lean.Nat.lt(y, x)>
  Empty

def eq_lt_absurd(x, y, e, n):
  match n:
    case Inl{l}:
      lt_ne(x, y, e)(l)
    case Inr{l}:
      lt_ne(y, x, eqs(x, y, e))(l)

def eqdec_of_tri(+a: Nat, +b: Nat, t: Either<&1, &1, {a == b : Nat}, Either<&1, &1, L.Lean.Nat.lt(a, b), L.Lean.Nat.lt(b, a)>>) -> Either<&1, &1, {a == b : Nat}, {a == b : Nat} -> Empty>:
  match t:
    case Inl{e}:
      Inl{e}
    case Inr{r}:
      Inr{e => eq_lt_absurd(a, b, e, r)}

law nat_eq_dec:
  for +a: Nat
  for +b: Nat
  Either<&1, &1, {a == b : Nat}, {a == b : Nat} -> Empty>

def nat_eq_dec(a, b):
  eqdec_of_tri(a, b, tri(a, b))

law zero_sub:
  for n: Nat
  {L.Lean.Nat.sub(0n, n) == 0n : Nat}

def zero_sub(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %eqs(L.Lean.Nat.sub(0n, p), 0n, zero_sub(p)) : {L.Lean.Nat.pred(_) == 0n : Nat}
      {==}

law succ_sub_succ:
  for +p: Nat
  for q: Nat
  {L.Lean.Nat.sub(1n+p, 1n+q) == L.Lean.Nat.sub(p, q) : Nat}

def succ_sub_succ(p, q):
  match q:
    case 0n:
      {==}
    case 1n+r:
      %succ_sub_succ(p, r) : {L.Lean.Nat.pred(L.Lean.Nat.sub(1n+p, 1n+r)) == L.Lean.Nat.pred(_) : Nat}
      {==}

law sub_add_cancel:
  for +b: Nat
  for +a: Nat
  for h: L.Lean.Nat.le(b, a)
  {L.Lean.Nat.add(L.Lean.Nat.sub(a, b), b) == a : Nat}

def sub_add_cancel(b, a, h):
  match b:
    case 0n:
      {==}
    case 1n+q:
      match a:
        case 0n:
          L.Lean.Empty.elim({L.Lean.Nat.add(L.Lean.Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, L.Lean.Bool.false_ne_true(h))
        case 1n+p:
          %Equal.sym(Nat, L.Lean.Nat.sub(1n+p, 1n+q), L.Lean.Nat.sub(p, q), succ_sub_succ(p, q)) : {1n+L.Lean.Nat.add(_, q) == 1n+p : Nat}
          succ_cong(L.Lean.Nat.add(L.Lean.Nat.sub(p, q), q), p, sub_add_cancel(q, p, h))

law sub_zero_of_lt:
  for +a: Nat
  for +b: Nat
  for h: L.Lean.Nat.lt(a, b)
  {L.Lean.Nat.sub(a, b) == 0n : Nat}

def sub_zero_of_lt(a, b, h):
  match a:
    case 0n:
      zero_sub(b)
    case 1n+p:
      match b:
        case 0n:
          L.Lean.Empty.elim({1n+p == 0n : Nat}, L.Lean.Bool.false_ne_true(h))
        case 1n+q:
          %Equal.sym(Nat, L.Lean.Nat.sub(1n+p, 1n+q), L.Lean.Nat.sub(p, q), succ_sub_succ(p, q)) : {_ == 0n : Nat}
          sub_zero_of_lt(p, q, h)

def sub_split_dec(+a: Nat, +b: Nat, d: Either<&1, &1, {L.Lean.Nat.ble(b, a) == True{} : Bool}, {L.Lean.Nat.ble(L.Lean.Nat.add(a, 1n), b) == True{} : Bool}>) -> Either<&1, &1, L.Lean.Nat.le(b, a) & {L.Lean.Nat.add(L.Lean.Nat.sub(a, b), b) == a : Nat}, L.Lean.Nat.lt(a, b) & {L.Lean.Nat.sub(a, b) == 0n : Nat}>:
  match d:
    case Inl{+h}:
      Inl{(h, sub_add_cancel(b, a, h))}
    case Inr{+h}:
      Inr{(h, sub_zero_of_lt(a, b, h))}

law sub_split:
  for +a: Nat
  for +b: Nat
  for -t: Nat
  for e: {t == L.Lean.Nat.sub(a, b) : Nat}
  Either<&1, &1, L.Lean.Nat.le(b, a) & {L.Lean.Nat.add(t, b) == a : Nat}, L.Lean.Nat.lt(a, b) & {t == 0n : Nat}>

def sub_split(a, b, t, e):
  %Equal.sym(Nat, t, L.Lean.Nat.sub(a, b), e) : Either<&1, &1, L.Lean.Nat.le(b, a) & {L.Lean.Nat.add(_, b) == a : Nat}, L.Lean.Nat.lt(a, b) & {_ == 0n : Nat}>
  sub_split_dec(a, b, le_dec(b, a))

# ---------------------------------------------------------------------------
# Ordering by witnesses: `a <= b` as a gap `d` with `a + d = b`, which turns
# summing and scaling inequalities into equational reasoning.
# ---------------------------------------------------------------------------

def Gap(a: Nat, b: Nat) -> Type:
  &d: Nat -> {L.Lean.Nat.add(a, d) == b : Nat}

def gap_succ(+p: Nat, +q: Nat, g: Gap(p, q)) -> Gap(1n+p, 1n+q):
  (d0, e) = g
  +d = d0
  (d, eqt(L.Lean.Nat.add(1n+p, d), 1n+L.Lean.Nat.add(p, d), 1n+q, L.Lean.Nat.succ_add(p, d), succ_cong(L.Lean.Nat.add(p, d), q, e)))

law le_wit:
  for +a: Nat
  for +b: Nat
  for h: L.Lean.Nat.le(a, b)
  Gap(a, b)

def le_wit(a, b, h):
  match a:
    case 0n:
      (b, L.Lean.Nat.zero_add(b))
    case 1n+p:
      match b:
        case 0n:
          L.Lean.Empty.elim(Gap(1n+p, 0n), L.Lean.Bool.false_ne_true(h))
        case 1n+q:
          gap_succ(p, q, le_wit(p, q, h))

law le_add_right:
  for +a: Nat
  for +d: Nat
  L.Lean.Nat.le(a, L.Lean.Nat.add(a, d))

def le_add_right(a, d):
  match d:
    case 0n:
      L.Lean.Nat.le_refl(a)
    case 1n+q:
      L.Lean.Nat.le_trans(a, L.Lean.Nat.add(a, q), 1n+L.Lean.Nat.add(a, q), le_add_right(a, q), L.Lean.Nat.le_succ(L.Lean.Nat.add(a, q)))

law le_of_gap:
  for +a: Nat
  for -b: Nat
  for g: Gap(a, b)
  L.Lean.Nat.le(a, b)

def le_of_gap(a, b, g):
  (d, e) = g
  %e : L.Lean.Nat.le(a, _)
  le_add_right(a, d)

law cancel_right:
  for -b: Nat
  for -c: Nat
  for a: Nat
  for e: {L.Lean.Nat.add(b, a) == L.Lean.Nat.add(c, a) : Nat}
  {b == c : Nat}

def cancel_right(b, c, a, e):
  match a:
    case 0n:
      e
    case 1n+p:
      cancel_right(b, c, p, succ_inj(L.Lean.Nat.add(b, p), L.Lean.Nat.add(c, p), e))

law swap4:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {L.Lean.Nat.add(L.Lean.Nat.add(a, b), L.Lean.Nat.add(c, d)) == L.Lean.Nat.add(L.Lean.Nat.add(a, c), L.Lean.Nat.add(b, d)) : Nat}

def swap4(a, b, c, d):
  %L.Lean.Nat.add_assoc(L.Lean.Nat.add(a, c), b, d) : {L.Lean.Nat.add(L.Lean.Nat.add(a, b), L.Lean.Nat.add(c, d)) == _ : Nat}
  %L.Lean.Nat.add_assoc(L.Lean.Nat.add(a, b), c, d) : {_ == L.Lean.Nat.add(L.Lean.Nat.add(L.Lean.Nat.add(a, c), b), d) : Nat}
  %L.Lean.Nat.add_right_comm(a, b, c) : {L.Lean.Nat.add(L.Lean.Nat.add(L.Lean.Nat.add(a, b), c), d) == L.Lean.Nat.add(_, d) : Nat}
  {==}

law mul_left_comm:
  for +x: Nat
  for +k: Nat
  for +c: Nat
  {L.Lean.Nat.mul(x, L.Lean.Nat.mul(k, c)) == L.Lean.Nat.mul(k, L.Lean.Nat.mul(x, c)) : Nat}

def mul_left_comm(x, k, c):
  %L.Lean.Nat.mul_assoc(k, x, c) : {L.Lean.Nat.mul(x, L.Lean.Nat.mul(k, c)) == _ : Nat}
  %L.Lean.Nat.mul_assoc(x, k, c) : {_ == L.Lean.Nat.mul(L.Lean.Nat.mul(k, x), c) : Nat}
  %L.Lean.Nat.mul_comm(x, k) : {L.Lean.Nat.mul(L.Lean.Nat.mul(x, k), c) == L.Lean.Nat.mul(_, c) : Nat}
  {==}

# ---------------------------------------------------------------------------
# The normal form is sound
# ---------------------------------------------------------------------------

law dot_unit:
  for i: Nat
  for +env: List<&2, Nat>
  {dot(unit(i), env) == nth(env, i) : Nat}

def dot_unit(i, env):
  match i:
    case 0n:
      match env:
        case Nil{}:
          {==}
        case Con{x, xs}:
          eqt(L.Lean.Nat.add(0n, L.Lean.Nat.add(0n, x)), L.Lean.Nat.add(0n, x), x, L.Lean.Nat.zero_add(L.Lean.Nat.add(0n, x)), L.Lean.Nat.zero_add(x))
    case 1n+j:
      match env:
        case Nil{}:
          {==}
        case Con{x, xs}:
          dot_unit(j, xs)

law dot_vadd:
  for +u: List<&2, Nat>
  for +v: List<&2, Nat>
  for +env: List<&2, Nat>
  {dot(vadd(u, v), env) == L.Lean.Nat.add(dot(u, env), dot(v, env)) : Nat}

def dot_vadd(u, v, env):
  match u:
    case Nil{}:
      eqs(L.Lean.Nat.add(0n, dot(v, env)), dot(v, env), L.Lean.Nat.zero_add(dot(v, env)))
    case Con{a, ur}:
      match v:
        case Nil{}:
          {==}
        case Con{b, vr}:
          match env:
            case Nil{}:
              {==}
            case Con{x, xs}:
              +du = dot(ur, xs)
              +dv = dot(vr, xs)
              +xa = L.Lean.Nat.mul(x, a)
              +xb = L.Lean.Nat.mul(x, b)
              eqt(L.Lean.Nat.add(dot(vadd(ur, vr), xs), L.Lean.Nat.mul(x, L.Lean.Nat.add(a, b))), L.Lean.Nat.add(L.Lean.Nat.add(du, dv), L.Lean.Nat.add(xa, xb)), L.Lean.Nat.add(L.Lean.Nat.add(du, xa), L.Lean.Nat.add(dv, xb)), cong_add2(dot(vadd(ur, vr), xs), L.Lean.Nat.add(du, dv), L.Lean.Nat.mul(x, L.Lean.Nat.add(a, b)), L.Lean.Nat.add(xa, xb), dot_vadd(ur, vr, xs), L.Lean.Nat.mul_add(x, a, b)), swap4(du, dv, xa, xb))

law dot_vscale:
  for +k: Nat
  for +u: List<&2, Nat>
  for +env: List<&2, Nat>
  {dot(vscale(k, u), env) == L.Lean.Nat.mul(k, dot(u, env)) : Nat}

def dot_vscale(k, u, env):
  match u:
    case Nil{}:
      {==}
    case Con{c, r}:
      match env:
        case Nil{}:
          {==}
        case Con{x, xs}:
          +dr = dot(r, xs)
          +xc = L.Lean.Nat.mul(x, c)
          eqt(L.Lean.Nat.add(dot(vscale(k, r), xs), L.Lean.Nat.mul(x, L.Lean.Nat.mul(k, c))), L.Lean.Nat.add(L.Lean.Nat.mul(k, dr), L.Lean.Nat.mul(k, xc)), L.Lean.Nat.mul(k, L.Lean.Nat.add(dr, xc)), cong_add2(dot(vscale(k, r), xs), L.Lean.Nat.mul(k, dr), L.Lean.Nat.mul(x, L.Lean.Nat.mul(k, c)), L.Lean.Nat.mul(k, xc), dot_vscale(k, r, xs), mul_left_comm(x, k, c)), eqs(L.Lean.Nat.mul(k, L.Lean.Nat.add(dr, xc)), L.Lean.Nat.add(L.Lean.Nat.mul(k, dr), L.Lean.Nat.mul(k, xc)), L.Lean.Nat.mul_add(k, dr, xc)))

law mul_norm:
  for +k: Nat
  for -a: Nat
  for +ka: Nat
  for +ca: List<&2, Nat>
  for +env: List<&2, Nat>
  for e: {a == L.Lean.Nat.add(ka, dot(ca, env)) : Nat}
  {L.Lean.Nat.mul(k, a) == L.Lean.Nat.add(L.Lean.Nat.mul(k, ka), dot(vscale(k, ca), env)) : Nat}

def mul_norm(k, a, ka, ca, env, e):
  +da = dot(ca, env)
  eqt(L.Lean.Nat.mul(k, a), L.Lean.Nat.mul(k, L.Lean.Nat.add(ka, da)), L.Lean.Nat.add(L.Lean.Nat.mul(k, ka), dot(vscale(k, ca), env)), cong_mul_r(k, a, L.Lean.Nat.add(ka, da), e), eqt(L.Lean.Nat.mul(k, L.Lean.Nat.add(ka, da)), L.Lean.Nat.add(L.Lean.Nat.mul(k, ka), L.Lean.Nat.mul(k, da)), L.Lean.Nat.add(L.Lean.Nat.mul(k, ka), dot(vscale(k, ca), env)), L.Lean.Nat.mul_add(k, ka, da), cong_add2(L.Lean.Nat.mul(k, ka), L.Lean.Nat.mul(k, ka), L.Lean.Nat.mul(k, da), dot(vscale(k, ca), env), {==}, eqs(dot(vscale(k, ca), env), L.Lean.Nat.mul(k, da), dot_vscale(k, ca, env)))))

law norm_sound:
  for +env: List<&2, Nat>
  for +t: Term
  {denote(env, t) == L.Lean.Nat.add(konst(t), dot(coeffs(t), env)) : Nat}

def norm_sound(env, t):
  match t:
    case TVar{i}:
      eqt(nth(env, i), dot(unit(i), env), L.Lean.Nat.add(0n, dot(unit(i), env)), eqs(dot(unit(i), env), nth(env, i), dot_unit(i, env)), eqs(L.Lean.Nat.add(0n, dot(unit(i), env)), dot(unit(i), env), L.Lean.Nat.zero_add(dot(unit(i), env))))
    case TLit{n}:
      {==}
    case TAdd{a, b}:
      +ka = konst(a)
      +kb = konst(b)
      +da = dot(coeffs(a), env)
      +db = dot(coeffs(b), env)
      eqt(L.Lean.Nat.add(denote(env, a), denote(env, b)), L.Lean.Nat.add(L.Lean.Nat.add(ka, da), L.Lean.Nat.add(kb, db)), L.Lean.Nat.add(L.Lean.Nat.add(ka, kb), dot(vadd(coeffs(a), coeffs(b)), env)), cong_add2(denote(env, a), L.Lean.Nat.add(ka, da), denote(env, b), L.Lean.Nat.add(kb, db), norm_sound(env, a), norm_sound(env, b)), eqt(L.Lean.Nat.add(L.Lean.Nat.add(ka, da), L.Lean.Nat.add(kb, db)), L.Lean.Nat.add(L.Lean.Nat.add(ka, kb), L.Lean.Nat.add(da, db)), L.Lean.Nat.add(L.Lean.Nat.add(ka, kb), dot(vadd(coeffs(a), coeffs(b)), env)), swap4(ka, da, kb, db), cong_add2(L.Lean.Nat.add(ka, kb), L.Lean.Nat.add(ka, kb), L.Lean.Nat.add(da, db), dot(vadd(coeffs(a), coeffs(b)), env), {==}, eqs(dot(vadd(coeffs(a), coeffs(b)), env), L.Lean.Nat.add(da, db), dot_vadd(coeffs(a), coeffs(b), env)))))
    case TMulL{k, a}:
      mul_norm(k, denote(env, a), konst(a), coeffs(a), env, norm_sound(env, a))
    case TMulR{a, k}:
      eqt(L.Lean.Nat.mul(denote(env, a), k), L.Lean.Nat.mul(k, denote(env, a)), L.Lean.Nat.add(L.Lean.Nat.mul(k, konst(a)), dot(vscale(k, coeffs(a)), env)), L.Lean.Nat.mul_comm(denote(env, a), k), mul_norm(k, denote(env, a), konst(a), coeffs(a), env, norm_sound(env, a)))

law allz_sound:
  for +v: List<&2, Nat>
  for +env: List<&2, Nat>
  for +ok: {allz(v) == True{} : Bool}
  {dot(v, env) == 0n : Nat}

def allz_sound(v, env, ok):
  match v:
    case Nil{}:
      {==}
    case Con{c, r}:
      match env:
        case Nil{}:
          {==}
        case Con{x, xs}:
          %eqs(c, 0n, eq_of_beq_true(c, 0n, and_l(L.Lean.Nat.beq(c, 0n), allz(r), ok))) : {L.Lean.Nat.add(dot(r, xs), L.Lean.Nat.mul(x, _)) == 0n : Nat}
          allz_sound(r, xs, and_r(L.Lean.Nat.beq(c, 0n), allz(r), ok))

law veq_sound:
  for +u: List<&2, Nat>
  for +v: List<&2, Nat>
  for +env: List<&2, Nat>
  for +ok: {veq(u, v) == True{} : Bool}
  {dot(u, env) == dot(v, env) : Nat}

def veq_sound(u, v, env, ok):
  match u:
    case Nil{}:
      eqs(dot(v, env), 0n, allz_sound(v, env, ok))
    case Con{a, ur}:
      match v:
        case Nil{}:
          allz_sound(Con{a, ur}, env, ok)
        case Con{b, vr}:
          match env:
            case Nil{}:
              {==}
            case Con{x, xs}:
              cong_add2(dot(ur, xs), dot(vr, xs), L.Lean.Nat.mul(x, a), L.Lean.Nat.mul(x, b), veq_sound(ur, vr, xs, and_r(L.Lean.Nat.beq(a, b), veq(ur, vr), ok)), cong_mul_r(x, a, b, eq_of_beq_true(a, b, and_l(L.Lean.Nat.beq(a, b), veq(ur, vr), ok))))

# ---------------------------------------------------------------------------
# A Farkas certificate is sound
# ---------------------------------------------------------------------------

def gap_comb(+m: Nat, +n1: Nat, +p1: Nat, +nr: Nat, +pr: Nat, g1: Gap(n1, p1), g2: Gap(nr, pr)) -> Gap(L.Lean.Nat.add(L.Lean.Nat.mul(m, n1), nr), L.Lean.Nat.add(L.Lean.Nat.mul(m, p1), pr)):
  (d1a, e1) = g1
  (d2a, e2) = g2
  +d1 = d1a
  +d2 = d2a
  +mn = L.Lean.Nat.mul(m, n1)
  +md = L.Lean.Nat.mul(m, d1)
  (L.Lean.Nat.add(md, d2), eqt(L.Lean.Nat.add(L.Lean.Nat.add(mn, nr), L.Lean.Nat.add(md, d2)), L.Lean.Nat.add(L.Lean.Nat.add(mn, md), L.Lean.Nat.add(nr, d2)), L.Lean.Nat.add(L.Lean.Nat.mul(m, p1), pr), swap4(mn, nr, md, d2), eqt(L.Lean.Nat.add(L.Lean.Nat.add(mn, md), L.Lean.Nat.add(nr, d2)), L.Lean.Nat.add(L.Lean.Nat.mul(m, L.Lean.Nat.add(n1, d1)), L.Lean.Nat.add(nr, d2)), L.Lean.Nat.add(L.Lean.Nat.mul(m, p1), pr), cong_add2(L.Lean.Nat.add(mn, md), L.Lean.Nat.mul(m, L.Lean.Nat.add(n1, d1)), L.Lean.Nat.add(nr, d2), L.Lean.Nat.add(nr, d2), eqs(L.Lean.Nat.mul(m, L.Lean.Nat.add(n1, d1)), L.Lean.Nat.add(mn, md), L.Lean.Nat.mul_add(m, n1, d1)), {==}), cong_add2(L.Lean.Nat.mul(m, L.Lean.Nat.add(n1, d1)), L.Lean.Nat.mul(m, p1), L.Lean.Nat.add(nr, d2), pr, cong_mul_r(m, L.Lean.Nat.add(n1, d1), p1, e1), e2))))

law sum_gap:
  for +env: List<&2, Nat>
  for +acc: List<&2, Ge>
  for +ms: List<&2, Nat>
  for ha: all_ge(env, acc)
  Gap(denote(env, rhs(acc, ms)), denote(env, lhs(acc, ms)))

def sum_gap(env, acc, ms, ha):
  match acc:
    case Nil{}:
      (0n, {==})
    case Con{g, rest}:
      match g:
        case Ge{p, n}:
          match ms:
            case Nil{}:
              (0n, {==})
            case Con{m, mr}:
              (hg, hr) = ha
              gap_comb(m, denote(env, n), denote(env, p), denote(env, rhs(rest, mr)), denote(env, lhs(rest, mr)), le_wit(denote(env, n), denote(env, p), hg), sum_gap(env, rest, mr, hr))

def gap_cast(-a: Nat, -b: Nat, -a2: Nat, -b2: Nat, g: Gap(a, b), ea: {a == a2 : Nat}, eb: {b == b2 : Nat}) -> Gap(a2, b2):
  (d0, e) = g
  +d = d0
  (d, eqt(L.Lean.Nat.add(a2, d), L.Lean.Nat.add(a, d), b2, cong_add2(a2, a, d, d, eqs(a, a2, ea), {==}), eqt(L.Lean.Nat.add(a, d), b, b2, e, eb)))

law lt_gap_absurd:
  for +kp: Nat
  for +kn: Nat
  for g: Gap(kn, kp)
  for lt: L.Lean.Nat.lt(kp, kn)
  Empty

def lt_gap_absurd(kp, kn, g, lt):
  lt_irrefl(kp, L.Lean.Nat.le_trans(L.Lean.Nat.add(kp, 1n), kn, kp, lt, le_of_gap(kn, kp, g)))

law farkas_final:
  for +kp: Nat
  for +kn: Nat
  for +dd: Nat
  for g: Gap(L.Lean.Nat.add(kn, dd), L.Lean.Nat.add(kp, dd))
  for lt: L.Lean.Nat.lt(kp, kn)
  Empty

def farkas_final(kp, kn, dd, g, lt):
  (d0, e) = g
  +d = d0
  lt_gap_absurd(kp, kn, (d, cancel_right(L.Lean.Nat.add(kn, d), kp, dd, eqt(L.Lean.Nat.add(L.Lean.Nat.add(kn, d), dd), L.Lean.Nat.add(L.Lean.Nat.add(kn, dd), d), L.Lean.Nat.add(kp, dd), eqs(L.Lean.Nat.add(L.Lean.Nat.add(kn, dd), d), L.Lean.Nat.add(L.Lean.Nat.add(kn, d), dd), L.Lean.Nat.add_right_comm(kn, dd, d)), e))), lt)

law farkas_sound:
  for +env: List<&2, Nat>
  for +acc: List<&2, Ge>
  for +ms: List<&2, Nat>
  for +ok: {farkas(acc, ms) == True{} : Bool}
  for ha: all_ge(env, acc)
  Empty

def farkas_sound(env, acc, ms, ok, ha):
  +p = lhs(acc, ms)
  +n = rhs(acc, ms)
  +cp = coeffs(p)
  +cn = coeffs(n)
  +kp = konst(p)
  +kn = konst(n)
  +dp = dot(cp, env)
  +dn = dot(cn, env)
  +ed = veq_sound(cp, cn, env, and_l(veq(cp, cn), L.Lean.Nat.blt(kp, kn), ok))
  +en = eqt(denote(env, n), L.Lean.Nat.add(kn, dn), L.Lean.Nat.add(kn, dp), norm_sound(env, n), cong_add2(kn, kn, dn, dp, {==}, eqs(dp, dn, ed)))
  farkas_final(kp, kn, dp, gap_cast(denote(env, n), denote(env, p), L.Lean.Nat.add(kn, dp), L.Lean.Nat.add(kp, dp), sum_gap(env, acc, ms, ha), en, norm_sound(env, p)), and_r(veq(cp, cn), L.Lean.Nat.blt(kp, kn), ok))

law all_ge_app:
  for +env: List<&2, Nat>
  for gs: List<&2, Ge>
  for +acc: List<&2, Ge>
  for h1: all_ge(env, gs)
  for h2: all_ge(env, acc)
  all_ge(env, app(gs, acc))

def all_ge_app(env, gs, acc, h1, h2):
  match gs:
    case Nil{}:
      h2
    case Con{g, rest}:
      (hg, hr) = h1
      (hg, all_ge_app(env, rest, acc, hr, h2))

# ---------------------------------------------------------------------------
# Decision, exclusion and the step lemmas
# ---------------------------------------------------------------------------

law excl:
  for +env: List<&2, Nat>
  for +f: Fact
  for h: holds(env, f)
  for n: holds(env, neg(f))
  Empty

def excl(env, f, h, n):
  match f:
    case FLe{a, b}:
      lt_irrefl(denote(env, b), L.Lean.Nat.le_trans(L.Lean.Nat.add(denote(env, b), 1n), denote(env, a), denote(env, b), n, h))
    case FLt{a, b}:
      lt_irrefl(denote(env, a), L.Lean.Nat.le_trans(L.Lean.Nat.add(denote(env, a), 1n), denote(env, b), denote(env, a), h, n))
    case FEq{a, b}:
      eq_lt_absurd(denote(env, a), denote(env, b), h, n)
    case FIs{e, v}:
      bool_excl(beval(env, e), v, h, n)
    case FSub{t, a, b}:
      n(h)
    case FAnd{p, q}:
      (hp, hq) = h
      match n:
        case Inl{np}:
          excl(env, p, hp, np)
        case Inr{nq}:
          excl(env, q, hq, nq)
    case FOr{p, q}:
      match h:
        case Inl{hp}:
          (np, nq) = n
          excl(env, p, hp, np)
        case Inr{hq}:
          (np, nq) = n
          excl(env, q, hq, nq)
    case FNot{p}:
      h(n)
    case FImp{p, q}:
      (hp, nq) = n
      excl(env, q, h(hp), nq)

def and_dec(-P: Type, -Q: Type, -NP: Type, -NQ: Type, dp: Either<&1, &1, P, NP>, dq: Either<&1, &1, Q, NQ>) -> Either<&1, &1, P & Q, Either<&1, &1, NP, NQ>>:
  match dp:
    case Inl{hp}:
      match dq:
        case Inl{hq}:
          Inl{(hp, hq)}
        case Inr{nq}:
          Inr{Inr{nq}}
    case Inr{np}:
      Inr{Inl{np}}

def or_dec(-P: Type, -Q: Type, -NP: Type, -NQ: Type, dp: Either<&1, &1, P, NP>, dq: Either<&1, &1, Q, NQ>) -> Either<&1, &1, Either<&1, &1, P, Q>, NP & NQ>:
  match dp:
    case Inl{hp}:
      Inl{Inl{hp}}
    case Inr{np}:
      match dq:
        case Inl{hq}:
          Inl{Inr{hq}}
        case Inr{nq}:
          Inr{(np, nq)}

def not_dec(+env: List<&2, Nat>, +p: Fact, d: Either<&1, &1, holds(env, p), holds(env, neg(p))>) -> Either<&1, &1, holds(env, p) -> Empty, holds(env, p)>:
  match d:
    case Inl{hp}:
      Inr{hp}
    case Inr{np}:
      Inl{hp => excl(env, p, hp, np)}

def imp_dec(+env: List<&2, Nat>, +p: Fact, +q: Fact, dp: Either<&1, &1, holds(env, p), holds(env, neg(p))>, dq: Either<&1, &1, holds(env, q), holds(env, neg(q))>) -> Either<&1, &1, holds(env, p) -> holds(env, q), holds(env, p) & holds(env, neg(q))>:
  match dp:
    case Inl{hp}:
      match dq:
        case Inl{hq}:
          Inl{x => hq}
        case Inr{nq}:
          Inr{(hp, nq)}
    case Inr{np}:
      Inl{hp => L.Lean.Empty.elim(holds(env, q), excl(env, p, hp, np))}

law decide:
  for +env: List<&2, Nat>
  for +f: Fact
  Either<&1, &1, holds(env, f), holds(env, neg(f))>

def decide(env, f):
  match f:
    case FLe{a, b}:
      le_dec(denote(env, a), denote(env, b))
    case FLt{a, b}:
      swap(L.Lean.Nat.le(denote(env, b), denote(env, a)), L.Lean.Nat.lt(denote(env, a), denote(env, b)), le_dec(denote(env, b), denote(env, a)))
    case FEq{a, b}:
      tri(denote(env, a), denote(env, b))
    case FIs{e, v}:
      bool_dec(beval(env, e), v)
    case FSub{t, a, b}:
      nat_eq_dec(denote(env, t), L.Lean.Nat.sub(denote(env, a), denote(env, b)))
    case FAnd{p, q}:
      and_dec(holds(env, p), holds(env, q), holds(env, neg(p)), holds(env, neg(q)), decide(env, p), decide(env, q))
    case FOr{p, q}:
      or_dec(holds(env, p), holds(env, q), holds(env, neg(p)), holds(env, neg(q)), decide(env, p), decide(env, q))
    case FNot{p}:
      not_dec(env, p, decide(env, p))
    case FImp{p, q}:
      imp_dec(env, p, q, decide(env, p), decide(env, q))

def not_to_neg(-X: Type, -Y: Type, h: X -> Empty, d: Either<&1, &1, X, Y>) -> Y:
  match d:
    case Inl{x}:
      L.Lean.Empty.elim(Y, h(x))
    case Inr{y}:
      y

law step_is_sound:
  for +env: List<&2, Nat>
  for e: BExp
  for v: Bool
  for h: {beval(env, e) == v : Bool}
  out_holds(env, step_is(e, v))

def step_is_sound(env, e, v, h):
  match e:
    case BLe{a, b}:
      match v:
        case True{}:
          h
        case False{}:
          lt_of_ble_false(denote(env, a), denote(env, b), h)
    case BLt{a, b}:
      match v:
        case True{}:
          h
        case False{}:
          lt_of_ble_false(L.Lean.Nat.add(denote(env, a), 1n), denote(env, b), h)
    case BEq{a, b}:
      match v:
        case True{}:
          eq_of_beq_true(denote(env, a), denote(env, b), h)
        case False{}:
          ne_of_beq_false(denote(env, a), denote(env, b), h)
    case BAnd{x, y}:
      match v:
        case True{}:
          bool_and_true(beval(env, x), beval(env, y), h)
        case False{}:
          bool_and_false(beval(env, x), beval(env, y), h)
    case BOr{x, y}:
      match v:
        case True{}:
          bool_or_true(beval(env, x), beval(env, y), h)
        case False{}:
          bool_or_false(beval(env, x), beval(env, y), h)
    case BNot{x}:
      bool_not_eq(beval(env, x), v, h)

law step_not_sound:
  for +env: List<&2, Nat>
  for p: Fact
  for h: holds(env, p) -> Empty
  out_holds(env, step_not(p))

def step_not_sound(env, p, h):
  match p:
    case FLe{a, b}:
      not_to_neg(holds(env, FLe{a, b}), holds(env, neg(FLe{a, b})), h, decide(env, FLe{a, b}))
    case FLt{a, b}:
      not_to_neg(holds(env, FLt{a, b}), holds(env, neg(FLt{a, b})), h, decide(env, FLt{a, b}))
    case FEq{a, b}:
      not_to_neg(holds(env, FEq{a, b}), holds(env, neg(FEq{a, b})), h, decide(env, FEq{a, b}))
    case FIs{e, v}:
      not_to_neg(holds(env, FIs{e, v}), holds(env, neg(FIs{e, v})), h, decide(env, FIs{e, v}))
    case FSub{t, a, b}:
      Unit{}
    case FAnd{x, y}:
      not_to_neg(holds(env, FAnd{x, y}), holds(env, neg(FAnd{x, y})), h, decide(env, FAnd{x, y}))
    case FOr{x, y}:
      not_to_neg(holds(env, FOr{x, y}), holds(env, neg(FOr{x, y})), h, decide(env, FOr{x, y}))
    case FNot{x}:
      not_to_neg(holds(env, FNot{x}), holds(env, neg(FNot{x})), h, decide(env, FNot{x}))
    case FImp{x, y}:
      not_to_neg(holds(env, FImp{x, y}), holds(env, neg(FImp{x, y})), h, decide(env, FImp{x, y}))

law eq_both:
  for +x: Nat
  for +y: Nat
  for +e: {x == y : Nat}
  L.Lean.Nat.le(y, x) & (L.Lean.Nat.le(x, y) & Unit)

def eq_both(x, y, e):
  (le_of_eq(y, x, eqs(x, y, e)), (le_of_eq(x, y, e), Unit{}))

def imp_split(-P: Type, -Q: Type, -NP: Type, h: P -> Q, d: Either<&1, &1, P, NP>) -> Either<&1, &1, NP, Q>:
  match d:
    case Inl{hp}:
      Inr{h(hp)}
    case Inr{np}:
      Inl{np}

law step_sound:
  for +env: List<&2, Nat>
  for +f: Fact
  for h: holds(env, f)
  out_holds(env, step(f))

def step_sound(env, f, h):
  match f:
    case FLe{a, b}:
      (h, Unit{})
    case FLt{a, b}:
      (h, Unit{})
    case FEq{a, b}:
      eq_both(denote(env, a), denote(env, b), h)
    case FIs{e, v}:
      step_is_sound(env, e, v, h)
    case FSub{t, a, b}:
      sub_split(denote(env, a), denote(env, b), denote(env, t), h)
    case FAnd{p, q}:
      h
    case FOr{p, q}:
      h
    case FNot{p}:
      step_not_sound(env, p, h)
    case FImp{p, q}:
      imp_split(holds(env, p), holds(env, q), holds(env, neg(p)), h, decide(env, p))

# ---------------------------------------------------------------------------
# The machine is sound, and the public laws
# ---------------------------------------------------------------------------

law go_sound:
  for +env: List<&2, Nat>
  for +fuel: Nat
  for o: Out
  for +facts: List<&2, Fact>
  for +acc: List<&2, Ge>
  for cert: Cert
  for +ok: {go(fuel, o, facts, acc, cert) == True{} : Bool}
  for ho: out_holds(env, o)
  for hf: all_holds(env, facts)
  for ha: all_ge(env, acc)
  Empty

def go_sound(env, fuel, o, facts, acc, cert, ok, ho, hf, ha):
  match fuel:
    case 0n:
      L.Lean.Bool.false_ne_true(ok)
    case 1n+k:
      match o:
        case OTake{}:
          match facts:
            case Nil{}:
              match cert:
                case Leaf{ms}:
                  farkas_sound(env, acc, ms, ok, ha)
                case Fork{l, r}:
                  L.Lean.Bool.false_ne_true(ok)
                case Skip{c}:
                  L.Lean.Bool.false_ne_true(ok)
            case Con{f, rest}:
              (hf1, hfr) = hf
              go_sound(env, k, step(f), rest, acc, cert, ok, step_sound(env, f, hf1), hfr, ha)
        case OGes{+gs}:
          go_sound(env, k, OTake{}, facts, app(gs, acc), cert, ok, Unit{}, hf, all_ge_app(env, gs, acc, ho, ha))
        case OPush{p, q}:
          (hp, hq) = ho
          go_sound(env, k, OTake{}, Con{p, Con{q, facts}}, acc, cert, ok, Unit{}, (hp, (hq, hf)), ha)
        case OPush1{p}:
          go_sound(env, k, OTake{}, Con{p, facts}, acc, cert, ok, Unit{}, (ho, hf), ha)
        case OSplit{+p, +q}:
          match cert:
            case Leaf{ms}:
              go_sound(env, k, OTake{}, facts, acc, Leaf{ms}, ok, Unit{}, hf, ha)
            case Fork{+l, +r}:
              match ho:
                case Inl{hp}:
                  go_sound(env, k, OTake{}, Con{p, facts}, acc, l, and_l(go(k, OTake{}, Con{p, facts}, acc, l), go(k, OTake{}, Con{q, facts}, acc, r), ok), Unit{}, (hp, hf), ha)
                case Inr{hq}:
                  go_sound(env, k, OTake{}, Con{q, facts}, acc, r, and_r(go(k, OTake{}, Con{p, facts}, acc, l), go(k, OTake{}, Con{q, facts}, acc, r), ok), Unit{}, (hq, hf), ha)
            case Skip{c}:
              go_sound(env, k, OTake{}, facts, acc, c, ok, Unit{}, hf, ha)

def pick(-X: Type, -Y: Type, d: Either<&1, &1, X, Y>, r: Y -> Empty) -> X:
  match d:
    case Inl{x}:
      x
    case Inr{y}:
      L.Lean.Empty.elim(X, r(y))

# The goal holds at every environment satisfying the hypotheses, whenever the
# closed certificate checks. The backend emits
# `sound(env, goal, hyps, fuel, cert, {==}, (h1, (h2, Unit{})))`.
law sound:
  for +env: List<&2, Nat>
  for +goal: Fact
  for +hyps: List<&2, Fact>
  for fuel: Nat
  for cert: Cert
  for +ok: {check(fuel, goal, hyps, cert) == True{} : Bool}
  for hs: all_holds(env, hyps)
  holds(env, goal)

def sound(env, goal, hyps, fuel, cert, ok, hs):
  pick(holds(env, goal), holds(env, neg(goal)), decide(env, goal), n => go_sound(env, fuel, OTake{}, Con{neg(goal), hyps}, Nil{}, cert, ok, Unit{}, (n, hs), Unit{}))

# Jointly infeasible hypotheses prove anything; the backend uses this for a
# goal with no linear content.
law refute:
  for +env: List<&2, Nat>
  for +hyps: List<&2, Fact>
  for fuel: Nat
  for cert: Cert
  for +ok: {refutes(fuel, hyps, cert) == True{} : Bool}
  for hs: all_holds(env, hyps)
  Empty

def refute(env, hyps, fuel, cert, ok, hs):
  go_sound(env, fuel, OTake{}, hyps, Nil{}, cert, ok, Unit{}, hs, Unit{})
