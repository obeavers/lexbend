# LexLean Bend prelude: the closed set of Lean 4 denotations the Bend backend
# may name. Every computational def reproduces the defining equations of Lean 4
# Init, so a Lean proof closed by `rfl` or `decide` closes here by `{==}`.
# Each def takes exactly the binders of its registry signature, in order;
# Lean implicit and instance binders are erased (`-x`) except where a proof
# must case on them, which `registry.toml` records under `live`.

import Base

# ---------------------------------------------------------------------------
# Empty elimination and clash motives
# ---------------------------------------------------------------------------

def Lean.Empty.elim(-B: Type, e: Empty) -> B:
  match e:

# Sends 0 to Empty and every successor to Unit, so a proof of `succ n = 0`
# rewrites Empty into Unit.
def Lean.Nat.zero_disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

# Sends true to Empty and false to Unit, so a proof of `false = true` rewrites
# Empty into Unit.
def Lean.Bool.true_disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def Lean.Bool.false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Lean.Bool.true_disc(_)
  Unit{}

# ---------------------------------------------------------------------------
# Bool
# ---------------------------------------------------------------------------

def Lean.Bool.not(a: Bool) -> Bool:
  match a:
    case True{}:
      False{}
    case False{}:
      True{}

def Lean.Bool.and(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      False{}
    case True{}:
      b

def Lean.Bool.or(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      b

# ---------------------------------------------------------------------------
# Nat: Lean recurses on the second argument of add, mul and sub.
# ---------------------------------------------------------------------------

def Lean.Nat.succ(n: Nat) -> Nat:
  1n+n

def Lean.Nat.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def Lean.Nat.add(a: Nat, b: Nat) -> Nat:
  match b:
    case 0n:
      a
    case 1n+p:
      1n+Lean.Nat.add(a, p)

def Lean.Nat.mul(+a: Nat, b: Nat) -> Nat:
  match b:
    case 0n:
      0n
    case 1n+p:
      Lean.Nat.add(Lean.Nat.mul(a, p), a)

def Lean.Nat.sub(a: Nat, b: Nat) -> Nat:
  match b:
    case 0n:
      a
    case 1n+p:
      Lean.Nat.pred(Lean.Nat.sub(a, p))

def Lean.Nat.beq(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+bp:
      False{}
    case 1n+ap 0n:
      False{}
    case 1n+ap 1n+bp:
      Lean.Nat.beq(ap, bp)

def Lean.Nat.ble(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n _:
      True{}
    case 1n+ap 0n:
      False{}
    case 1n+ap 1n+bp:
      Lean.Nat.ble(ap, bp)

def Lean.Nat.blt(a: Nat, b: Nat) -> Bool:
  Lean.Nat.ble(Lean.Nat.add(a, 1n), b)

# Lean's x / 0 = 0 and x % 0 = x; Base's divmod agrees on every closed value.
def Lean.Nat.div(a: Nat, b: Nat) -> Nat:
  Nat.div(a, b)

def Lean.Nat.mod(a: Nat, b: Nat) -> Nat:
  Nat.mod(a, b)

def Lean.Nat.le(a: Nat, b: Nat) -> Type:
  {Lean.Nat.ble(a, b) == True{} : Bool}

def Lean.Nat.lt(a: Nat, b: Nat) -> Type:
  Lean.Nat.le(Lean.Nat.add(a, 1n), b)

def Lean.Nat.ne(a: Nat, b: Nat) -> Type:
  {a == b : Nat} -> Empty

# ---------------------------------------------------------------------------
# Int, in Lean's own representation
# ---------------------------------------------------------------------------

type Lean.Int is Data:
  ofNat{n: Nat}
  negSucc{n: Nat}

def Lean.Int.negOfNat(n: Nat) -> Lean.Int:
  match n:
    case 0n:
      ofNat{0n}
    case 1n+p:
      negSucc{p}

def Lean.Int.natAbs(a: Lean.Int) -> Nat:
  match a:
    case ofNat{n}:
      n
    case negSucc{n}:
      1n+n

def Lean.Int.subNatNat.go(d: Nat, m: Nat, n: Nat) -> Lean.Int:
  match d:
    case 0n:
      ofNat{Lean.Nat.sub(m, n)}
    case 1n+k:
      negSucc{k}

def Lean.Int.subNatNat(+m: Nat, +n: Nat) -> Lean.Int:
  Lean.Int.subNatNat.go(Lean.Nat.sub(n, m), m, n)

def Lean.Int.neg(a: Lean.Int) -> Lean.Int:
  match a:
    case ofNat{n}:
      Lean.Int.negOfNat(n)
    case negSucc{n}:
      ofNat{1n+n}

def Lean.Int.add(a: Lean.Int, b: Lean.Int) -> Lean.Int:
  match a b:
    case ofNat{m} ofNat{n}:
      ofNat{Lean.Nat.add(m, n)}
    case ofNat{m} negSucc{n}:
      Lean.Int.subNatNat(m, 1n+n)
    case negSucc{m} ofNat{n}:
      Lean.Int.subNatNat(n, 1n+m)
    case negSucc{m} negSucc{n}:
      negSucc{1n+Lean.Nat.add(m, n)}

def Lean.Int.sub(a: Lean.Int, b: Lean.Int) -> Lean.Int:
  Lean.Int.add(a, Lean.Int.neg(b))

def Lean.Int.mul(a: Lean.Int, b: Lean.Int) -> Lean.Int:
  match a b:
    case ofNat{m} ofNat{n}:
      ofNat{Lean.Nat.mul(m, n)}
    case ofNat{m} negSucc{n}:
      Lean.Int.negOfNat(Lean.Nat.mul(m, 1n+n))
    case negSucc{m} ofNat{n}:
      Lean.Int.negOfNat(Lean.Nat.mul(1n+m, n))
    case negSucc{m} negSucc{n}:
      ofNat{Lean.Nat.mul(1n+m, 1n+n)}

def Lean.Int.sign(a: Lean.Int) -> Lean.Int:
  match a:
    case ofNat{0n}:
      ofNat{0n}
    case ofNat{1n+p}:
      ofNat{1n}
    case negSucc{n}:
      negSucc{0n}

def Lean.Int.ediv(a: Lean.Int, b: Lean.Int) -> Lean.Int:
  match a b:
    case ofNat{m} ofNat{n}:
      ofNat{Lean.Nat.div(m, n)}
    case ofNat{m} negSucc{n}:
      Lean.Int.neg(ofNat{Lean.Nat.div(m, 1n+n)})
    case negSucc{m} ofNat{0n}:
      ofNat{0n}
    case negSucc{m} ofNat{1n+n}:
      negSucc{Lean.Nat.div(m, 1n+n)}
    case negSucc{m} negSucc{n}:
      ofNat{1n+Lean.Nat.div(m, 1n+n)}

def Lean.Int.emod(a: Lean.Int, +b: Lean.Int) -> Lean.Int:
  match a:
    case ofNat{m}:
      ofNat{Lean.Nat.mod(m, Lean.Int.natAbs(b))}
    case negSucc{m}:
      Lean.Int.subNatNat(Lean.Int.natAbs(b), 1n+Lean.Nat.mod(m, Lean.Int.natAbs(b)))

def Lean.Int.nonneg(a: Lean.Int) -> Bool:
  match a:
    case ofNat{n}:
      True{}
    case negSucc{n}:
      False{}

# Lean: a <= b is NonNeg (b - a), and a < b is a + 1 <= b.
def Lean.Int.le(a: Lean.Int, b: Lean.Int) -> Type:
  {Lean.Int.nonneg(Lean.Int.sub(b, a)) == True{} : Bool}

def Lean.Int.lt(a: Lean.Int, b: Lean.Int) -> Type:
  Lean.Int.le(Lean.Int.add(a, ofNat{1n}), b)

# ---------------------------------------------------------------------------
# List and Prod
# ---------------------------------------------------------------------------

def Lean.Prod(A: Data, B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def Lean.List.nil(-A: Data) -> List<&2, A>:
  Nil{}

def Lean.List.cons(-A: Data, x: A, xs: List<&2, A>) -> List<&2, A>:
  Con{x, xs}

def Lean.List.append(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, Lean.List.append(A, t, ys)}

def Lean.List.length(-A: Data, xs: List<&2, A>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Lean.Nat.add(Lean.List.length(A, t), 1n)

# Lean: elem a (b :: bs) = match a == b with | true => true | false => elem a bs,
# which is `or (a == b) (elem a bs)` by the defining equations of `or`.
def Lean.List.elem(+a: Nat, l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{h, t}:
      Lean.Bool.or(Lean.Nat.beq(a, h), Lean.List.elem(a, t))

def Lean.List.filter.put(h: Nat, keep: Bool, r: List<&2, Nat>) -> List<&2, Nat>:
  match keep:
    case True{}:
      Con{h, r}
    case False{}:
      r

# Lean: xs.removeAll ys = xs.filter (fun x => !ys.elem x).
def Lean.List.removeAll(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Lean.List.filter.put(h, Lean.Bool.not(Lean.List.elem(h, ys)), Lean.List.removeAll(t, ys))

def Lean.List.Mem(+a: Nat, l: List<&2, Nat>) -> Type:
  match l:
    case Nil{}:
      Empty
    case Con{h, t}:
      Either<&1, &1, {a == h : Nat}, Lean.List.Mem(a, t)>

def Lean.List.Subset(a: List<&2, Nat>, b: List<&2, Nat>) -> Type:
  @x: Nat -> Lean.List.Mem(x, a) -> Lean.List.Mem(x, b)

# ---------------------------------------------------------------------------
# Logic
# ---------------------------------------------------------------------------

def Lean.And.intro(-A: Type, -B: Type, left: A, right: B) -> A & B:
  (left, right)

def Lean.Or.inl(-A: Type, -B: Type, h: A) -> Either<&1, &1, A, B>:
  Inl{h}

def Lean.Or.inr(-A: Type, -B: Type, h: B) -> Either<&1, &1, A, B>:
  Inr{h}

def Lean.Iff.intro(-A: Type, -B: Type, mp: A -> B, mpr: B -> A) -> (A -> B) & (B -> A):
  (mp, mpr)

def Lean.Exists.intro(-A: Type, -P: A -> Type, w: A, h: P(w)) -> &x: A -> P(x):
  (w, h)

def Lean.absurd(-A: Type, -B: Type, h1: A, h2: A -> Empty) -> B:
  Lean.Empty.elim(B, h2(h1))

law Lean.rfl:
  for -A: Type
  for -x: A
  {x == x : A}

def Lean.rfl(A, x):
  {==}

law Lean.Eq.symm:
  for -A: Type
  for -x: A
  for -y: A
  for h: {x == y : A}
  {y == x : A}

def Lean.Eq.symm(A, x, y, h):
  %h : {_ == x : A}
  {==}

law Lean.Eq.trans:
  for -A: Type
  for -x: A
  for -y: A
  for -z: A
  for h1: {x == y : A}
  for h2: {y == z : A}
  {x == z : A}

def Lean.Eq.trans(A, x, y, z, h1, h2):
  %h2 : {x == _ : A}
  h1

law Lean.congrArg:
  for -A: Type
  for -B: Type
  for -x: A
  for -y: A
  for f: A -> B
  for h: {x == y : A}
  {f(x) == f(y) : B}

def Lean.congrArg(A, B, x, y, f, h):
  %h : {f(x) == f(_) : B}
  {==}

# ---------------------------------------------------------------------------
# Assumption premises. None is a def a proof may call; a statement that relies
# on one takes it as a template premise `~name` of the type below.
# ---------------------------------------------------------------------------

def Lean.Assume.excluded_middle() -> Type:
  @-P: Type -> Either<&1, &1, P, P -> Empty>

# Lean's `Nonempty A` is a proof-irrelevant Prop; Bend has no Prop universe,
# and a Sigma would make choice provable, so inhabitation is stated as the
# double negation, which classical logic identifies with `Nonempty`.
def Lean.Assume.choice() -> Type:
  @-A: Type -> ((A -> Empty) -> Empty) -> A

def Lean.Assume.propext() -> Type:
  @-P: Type -> @-Q: Type -> ((P -> Q) & (Q -> P)) -> {P == Q : Type}

def Lean.Assume.funext() -> Type:
  @-A: Type -> @-B: (A -> Type) -> @-f: (@x: A -> B(x)) -> @-g: (@x: A -> B(x)) -> (@x: A -> {f(x) == g(x) : B(x)}) -> {f == g : @x: A -> B(x)}

# ---------------------------------------------------------------------------
# Nat lemmas
# ---------------------------------------------------------------------------

law Lean.Nat.add_succ:
  for n: Nat
  for m: Nat
  {Lean.Nat.add(n, Lean.Nat.succ(m)) == Lean.Nat.succ(Lean.Nat.add(n, m)) : Nat}

def Lean.Nat.add_succ(n, m):
  {==}

law Lean.Nat.zero_add:
  for n: Nat
  {Lean.Nat.add(0n, n) == n : Nat}

def Lean.Nat.zero_add(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Lean.Nat.zero_add(p) : {1n+Lean.Nat.add(0n, p) == 1n+_ : Nat}
      {==}

law Lean.Nat.succ_add:
  for +n: Nat
  for m: Nat
  {Lean.Nat.add(Lean.Nat.succ(n), m) == Lean.Nat.succ(Lean.Nat.add(n, m)) : Nat}

def Lean.Nat.succ_add(n, m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      %Lean.Nat.succ_add(n, p) : {1n+Lean.Nat.add(1n+n, p) == 1n+_ : Nat}
      {==}

law Lean.Nat.add_comm:
  for +n: Nat
  for +m: Nat
  {Lean.Nat.add(n, m) == Lean.Nat.add(m, n) : Nat}

def Lean.Nat.add_comm(n, m):
  match m:
    case 0n:
      %Lean.Nat.zero_add(n) : {_ == Lean.Nat.add(0n, n) : Nat}
      {==}
    case 1n+p:
      %Lean.Eq.symm(Nat, Lean.Nat.add(1n+p, n), 1n+Lean.Nat.add(p, n), Lean.Nat.succ_add(p, n)) : {1n+Lean.Nat.add(n, p) == _ : Nat}
      %Lean.Nat.add_comm(n, p) : {1n+Lean.Nat.add(n, p) == 1n+_ : Nat}
      {==}

law Lean.Nat.add_assoc:
  for +n: Nat
  for +m: Nat
  for k: Nat
  {Lean.Nat.add(Lean.Nat.add(n, m), k) == Lean.Nat.add(n, Lean.Nat.add(m, k)) : Nat}

def Lean.Nat.add_assoc(n, m, k):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Lean.Nat.add_assoc(n, m, p) : {1n+Lean.Nat.add(Lean.Nat.add(n, m), p) == 1n+_ : Nat}
      {==}

law Lean.Nat.add_right_comm:
  for +n: Nat
  for +m: Nat
  for +k: Nat
  {Lean.Nat.add(Lean.Nat.add(n, m), k) == Lean.Nat.add(Lean.Nat.add(n, k), m) : Nat}

def Lean.Nat.add_right_comm(n, m, k):
  %Lean.Eq.symm(Nat, Lean.Nat.add(Lean.Nat.add(n, m), k), Lean.Nat.add(n, Lean.Nat.add(m, k)), Lean.Nat.add_assoc(n, m, k)) : {_ == Lean.Nat.add(Lean.Nat.add(n, k), m) : Nat}
  %Lean.Eq.symm(Nat, Lean.Nat.add(Lean.Nat.add(n, k), m), Lean.Nat.add(n, Lean.Nat.add(k, m)), Lean.Nat.add_assoc(n, k, m)) : {Lean.Nat.add(n, Lean.Nat.add(m, k)) == _ : Nat}
  %Lean.Nat.add_comm(m, k) : {Lean.Nat.add(n, Lean.Nat.add(m, k)) == Lean.Nat.add(n, _) : Nat}
  {==}

law Lean.Nat.zero_mul:
  for n: Nat
  {Lean.Nat.mul(0n, n) == 0n : Nat}

def Lean.Nat.zero_mul(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Lean.Nat.zero_mul(p)

law Lean.Nat.succ_mul:
  for +n: Nat
  for +m: Nat
  {Lean.Nat.mul(Lean.Nat.succ(n), m) == Lean.Nat.add(Lean.Nat.mul(n, m), m) : Nat}

def Lean.Nat.succ_mul(n, m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      %Lean.Eq.symm(Nat, Lean.Nat.mul(1n+n, p), Lean.Nat.add(Lean.Nat.mul(n, p), p), Lean.Nat.succ_mul(n, p)) : {1n+Lean.Nat.add(_, n) == 1n+Lean.Nat.add(Lean.Nat.add(Lean.Nat.mul(n, p), n), p) : Nat}
      %Lean.Nat.add_right_comm(Lean.Nat.mul(n, p), p, n) : {1n+Lean.Nat.add(Lean.Nat.add(Lean.Nat.mul(n, p), p), n) == 1n+_ : Nat}
      {==}

law Lean.Nat.mul_one:
  for n: Nat
  {Lean.Nat.mul(n, 1n) == n : Nat}

def Lean.Nat.mul_one(n):
  Lean.Nat.zero_add(n)

law Lean.Nat.one_mul:
  for n: Nat
  {Lean.Nat.mul(1n, n) == n : Nat}

def Lean.Nat.one_mul(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Lean.Nat.one_mul(p) : {1n+Lean.Nat.mul(1n, p) == 1n+_ : Nat}
      {==}

law Lean.Nat.mul_comm:
  for +n: Nat
  for +m: Nat
  {Lean.Nat.mul(n, m) == Lean.Nat.mul(m, n) : Nat}

def Lean.Nat.mul_comm(n, m):
  match m:
    case 0n:
      Lean.Eq.symm(Nat, Lean.Nat.mul(0n, n), 0n, Lean.Nat.zero_mul(n))
    case 1n+p:
      %Lean.Eq.symm(Nat, Lean.Nat.mul(1n+p, n), Lean.Nat.add(Lean.Nat.mul(p, n), n), Lean.Nat.succ_mul(p, n)) : {Lean.Nat.add(Lean.Nat.mul(n, p), n) == _ : Nat}
      %Lean.Nat.mul_comm(n, p) : {Lean.Nat.add(Lean.Nat.mul(n, p), n) == Lean.Nat.add(_, n) : Nat}
      {==}

law Lean.Nat.mul_add:
  for +n: Nat
  for +m: Nat
  for +k: Nat
  {Lean.Nat.mul(n, Lean.Nat.add(m, k)) == Lean.Nat.add(Lean.Nat.mul(n, m), Lean.Nat.mul(n, k)) : Nat}

def Lean.Nat.mul_add(n, m, k):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Lean.Eq.symm(Nat, Lean.Nat.mul(n, Lean.Nat.add(m, p)), Lean.Nat.add(Lean.Nat.mul(n, m), Lean.Nat.mul(n, p)), Lean.Nat.mul_add(n, m, p)) : {Lean.Nat.add(_, n) == Lean.Nat.add(Lean.Nat.mul(n, m), Lean.Nat.add(Lean.Nat.mul(n, p), n)) : Nat}
      Lean.Nat.add_assoc(Lean.Nat.mul(n, m), Lean.Nat.mul(n, p), n)

law Lean.Nat.mul_assoc:
  for +n: Nat
  for +m: Nat
  for +k: Nat
  {Lean.Nat.mul(Lean.Nat.mul(n, m), k) == Lean.Nat.mul(n, Lean.Nat.mul(m, k)) : Nat}

def Lean.Nat.mul_assoc(n, m, k):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Lean.Eq.symm(Nat, Lean.Nat.mul(n, Lean.Nat.add(Lean.Nat.mul(m, p), m)), Lean.Nat.add(Lean.Nat.mul(n, Lean.Nat.mul(m, p)), Lean.Nat.mul(n, m)), Lean.Nat.mul_add(n, Lean.Nat.mul(m, p), m)) : {Lean.Nat.add(Lean.Nat.mul(Lean.Nat.mul(n, m), p), Lean.Nat.mul(n, m)) == _ : Nat}
      %Lean.Nat.mul_assoc(n, m, p) : {Lean.Nat.add(Lean.Nat.mul(Lean.Nat.mul(n, m), p), Lean.Nat.mul(n, m)) == Lean.Nat.add(_, Lean.Nat.mul(n, m)) : Nat}
      {==}

law Lean.Nat.two_mul:
  for +n: Nat
  {Lean.Nat.mul(2n, n) == Lean.Nat.add(n, n) : Nat}

def Lean.Nat.two_mul(n):
  %Lean.Eq.symm(Nat, Lean.Nat.mul(2n, n), Lean.Nat.add(Lean.Nat.mul(1n, n), n), Lean.Nat.succ_mul(1n, n)) : {_ == Lean.Nat.add(n, n) : Nat}
  %Lean.Nat.one_mul(n) : {Lean.Nat.add(Lean.Nat.mul(1n, n), n) == Lean.Nat.add(_, n) : Nat}
  {==}

law Lean.Nat.le_refl:
  for n: Nat
  Lean.Nat.le(n, n)

def Lean.Nat.le_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Lean.Nat.le_refl(p)

law Lean.Nat.le_succ:
  for n: Nat
  Lean.Nat.le(n, Lean.Nat.succ(n))

def Lean.Nat.le_succ(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Lean.Nat.le_succ(p)

law Lean.Nat.le_trans:
  for n: Nat
  for m: Nat
  for k: Nat
  for h1: Lean.Nat.le(n, m)
  for h2: Lean.Nat.le(m, k)
  Lean.Nat.le(n, k)

def Lean.Nat.le_trans(n, m, k, h1, h2):
  match n m k:
    case 0n _ _:
      {==}
    case 1n+a 0n _:
      Lean.Empty.elim(Lean.Nat.le(1n+a, k), Lean.Bool.false_ne_true(h1))
    case 1n+a 1n+b 0n:
      Lean.Empty.elim(Lean.Nat.le(1n+a, 0n), Lean.Bool.false_ne_true(h2))
    case 1n+a 1n+b 1n+c:
      Lean.Nat.le_trans(a, b, c, h1, h2)

law Lean.Nat.zero_lt_succ:
  for n: Nat
  Lean.Nat.lt(0n, Lean.Nat.succ(n))

def Lean.Nat.zero_lt_succ(n):
  {==}

def Lean.Nat.succ_ne_zero.go(-n: Nat, e: {1n+n == 0n : Nat}) -> Empty:
  %e : Lean.Nat.zero_disc(_)
  Unit{}

law Lean.Nat.succ_ne_zero:
  for n: Nat
  Lean.Nat.ne(Lean.Nat.succ(n), 0n)

def Lean.Nat.succ_ne_zero(n):
  e => Lean.Nat.succ_ne_zero.go(n, e)

# ---------------------------------------------------------------------------
# List lemmas
# ---------------------------------------------------------------------------

law Lean.List.length_append:
  for -A: Data
  for xs: List<&2, A>
  for +ys: List<&2, A>
  {Lean.List.length(A, Lean.List.append(A, xs, ys)) == Lean.Nat.add(Lean.List.length(A, xs), Lean.List.length(A, ys)) : Nat}

def Lean.List.length_append(A, xs, ys):
  match xs:
    case Nil{}:
      Lean.Eq.symm(Nat, Lean.Nat.add(0n, Lean.List.length(A, ys)), Lean.List.length(A, ys), Lean.Nat.zero_add(Lean.List.length(A, ys)))
    case Con{h, +t}:
      %Lean.Eq.symm(Nat, Lean.List.length(A, Lean.List.append(A, t, ys)), Lean.Nat.add(Lean.List.length(A, t), Lean.List.length(A, ys)), Lean.List.length_append(A, t, ys)) : {1n+_ == Lean.Nat.add(1n+Lean.List.length(A, t), Lean.List.length(A, ys)) : Nat}
      Lean.Eq.symm(Nat, Lean.Nat.add(1n+Lean.List.length(A, t), Lean.List.length(A, ys)), 1n+Lean.Nat.add(Lean.List.length(A, t), Lean.List.length(A, ys)), Lean.Nat.succ_add(Lean.List.length(A, t), Lean.List.length(A, ys)))
