# LexLean Bend runtime: the Lean 4 runtime library of LexLean (namespaces
# LexLeanRuntime, LexLeanCollections, LexLeanModels, LexLeanReasoning) ported
# to Bend 2 for language 2.2. Class-polymorphic Lean functions are
# monomorphized: one def per instance, named `<function>.<Instance>`.
# Every def computes, on every input, the value the Lean definition computes;
# RUNTIME.md states the representations and the per-family fidelity notes, and
# runtime-registry.toml maps each Lean constant to its Bend def.
#
# Fixed-width integers are exact bit vectors (Base `Word(n)`, least significant
# bit first), never Nat-backed, so a closed computation on a 64-bit value costs
# a few hundred Bool steps in the checker instead of a unary Nat of 2^64.

import Base
import ./LexLean.bend as L

# ---------------------------------------------------------------------------
# Word layer: width-generic bit-vector helpers (least significant bit first).
# ---------------------------------------------------------------------------

# Appends `b` as the new most significant bit.
def LexLeanRuntime.W.snoc(n: Nat, w: Word(n), b: Bool) -> Word(1n+n):
  match n:
    case 0n:
      WCon{b, WNil{}}
    case 1n+p:
      match w:
        case WCon{h, t}:
          WCon{h, LexLeanRuntime.W.snoc(p, t, b)}

# Removes the most significant bit.
def LexLeanRuntime.W.dropTop(n: Nat, w: Word(1n+n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{h, t}:
          WCon{h, LexLeanRuntime.W.dropTop(p, t)}

# The low k bits of w, padded with `fill` above bit n: truncation when k <= n,
# zero extension with fill = false, sign extension with fill = the top bit.
def LexLeanRuntime.W.resize(k: Nat, n: Nat, +fill: Bool, w: Word(n)) -> Word(k):
  match k:
    case 0n:
      WNil{}
    case 1n+kp:
      match n:
        case 0n:
          WCon{fill, LexLeanRuntime.W.resize(kp, 0n, fill, WNil{})}
        case 1n+np:
          match w:
            case WCon{h, t}:
              WCon{h, LexLeanRuntime.W.resize(kp, np, fill, t)}

# Lower word first: concat(n, a, m, b) has the bits of a below the bits of b.
def LexLeanRuntime.W.concat(n: Nat, a: Word(n), -m: Nat, b: Word(m)) -> Word(Nat.add(n, m)):
  match n:
    case 0n:
      b
    case 1n+p:
      match a:
        case WCon{h, t}:
          WCon{h, LexLeanRuntime.W.concat(p, t, m, b)}

def LexLeanRuntime.W.msb.go(p: Nat, h: Bool, t: Word(p)) -> Bool:
  match p:
    case 0n:
      h
    case 1n+q:
      match t:
        case WCon{h2, t2}:
          LexLeanRuntime.W.msb.go(q, h2, t2)

def LexLeanRuntime.W.msb(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{h, t}:
          LexLeanRuntime.W.msb.go(p, h, t)

def LexLeanRuntime.W.isZero(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          False{}
        case WCon{False{}, t}:
          LexLeanRuntime.W.isZero(p, t)

def LexLeanRuntime.W.allEq(n: Nat, +s: Bool, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{h, t}:
          L.Lean.Bool.and(Cmp.is_eq(Bool.cmp(h, s)), LexLeanRuntime.W.allEq(p, s, t))

# Every bit at position k or above equals s.
def LexLeanRuntime.W.highSame(k: Nat, n: Nat, +s: Bool, w: Word(n)) -> Bool:
  match k:
    case 0n:
      LexLeanRuntime.W.allEq(n, s, w)
    case 1n+kp:
      match n:
        case 0n:
          True{}
        case 1n+np:
          match w:
            case WCon{h, t}:
              LexLeanRuntime.W.highSame(kp, np, s, t)

def LexLeanRuntime.W.eq(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  Cmp.is_eq(Word.cmp(n, a, b))

def LexLeanRuntime.W.neg(+n: Nat, w: Word(n)) -> Word(n):
  Word.sub(n, Word.zero(n), w)

def LexLeanRuntime.W.scmp.fin(sa: Bool, sb: Bool, c: Cmp) -> Cmp:
  match sa sb:
    case True{} False{}:
      LT{}
    case False{} True{}:
      GT{}
    case True{} True{}:
      c
    case False{} False{}:
      c

# Two's complement order: a negative word is below every non-negative one, and
# within one sign the unsigned order is the signed order.
def LexLeanRuntime.W.scmp(+n: Nat, +a: Word(n), +b: Word(n)) -> Cmp:
  LexLeanRuntime.W.scmp.fin(LexLeanRuntime.W.msb(n, a), LexLeanRuntime.W.msb(n, b), Word.cmp(n, a, b))

def LexLeanRuntime.W.shlBy(k: Nat, +n: Nat, w: Word(n)) -> Word(n):
  match k:
    case 0n:
      w
    case 1n+p:
      LexLeanRuntime.W.shlBy(p, n, Word.shl(n, w))

def LexLeanRuntime.W.lshrBy(k: Nat, +n: Nat, w: Word(n)) -> Word(n):
  match k:
    case 0n:
      w
    case 1n+p:
      LexLeanRuntime.W.lshrBy(p, n, Word.shr(n, w))

def LexLeanRuntime.W.ashr1.go(p: Nat, s: Bool, w: Word(1n+p)) -> Word(1n+p):
  match w:
    case WCon{h, t}:
      LexLeanRuntime.W.snoc(p, t, s)

# One arithmetic right shift: the vacated top bit copies the sign.
def LexLeanRuntime.W.ashr1(+n: Nat, +w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      LexLeanRuntime.W.ashr1.go(p, LexLeanRuntime.W.msb(1n+p, w), w)

def LexLeanRuntime.W.ashrBy(k: Nat, +n: Nat, w: Word(n)) -> Word(n):
  match k:
    case 0n:
      w
    case 1n+p:
      LexLeanRuntime.W.ashrBy(p, n, LexLeanRuntime.W.ashr1(n, w))

# Restoring division of an m-bit dividend by an n-bit divisor, most
# significant dividend bit first. The partial remainder lives in n + 1 bits, so
# doubling it never loses a bit. The divisor must not be zero.
def LexLeanRuntime.W.udivmod.fin(-p: Nat, +n: Nat, ge: Bool, q: Word(p), r2: Word(1n+n), be: Word(1n+n)) -> L.Lean.Prod(Word(1n+p), Word(n)):
  match ge:
    case True{}:
      (WCon{True{}, q}, LexLeanRuntime.W.dropTop(n, Word.sub(1n+n, r2, be)))
    case False{}:
      (WCon{False{}, q}, LexLeanRuntime.W.dropTop(n, r2))

def LexLeanRuntime.W.udivmod.step(-p: Nat, +n: Nat, a0: Bool, b: Word(n), qr: L.Lean.Prod(Word(p), Word(n))) -> L.Lean.Prod(Word(1n+p), Word(n)):
  (q, r) = qr
  +r2 = {WCon{a0, r} : Word(1n+n)}
  +be = LexLeanRuntime.W.snoc(n, b, False{})
  LexLeanRuntime.W.udivmod.fin(p, n, Bool.not(Cmp.is_lt(Word.cmp(1n+n, r2, be))), q, r2, be)

def LexLeanRuntime.W.udivmod(m: Nat, a: Word(m), +n: Nat, +b: Word(n)) -> L.Lean.Prod(Word(m), Word(n)):
  match m:
    case 0n:
      (WNil{}, Word.zero(n))
    case 1n+p:
      match a:
        case WCon{a0, at}:
          LexLeanRuntime.W.udivmod.step(p, n, a0, b, LexLeanRuntime.W.udivmod(p, at, n, b))

def LexLeanRuntime.W.quo(-n: Nat, qr: L.Lean.Prod(Word(n), Word(n))) -> Word(n):
  (q, r) = qr
  q

def LexLeanRuntime.W.rem(-n: Nat, qr: L.Lean.Prod(Word(n), Word(n))) -> Word(n):
  (q, r) = qr
  r

# BitVec.udiv and BitVec.umod: x / 0 = 0 and x % 0 = x.
def LexLeanRuntime.W.udiv.fin(+n: Nat, z: Bool, a: Word(n), b: Word(n)) -> Word(n):
  match z:
    case True{}:
      Word.zero(n)
    case False{}:
      LexLeanRuntime.W.quo(n, LexLeanRuntime.W.udivmod(n, a, n, b))

def LexLeanRuntime.W.udiv(+n: Nat, a: Word(n), +b: Word(n)) -> Word(n):
  LexLeanRuntime.W.udiv.fin(n, LexLeanRuntime.W.isZero(n, b), a, b)

def LexLeanRuntime.W.umod.fin(+n: Nat, z: Bool, a: Word(n), b: Word(n)) -> Word(n):
  match z:
    case True{}:
      a
    case False{}:
      LexLeanRuntime.W.rem(n, LexLeanRuntime.W.udivmod(n, a, n, b))

def LexLeanRuntime.W.umod(+n: Nat, a: Word(n), +b: Word(n)) -> Word(n):
  LexLeanRuntime.W.umod.fin(n, LexLeanRuntime.W.isZero(n, b), a, b)

def LexLeanRuntime.W.negIf(+n: Nat, c: Bool, w: Word(n)) -> Word(n):
  match c:
    case True{}:
      LexLeanRuntime.W.neg(n, w)
    case False{}:
      w

# The magnitude of a two's complement word, as an unsigned word of the same
# width (the minimum maps to itself, which read unsigned is its magnitude).
def LexLeanRuntime.W.abs(+n: Nat, +w: Word(n)) -> Word(n):
  LexLeanRuntime.W.negIf(n, LexLeanRuntime.W.msb(n, w), w)

# BitVec.sdiv: the quotient truncated toward zero; x / 0 = 0.
def LexLeanRuntime.W.sdiv(+n: Nat, +a: Word(n), +b: Word(n)) -> Word(n):
  LexLeanRuntime.W.negIf(n, Bool.xor(LexLeanRuntime.W.msb(n, a), LexLeanRuntime.W.msb(n, b)), LexLeanRuntime.W.udiv(n, LexLeanRuntime.W.abs(n, a), LexLeanRuntime.W.abs(n, b)))

# BitVec.srem: the remainder takes the dividend's sign; x % 0 = x.
def LexLeanRuntime.W.srem(+n: Nat, +a: Word(n), +b: Word(n)) -> Word(n):
  LexLeanRuntime.W.negIf(n, LexLeanRuntime.W.msb(n, a), LexLeanRuntime.W.umod(n, LexLeanRuntime.W.abs(n, a), LexLeanRuntime.W.abs(n, b)))

# The low k bits of w read as a Nat (k is small: a shift amount).
def LexLeanRuntime.W.lowNat(+k: Nat, n: Nat, w: Word(n)) -> Nat:
  Word.to_nat(k, LexLeanRuntime.W.resize(k, n, False{}, w))

# ---------------------------------------------------------------------------
# Nat to Word: n mod 2^k, and whether n < 2^k, by halving.
# ---------------------------------------------------------------------------

# (n mod 2 = 1, n / 2), tail recursive on n.
def LexLeanRuntime.Nat.half.go(n: Nat, q: Nat) -> Bool & Nat:
  match n:
    case 0n:
      (False{}, q)
    case 1n+p:
      match p:
        case 0n:
          (True{}, q)
        case 1n+r:
          LexLeanRuntime.Nat.half.go(r, 1n+q)

def LexLeanRuntime.Nat.half(n: Nat) -> Bool & Nat:
  LexLeanRuntime.Nat.half.go(n, 0n)

def LexLeanRuntime.Nat.toWord.go(k: Nat, bq: Bool & Nat) -> Word(k):
  match k:
    case 0n:
      WNil{}
    case 1n+p:
      (b, q) = bq
      WCon{b, LexLeanRuntime.Nat.toWord.go(p, LexLeanRuntime.Nat.half(q))}

# BitVec.ofNat k n: n mod 2^k.
def LexLeanRuntime.Nat.toWord(k: Nat, n: Nat) -> Word(k):
  LexLeanRuntime.Nat.toWord.go(k, LexLeanRuntime.Nat.half(n))

def LexLeanRuntime.Nat.ltPow2.snd(bq: Bool & Nat) -> Nat:
  (b, q) = bq
  q

# n < 2^k.
def LexLeanRuntime.Nat.ltPow2(k: Nat, n: Nat) -> Bool:
  match k:
    case 0n:
      L.Lean.Nat.beq(n, 0n)
    case 1n+p:
      LexLeanRuntime.Nat.ltPow2(p, LexLeanRuntime.Nat.ltPow2.snd(LexLeanRuntime.Nat.half(n)))

# ---------------------------------------------------------------------------
# Int helpers Lean core defines and the prelude does not.
# ---------------------------------------------------------------------------

def Lean.Int.beq(a: L.Lean.Int, b: L.Lean.Int) -> Bool:
  match a b:
    case L.ofNat{m} L.ofNat{n}:
      L.Lean.Nat.beq(m, n)
    case L.ofNat{m} L.negSucc{n}:
      False{}
    case L.negSucc{m} L.ofNat{n}:
      False{}
    case L.negSucc{m} L.negSucc{n}:
      L.Lean.Nat.beq(m, n)

# Ord Int: the order of the integers.
def Lean.Int.cmp(a: L.Lean.Int, b: L.Lean.Int) -> Cmp:
  match a b:
    case L.ofNat{m} L.ofNat{n}:
      Nat.cmp(m, n)
    case L.ofNat{m} L.negSucc{n}:
      GT{}
    case L.negSucc{m} L.ofNat{n}:
      LT{}
    case L.negSucc{m} L.negSucc{n}:
      Nat.cmp(n, m)

def Lean.Int.decLt(a: L.Lean.Int, b: L.Lean.Int) -> Bool:
  Cmp.is_lt(Lean.Int.cmp(a, b))

def Lean.Int.decLe(a: L.Lean.Int, b: L.Lean.Int) -> Bool:
  Cmp.is_le(Lean.Int.cmp(a, b))

# Int.tdiv and Int.tmod: division rounding toward zero, as Lean defines them.
def Lean.Int.tdiv(a: L.Lean.Int, b: L.Lean.Int) -> L.Lean.Int:
  match a b:
    case L.ofNat{m} L.ofNat{n}:
      L.ofNat{L.Lean.Nat.div(m, n)}
    case L.ofNat{m} L.negSucc{n}:
      L.Lean.Int.negOfNat(L.Lean.Nat.div(m, 1n+n))
    case L.negSucc{m} L.ofNat{n}:
      L.Lean.Int.negOfNat(L.Lean.Nat.div(1n+m, n))
    case L.negSucc{m} L.negSucc{n}:
      L.ofNat{L.Lean.Nat.div(1n+m, 1n+n)}

def Lean.Int.tmod(a: L.Lean.Int, b: L.Lean.Int) -> L.Lean.Int:
  match a b:
    case L.ofNat{m} L.ofNat{n}:
      L.ofNat{L.Lean.Nat.mod(m, n)}
    case L.ofNat{m} L.negSucc{n}:
      L.ofNat{L.Lean.Nat.mod(m, 1n+n)}
    case L.negSucc{m} L.ofNat{n}:
      L.Lean.Int.negOfNat(L.Lean.Nat.mod(1n+m, n))
    case L.negSucc{m} L.negSucc{n}:
      L.Lean.Int.negOfNat(L.Lean.Nat.mod(1n+m, 1n+n))

# Int.repr: toString on Int.
def Lean.Int.repr(a: L.Lean.Int) -> String:
  match a:
    case L.ofNat{n}:
      Nat.show(n)
    case L.negSucc{m}:
      SCon{'-', Nat.show(1n+m)}

# ---------------------------------------------------------------------------
# Prod projections and the Bool conditional used in lemma statements.
# ---------------------------------------------------------------------------

def Lean.Prod.fst(-A: Data, -B: Data, p: L.Lean.Prod(A, B)) -> A:
  (a, b) = p
  a

def Lean.Prod.snd(-A: Data, -B: Data, p: L.Lean.Prod(A, B)) -> B:
  (a, b) = p
  b

# ---------------------------------------------------------------------------
# Fixed-width integers. UInt32 is Base U32 (itself a Word(32n)); the other
# seven are one-field wrappers of a Word, so each type has exactly 2^w values.
# Unsigned types are emitted before signed ones so each sign reinterpretation
# names a type declared above it.
# ---------------------------------------------------------------------------

type Lean.UInt8 is Data:
  Lean.UInt8.mk{bits: Word(8n)}

type Lean.UInt16 is Data:
  Lean.UInt16.mk{bits: Word(16n)}

type Lean.UInt64 is Data:
  Lean.UInt64.mk{bits: Word(64n)}

type Lean.Int8 is Data:
  Lean.Int8.mk{bits: Word(8n)}

type Lean.Int16 is Data:
  Lean.Int16.mk{bits: Word(16n)}

type Lean.Int32 is Data:
  Lean.Int32.mk{bits: Word(32n)}

type Lean.Int64 is Data:
  Lean.Int64.mk{bits: Word(64n)}

# ---- UInt8: exactly 2^8 values, the 8-bit word read unsigned.
def Lean.UInt8.bits(x: Lean.UInt8) -> Word(8n):
  match x:
    case Lean.UInt8.mk{b}:
      b

def Lean.UInt8.ofBits(b: Word(8n)) -> Lean.UInt8:
  Lean.UInt8.mk{b}

# OfNat UInt8 n for a literal n <= 4294967295: n mod 2^8.
def Lean.UInt8.lit(x: U32) -> Lean.UInt8:
  match x:
    case U32{d}:
      Lean.UInt8.mk{LexLeanRuntime.W.resize(8n, 32n, False{}, d)}

def Lean.UInt8.ofNat(n: Nat) -> Lean.UInt8:
  Lean.UInt8.mk{LexLeanRuntime.Nat.toWord(8n, n)}

def Lean.UInt8.toNat(x: Lean.UInt8) -> Nat:
  Word.to_nat(8n, Lean.UInt8.bits(x))

# BitVec.ofInt 8 i, that is i mod 2^8; for i = -(m + 1) that is the complement of m mod 2^8.
def Lean.UInt8.ofInt(i: L.Lean.Int) -> Lean.UInt8:
  match i:
    case L.ofNat{n}:
      Lean.UInt8.mk{LexLeanRuntime.Nat.toWord(8n, n)}
    case L.negSucc{m}:
      Lean.UInt8.mk{Word.not(8n, LexLeanRuntime.Nat.toWord(8n, m))}

def Lean.UInt8.add(a: Lean.UInt8, b: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{Word.add(8n, Lean.UInt8.bits(a), Lean.UInt8.bits(b))}

def Lean.UInt8.sub(a: Lean.UInt8, b: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{Word.sub(8n, Lean.UInt8.bits(a), Lean.UInt8.bits(b))}

def Lean.UInt8.mul(a: Lean.UInt8, b: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{Word.mul(8n, Lean.UInt8.bits(a), Lean.UInt8.bits(b))}

def Lean.UInt8.neg(a: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{LexLeanRuntime.W.neg(8n, Lean.UInt8.bits(a))}

# x / 0 = 0 and x % 0 = x.
def Lean.UInt8.div(a: Lean.UInt8, b: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{LexLeanRuntime.W.udiv(8n, Lean.UInt8.bits(a), Lean.UInt8.bits(b))}

def Lean.UInt8.mod(a: Lean.UInt8, b: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{LexLeanRuntime.W.umod(8n, Lean.UInt8.bits(a), Lean.UInt8.bits(b))}

def Lean.UInt8.land(a: Lean.UInt8, b: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{Word.and(8n, Lean.UInt8.bits(a), Lean.UInt8.bits(b))}

def Lean.UInt8.lor(a: Lean.UInt8, b: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{Word.or(8n, Lean.UInt8.bits(a), Lean.UInt8.bits(b))}

def Lean.UInt8.xor(a: Lean.UInt8, b: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{Word.xor(8n, Lean.UInt8.bits(a), Lean.UInt8.bits(b))}

def Lean.UInt8.complement(a: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{Word.not(8n, Lean.UInt8.bits(a))}

# The shift amount is b mod 8, the low 3 bits of b (umod by a power of two).
def Lean.UInt8.shiftLeft(a: Lean.UInt8, b: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{LexLeanRuntime.W.shlBy(LexLeanRuntime.W.lowNat(3n, 8n, Lean.UInt8.bits(b)), 8n, Lean.UInt8.bits(a))}

def Lean.UInt8.shiftRight(a: Lean.UInt8, b: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mk{LexLeanRuntime.W.lshrBy(LexLeanRuntime.W.lowNat(3n, 8n, Lean.UInt8.bits(b)), 8n, Lean.UInt8.bits(a))}

def Lean.UInt8.beq(a: Lean.UInt8, b: Lean.UInt8) -> Bool:
  LexLeanRuntime.W.eq(8n, Lean.UInt8.bits(a), Lean.UInt8.bits(b))

def Lean.UInt8.cmp(a: Lean.UInt8, b: Lean.UInt8) -> Cmp:
  Word.cmp(8n, Lean.UInt8.bits(a), Lean.UInt8.bits(b))

def Lean.UInt8.decLt(a: Lean.UInt8, b: Lean.UInt8) -> Bool:
  Cmp.is_lt(Lean.UInt8.cmp(a, b))

def Lean.UInt8.decLe(a: Lean.UInt8, b: Lean.UInt8) -> Bool:
  Cmp.is_le(Lean.UInt8.cmp(a, b))

def Lean.UInt8.lt(a: Lean.UInt8, b: Lean.UInt8) -> Type:
  {Lean.UInt8.decLt(a, b) == True{} : Bool}

def Lean.UInt8.le(a: Lean.UInt8, b: Lean.UInt8) -> Type:
  {Lean.UInt8.decLe(a, b) == True{} : Bool}

def Lean.UInt8.toInt8(a: Lean.UInt8) -> Lean.Int8:
  Lean.Int8.mk{Lean.UInt8.bits(a)}

# ---- UInt16: exactly 2^16 values, the 16-bit word read unsigned.
def Lean.UInt16.bits(x: Lean.UInt16) -> Word(16n):
  match x:
    case Lean.UInt16.mk{b}:
      b

def Lean.UInt16.ofBits(b: Word(16n)) -> Lean.UInt16:
  Lean.UInt16.mk{b}

# OfNat UInt16 n for a literal n <= 4294967295: n mod 2^16.
def Lean.UInt16.lit(x: U32) -> Lean.UInt16:
  match x:
    case U32{d}:
      Lean.UInt16.mk{LexLeanRuntime.W.resize(16n, 32n, False{}, d)}

def Lean.UInt16.ofNat(n: Nat) -> Lean.UInt16:
  Lean.UInt16.mk{LexLeanRuntime.Nat.toWord(16n, n)}

def Lean.UInt16.toNat(x: Lean.UInt16) -> Nat:
  Word.to_nat(16n, Lean.UInt16.bits(x))

# BitVec.ofInt 16 i, that is i mod 2^16; for i = -(m + 1) that is the complement of m mod 2^16.
def Lean.UInt16.ofInt(i: L.Lean.Int) -> Lean.UInt16:
  match i:
    case L.ofNat{n}:
      Lean.UInt16.mk{LexLeanRuntime.Nat.toWord(16n, n)}
    case L.negSucc{m}:
      Lean.UInt16.mk{Word.not(16n, LexLeanRuntime.Nat.toWord(16n, m))}

def Lean.UInt16.add(a: Lean.UInt16, b: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{Word.add(16n, Lean.UInt16.bits(a), Lean.UInt16.bits(b))}

def Lean.UInt16.sub(a: Lean.UInt16, b: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{Word.sub(16n, Lean.UInt16.bits(a), Lean.UInt16.bits(b))}

def Lean.UInt16.mul(a: Lean.UInt16, b: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{Word.mul(16n, Lean.UInt16.bits(a), Lean.UInt16.bits(b))}

def Lean.UInt16.neg(a: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{LexLeanRuntime.W.neg(16n, Lean.UInt16.bits(a))}

# x / 0 = 0 and x % 0 = x.
def Lean.UInt16.div(a: Lean.UInt16, b: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{LexLeanRuntime.W.udiv(16n, Lean.UInt16.bits(a), Lean.UInt16.bits(b))}

def Lean.UInt16.mod(a: Lean.UInt16, b: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{LexLeanRuntime.W.umod(16n, Lean.UInt16.bits(a), Lean.UInt16.bits(b))}

def Lean.UInt16.land(a: Lean.UInt16, b: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{Word.and(16n, Lean.UInt16.bits(a), Lean.UInt16.bits(b))}

def Lean.UInt16.lor(a: Lean.UInt16, b: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{Word.or(16n, Lean.UInt16.bits(a), Lean.UInt16.bits(b))}

def Lean.UInt16.xor(a: Lean.UInt16, b: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{Word.xor(16n, Lean.UInt16.bits(a), Lean.UInt16.bits(b))}

def Lean.UInt16.complement(a: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{Word.not(16n, Lean.UInt16.bits(a))}

# The shift amount is b mod 16, the low 4 bits of b (umod by a power of two).
def Lean.UInt16.shiftLeft(a: Lean.UInt16, b: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{LexLeanRuntime.W.shlBy(LexLeanRuntime.W.lowNat(4n, 16n, Lean.UInt16.bits(b)), 16n, Lean.UInt16.bits(a))}

def Lean.UInt16.shiftRight(a: Lean.UInt16, b: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mk{LexLeanRuntime.W.lshrBy(LexLeanRuntime.W.lowNat(4n, 16n, Lean.UInt16.bits(b)), 16n, Lean.UInt16.bits(a))}

def Lean.UInt16.beq(a: Lean.UInt16, b: Lean.UInt16) -> Bool:
  LexLeanRuntime.W.eq(16n, Lean.UInt16.bits(a), Lean.UInt16.bits(b))

def Lean.UInt16.cmp(a: Lean.UInt16, b: Lean.UInt16) -> Cmp:
  Word.cmp(16n, Lean.UInt16.bits(a), Lean.UInt16.bits(b))

def Lean.UInt16.decLt(a: Lean.UInt16, b: Lean.UInt16) -> Bool:
  Cmp.is_lt(Lean.UInt16.cmp(a, b))

def Lean.UInt16.decLe(a: Lean.UInt16, b: Lean.UInt16) -> Bool:
  Cmp.is_le(Lean.UInt16.cmp(a, b))

def Lean.UInt16.lt(a: Lean.UInt16, b: Lean.UInt16) -> Type:
  {Lean.UInt16.decLt(a, b) == True{} : Bool}

def Lean.UInt16.le(a: Lean.UInt16, b: Lean.UInt16) -> Type:
  {Lean.UInt16.decLe(a, b) == True{} : Bool}

def Lean.UInt16.toInt16(a: Lean.UInt16) -> Lean.Int16:
  Lean.Int16.mk{Lean.UInt16.bits(a)}

# ---- UInt32: exactly 2^32 values, the 32-bit word read unsigned.
def Lean.UInt32.bits(x: U32) -> Word(32n):
  match x:
    case U32{b}:
      b

def Lean.UInt32.ofBits(b: Word(32n)) -> U32:
  U32{b}

# OfNat UInt32 n for a literal n <= 4294967295: n mod 2^32.
def Lean.UInt32.lit(x: U32) -> U32:
  match x:
    case U32{d}:
      U32{LexLeanRuntime.W.resize(32n, 32n, False{}, d)}

def Lean.UInt32.ofNat(n: Nat) -> U32:
  U32{LexLeanRuntime.Nat.toWord(32n, n)}

def Lean.UInt32.toNat(x: U32) -> Nat:
  Word.to_nat(32n, Lean.UInt32.bits(x))

# BitVec.ofInt 32 i, that is i mod 2^32; for i = -(m + 1) that is the complement of m mod 2^32.
def Lean.UInt32.ofInt(i: L.Lean.Int) -> U32:
  match i:
    case L.ofNat{n}:
      U32{LexLeanRuntime.Nat.toWord(32n, n)}
    case L.negSucc{m}:
      U32{Word.not(32n, LexLeanRuntime.Nat.toWord(32n, m))}

def Lean.UInt32.add(a: U32, b: U32) -> U32:
  U32{Word.add(32n, Lean.UInt32.bits(a), Lean.UInt32.bits(b))}

def Lean.UInt32.sub(a: U32, b: U32) -> U32:
  U32{Word.sub(32n, Lean.UInt32.bits(a), Lean.UInt32.bits(b))}

def Lean.UInt32.mul(a: U32, b: U32) -> U32:
  U32{Word.mul(32n, Lean.UInt32.bits(a), Lean.UInt32.bits(b))}

def Lean.UInt32.neg(a: U32) -> U32:
  U32{LexLeanRuntime.W.neg(32n, Lean.UInt32.bits(a))}

# x / 0 = 0 and x % 0 = x.
def Lean.UInt32.div(a: U32, b: U32) -> U32:
  U32{LexLeanRuntime.W.udiv(32n, Lean.UInt32.bits(a), Lean.UInt32.bits(b))}

def Lean.UInt32.mod(a: U32, b: U32) -> U32:
  U32{LexLeanRuntime.W.umod(32n, Lean.UInt32.bits(a), Lean.UInt32.bits(b))}

def Lean.UInt32.land(a: U32, b: U32) -> U32:
  U32{Word.and(32n, Lean.UInt32.bits(a), Lean.UInt32.bits(b))}

def Lean.UInt32.lor(a: U32, b: U32) -> U32:
  U32{Word.or(32n, Lean.UInt32.bits(a), Lean.UInt32.bits(b))}

def Lean.UInt32.xor(a: U32, b: U32) -> U32:
  U32{Word.xor(32n, Lean.UInt32.bits(a), Lean.UInt32.bits(b))}

def Lean.UInt32.complement(a: U32) -> U32:
  U32{Word.not(32n, Lean.UInt32.bits(a))}

# The shift amount is b mod 32, the low 5 bits of b (umod by a power of two).
def Lean.UInt32.shiftLeft(a: U32, b: U32) -> U32:
  U32{LexLeanRuntime.W.shlBy(LexLeanRuntime.W.lowNat(5n, 32n, Lean.UInt32.bits(b)), 32n, Lean.UInt32.bits(a))}

def Lean.UInt32.shiftRight(a: U32, b: U32) -> U32:
  U32{LexLeanRuntime.W.lshrBy(LexLeanRuntime.W.lowNat(5n, 32n, Lean.UInt32.bits(b)), 32n, Lean.UInt32.bits(a))}

def Lean.UInt32.beq(a: U32, b: U32) -> Bool:
  LexLeanRuntime.W.eq(32n, Lean.UInt32.bits(a), Lean.UInt32.bits(b))

def Lean.UInt32.cmp(a: U32, b: U32) -> Cmp:
  Word.cmp(32n, Lean.UInt32.bits(a), Lean.UInt32.bits(b))

def Lean.UInt32.decLt(a: U32, b: U32) -> Bool:
  Cmp.is_lt(Lean.UInt32.cmp(a, b))

def Lean.UInt32.decLe(a: U32, b: U32) -> Bool:
  Cmp.is_le(Lean.UInt32.cmp(a, b))

def Lean.UInt32.lt(a: U32, b: U32) -> Type:
  {Lean.UInt32.decLt(a, b) == True{} : Bool}

def Lean.UInt32.le(a: U32, b: U32) -> Type:
  {Lean.UInt32.decLe(a, b) == True{} : Bool}

def Lean.UInt32.toInt32(a: U32) -> Lean.Int32:
  Lean.Int32.mk{Lean.UInt32.bits(a)}

# ---- UInt64: exactly 2^64 values, the 64-bit word read unsigned.
def Lean.UInt64.bits(x: Lean.UInt64) -> Word(64n):
  match x:
    case Lean.UInt64.mk{b}:
      b

def Lean.UInt64.ofBits(b: Word(64n)) -> Lean.UInt64:
  Lean.UInt64.mk{b}

# OfNat UInt64 n for a literal n <= 4294967295: n mod 2^64.
def Lean.UInt64.lit(x: U32) -> Lean.UInt64:
  match x:
    case U32{d}:
      Lean.UInt64.mk{LexLeanRuntime.W.resize(64n, 32n, False{}, d)}

# OfNat UInt64 (hi * 2^32 + lo), for literals above 4294967295.
def Lean.UInt64.lit2(hi: U32, lo: U32) -> Lean.UInt64:
  match hi lo:
    case U32{h} U32{l}:
      Lean.UInt64.mk{LexLeanRuntime.W.concat(32n, l, 32n, h)}

def Lean.UInt64.ofNat(n: Nat) -> Lean.UInt64:
  Lean.UInt64.mk{LexLeanRuntime.Nat.toWord(64n, n)}

def Lean.UInt64.toNat(x: Lean.UInt64) -> Nat:
  Word.to_nat(64n, Lean.UInt64.bits(x))

# BitVec.ofInt 64 i, that is i mod 2^64; for i = -(m + 1) that is the complement of m mod 2^64.
def Lean.UInt64.ofInt(i: L.Lean.Int) -> Lean.UInt64:
  match i:
    case L.ofNat{n}:
      Lean.UInt64.mk{LexLeanRuntime.Nat.toWord(64n, n)}
    case L.negSucc{m}:
      Lean.UInt64.mk{Word.not(64n, LexLeanRuntime.Nat.toWord(64n, m))}

def Lean.UInt64.add(a: Lean.UInt64, b: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{Word.add(64n, Lean.UInt64.bits(a), Lean.UInt64.bits(b))}

def Lean.UInt64.sub(a: Lean.UInt64, b: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{Word.sub(64n, Lean.UInt64.bits(a), Lean.UInt64.bits(b))}

def Lean.UInt64.mul(a: Lean.UInt64, b: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{Word.mul(64n, Lean.UInt64.bits(a), Lean.UInt64.bits(b))}

def Lean.UInt64.neg(a: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{LexLeanRuntime.W.neg(64n, Lean.UInt64.bits(a))}

# x / 0 = 0 and x % 0 = x.
def Lean.UInt64.div(a: Lean.UInt64, b: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{LexLeanRuntime.W.udiv(64n, Lean.UInt64.bits(a), Lean.UInt64.bits(b))}

def Lean.UInt64.mod(a: Lean.UInt64, b: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{LexLeanRuntime.W.umod(64n, Lean.UInt64.bits(a), Lean.UInt64.bits(b))}

def Lean.UInt64.land(a: Lean.UInt64, b: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{Word.and(64n, Lean.UInt64.bits(a), Lean.UInt64.bits(b))}

def Lean.UInt64.lor(a: Lean.UInt64, b: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{Word.or(64n, Lean.UInt64.bits(a), Lean.UInt64.bits(b))}

def Lean.UInt64.xor(a: Lean.UInt64, b: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{Word.xor(64n, Lean.UInt64.bits(a), Lean.UInt64.bits(b))}

def Lean.UInt64.complement(a: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{Word.not(64n, Lean.UInt64.bits(a))}

# The shift amount is b mod 64, the low 6 bits of b (umod by a power of two).
def Lean.UInt64.shiftLeft(a: Lean.UInt64, b: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{LexLeanRuntime.W.shlBy(LexLeanRuntime.W.lowNat(6n, 64n, Lean.UInt64.bits(b)), 64n, Lean.UInt64.bits(a))}

def Lean.UInt64.shiftRight(a: Lean.UInt64, b: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mk{LexLeanRuntime.W.lshrBy(LexLeanRuntime.W.lowNat(6n, 64n, Lean.UInt64.bits(b)), 64n, Lean.UInt64.bits(a))}

def Lean.UInt64.beq(a: Lean.UInt64, b: Lean.UInt64) -> Bool:
  LexLeanRuntime.W.eq(64n, Lean.UInt64.bits(a), Lean.UInt64.bits(b))

def Lean.UInt64.cmp(a: Lean.UInt64, b: Lean.UInt64) -> Cmp:
  Word.cmp(64n, Lean.UInt64.bits(a), Lean.UInt64.bits(b))

def Lean.UInt64.decLt(a: Lean.UInt64, b: Lean.UInt64) -> Bool:
  Cmp.is_lt(Lean.UInt64.cmp(a, b))

def Lean.UInt64.decLe(a: Lean.UInt64, b: Lean.UInt64) -> Bool:
  Cmp.is_le(Lean.UInt64.cmp(a, b))

def Lean.UInt64.lt(a: Lean.UInt64, b: Lean.UInt64) -> Type:
  {Lean.UInt64.decLt(a, b) == True{} : Bool}

def Lean.UInt64.le(a: Lean.UInt64, b: Lean.UInt64) -> Type:
  {Lean.UInt64.decLe(a, b) == True{} : Bool}

def Lean.UInt64.toInt64(a: Lean.UInt64) -> Lean.Int64:
  Lean.Int64.mk{Lean.UInt64.bits(a)}

# ---- Int8: exactly 2^8 values, the 8-bit word read in twos complement.
def Lean.Int8.bits(x: Lean.Int8) -> Word(8n):
  match x:
    case Lean.Int8.mk{b}:
      b

def Lean.Int8.ofBits(b: Word(8n)) -> Lean.Int8:
  Lean.Int8.mk{b}

# OfNat Int8 n for a literal n <= 4294967295: n mod 2^8.
def Lean.Int8.lit(x: U32) -> Lean.Int8:
  match x:
    case U32{d}:
      Lean.Int8.mk{LexLeanRuntime.W.resize(8n, 32n, False{}, d)}

def Lean.Int8.ofNat(n: Nat) -> Lean.Int8:
  Lean.Int8.mk{LexLeanRuntime.Nat.toWord(8n, n)}

def Lean.Int8.toInt.fin(s: Bool, b: Word(8n)) -> L.Lean.Int:
  match s:
    case False{}:
      L.ofNat{Word.to_nat(8n, b)}
    case True{}:
      L.negSucc{Word.to_nat(8n, Word.not(8n, b))}

def Lean.Int8.toInt(x: Lean.Int8) -> L.Lean.Int:
  +b = Lean.Int8.bits(x)
  Lean.Int8.toInt.fin(LexLeanRuntime.W.msb(8n, b), b)

def Lean.Int8.toNatClampNeg.fin(s: Bool, b: Word(8n)) -> Nat:
  match s:
    case False{}:
      Word.to_nat(8n, b)
    case True{}:
      0n

def Lean.Int8.toNatClampNeg(x: Lean.Int8) -> Nat:
  +b = Lean.Int8.bits(x)
  Lean.Int8.toNatClampNeg.fin(LexLeanRuntime.W.msb(8n, b), b)

# BitVec.ofInt 8 i, that is i mod 2^8; for i = -(m + 1) that is the complement of m mod 2^8.
def Lean.Int8.ofInt(i: L.Lean.Int) -> Lean.Int8:
  match i:
    case L.ofNat{n}:
      Lean.Int8.mk{LexLeanRuntime.Nat.toWord(8n, n)}
    case L.negSucc{m}:
      Lean.Int8.mk{Word.not(8n, LexLeanRuntime.Nat.toWord(8n, m))}

def Lean.Int8.add(a: Lean.Int8, b: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{Word.add(8n, Lean.Int8.bits(a), Lean.Int8.bits(b))}

def Lean.Int8.sub(a: Lean.Int8, b: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{Word.sub(8n, Lean.Int8.bits(a), Lean.Int8.bits(b))}

def Lean.Int8.mul(a: Lean.Int8, b: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{Word.mul(8n, Lean.Int8.bits(a), Lean.Int8.bits(b))}

def Lean.Int8.neg(a: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{LexLeanRuntime.W.neg(8n, Lean.Int8.bits(a))}

# BitVec.sdiv and BitVec.srem: truncating; x / 0 = 0, x % 0 = x, min / -1 = min.
def Lean.Int8.div(a: Lean.Int8, b: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{LexLeanRuntime.W.sdiv(8n, Lean.Int8.bits(a), Lean.Int8.bits(b))}

def Lean.Int8.mod(a: Lean.Int8, b: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{LexLeanRuntime.W.srem(8n, Lean.Int8.bits(a), Lean.Int8.bits(b))}

def Lean.Int8.land(a: Lean.Int8, b: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{Word.and(8n, Lean.Int8.bits(a), Lean.Int8.bits(b))}

def Lean.Int8.lor(a: Lean.Int8, b: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{Word.or(8n, Lean.Int8.bits(a), Lean.Int8.bits(b))}

def Lean.Int8.xor(a: Lean.Int8, b: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{Word.xor(8n, Lean.Int8.bits(a), Lean.Int8.bits(b))}

def Lean.Int8.complement(a: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{Word.not(8n, Lean.Int8.bits(a))}

# The shift amount is b mod 8, the low 3 bits of b (smod by a power of two).
def Lean.Int8.shiftLeft(a: Lean.Int8, b: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{LexLeanRuntime.W.shlBy(LexLeanRuntime.W.lowNat(3n, 8n, Lean.Int8.bits(b)), 8n, Lean.Int8.bits(a))}

def Lean.Int8.shiftRight(a: Lean.Int8, b: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mk{LexLeanRuntime.W.ashrBy(LexLeanRuntime.W.lowNat(3n, 8n, Lean.Int8.bits(b)), 8n, Lean.Int8.bits(a))}

def Lean.Int8.beq(a: Lean.Int8, b: Lean.Int8) -> Bool:
  LexLeanRuntime.W.eq(8n, Lean.Int8.bits(a), Lean.Int8.bits(b))

def Lean.Int8.cmp(a: Lean.Int8, b: Lean.Int8) -> Cmp:
  LexLeanRuntime.W.scmp(8n, Lean.Int8.bits(a), Lean.Int8.bits(b))

def Lean.Int8.decLt(a: Lean.Int8, b: Lean.Int8) -> Bool:
  Cmp.is_lt(Lean.Int8.cmp(a, b))

def Lean.Int8.decLe(a: Lean.Int8, b: Lean.Int8) -> Bool:
  Cmp.is_le(Lean.Int8.cmp(a, b))

def Lean.Int8.lt(a: Lean.Int8, b: Lean.Int8) -> Type:
  {Lean.Int8.decLt(a, b) == True{} : Bool}

def Lean.Int8.le(a: Lean.Int8, b: Lean.Int8) -> Type:
  {Lean.Int8.decLe(a, b) == True{} : Bool}

def Lean.Int8.toUInt8(a: Lean.Int8) -> Lean.UInt8:
  Lean.UInt8.mk{Lean.Int8.bits(a)}

# ---- Int16: exactly 2^16 values, the 16-bit word read in twos complement.
def Lean.Int16.bits(x: Lean.Int16) -> Word(16n):
  match x:
    case Lean.Int16.mk{b}:
      b

def Lean.Int16.ofBits(b: Word(16n)) -> Lean.Int16:
  Lean.Int16.mk{b}

# OfNat Int16 n for a literal n <= 4294967295: n mod 2^16.
def Lean.Int16.lit(x: U32) -> Lean.Int16:
  match x:
    case U32{d}:
      Lean.Int16.mk{LexLeanRuntime.W.resize(16n, 32n, False{}, d)}

def Lean.Int16.ofNat(n: Nat) -> Lean.Int16:
  Lean.Int16.mk{LexLeanRuntime.Nat.toWord(16n, n)}

def Lean.Int16.toInt.fin(s: Bool, b: Word(16n)) -> L.Lean.Int:
  match s:
    case False{}:
      L.ofNat{Word.to_nat(16n, b)}
    case True{}:
      L.negSucc{Word.to_nat(16n, Word.not(16n, b))}

def Lean.Int16.toInt(x: Lean.Int16) -> L.Lean.Int:
  +b = Lean.Int16.bits(x)
  Lean.Int16.toInt.fin(LexLeanRuntime.W.msb(16n, b), b)

def Lean.Int16.toNatClampNeg.fin(s: Bool, b: Word(16n)) -> Nat:
  match s:
    case False{}:
      Word.to_nat(16n, b)
    case True{}:
      0n

def Lean.Int16.toNatClampNeg(x: Lean.Int16) -> Nat:
  +b = Lean.Int16.bits(x)
  Lean.Int16.toNatClampNeg.fin(LexLeanRuntime.W.msb(16n, b), b)

# BitVec.ofInt 16 i, that is i mod 2^16; for i = -(m + 1) that is the complement of m mod 2^16.
def Lean.Int16.ofInt(i: L.Lean.Int) -> Lean.Int16:
  match i:
    case L.ofNat{n}:
      Lean.Int16.mk{LexLeanRuntime.Nat.toWord(16n, n)}
    case L.negSucc{m}:
      Lean.Int16.mk{Word.not(16n, LexLeanRuntime.Nat.toWord(16n, m))}

def Lean.Int16.add(a: Lean.Int16, b: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{Word.add(16n, Lean.Int16.bits(a), Lean.Int16.bits(b))}

def Lean.Int16.sub(a: Lean.Int16, b: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{Word.sub(16n, Lean.Int16.bits(a), Lean.Int16.bits(b))}

def Lean.Int16.mul(a: Lean.Int16, b: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{Word.mul(16n, Lean.Int16.bits(a), Lean.Int16.bits(b))}

def Lean.Int16.neg(a: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{LexLeanRuntime.W.neg(16n, Lean.Int16.bits(a))}

# BitVec.sdiv and BitVec.srem: truncating; x / 0 = 0, x % 0 = x, min / -1 = min.
def Lean.Int16.div(a: Lean.Int16, b: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{LexLeanRuntime.W.sdiv(16n, Lean.Int16.bits(a), Lean.Int16.bits(b))}

def Lean.Int16.mod(a: Lean.Int16, b: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{LexLeanRuntime.W.srem(16n, Lean.Int16.bits(a), Lean.Int16.bits(b))}

def Lean.Int16.land(a: Lean.Int16, b: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{Word.and(16n, Lean.Int16.bits(a), Lean.Int16.bits(b))}

def Lean.Int16.lor(a: Lean.Int16, b: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{Word.or(16n, Lean.Int16.bits(a), Lean.Int16.bits(b))}

def Lean.Int16.xor(a: Lean.Int16, b: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{Word.xor(16n, Lean.Int16.bits(a), Lean.Int16.bits(b))}

def Lean.Int16.complement(a: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{Word.not(16n, Lean.Int16.bits(a))}

# The shift amount is b mod 16, the low 4 bits of b (smod by a power of two).
def Lean.Int16.shiftLeft(a: Lean.Int16, b: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{LexLeanRuntime.W.shlBy(LexLeanRuntime.W.lowNat(4n, 16n, Lean.Int16.bits(b)), 16n, Lean.Int16.bits(a))}

def Lean.Int16.shiftRight(a: Lean.Int16, b: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mk{LexLeanRuntime.W.ashrBy(LexLeanRuntime.W.lowNat(4n, 16n, Lean.Int16.bits(b)), 16n, Lean.Int16.bits(a))}

def Lean.Int16.beq(a: Lean.Int16, b: Lean.Int16) -> Bool:
  LexLeanRuntime.W.eq(16n, Lean.Int16.bits(a), Lean.Int16.bits(b))

def Lean.Int16.cmp(a: Lean.Int16, b: Lean.Int16) -> Cmp:
  LexLeanRuntime.W.scmp(16n, Lean.Int16.bits(a), Lean.Int16.bits(b))

def Lean.Int16.decLt(a: Lean.Int16, b: Lean.Int16) -> Bool:
  Cmp.is_lt(Lean.Int16.cmp(a, b))

def Lean.Int16.decLe(a: Lean.Int16, b: Lean.Int16) -> Bool:
  Cmp.is_le(Lean.Int16.cmp(a, b))

def Lean.Int16.lt(a: Lean.Int16, b: Lean.Int16) -> Type:
  {Lean.Int16.decLt(a, b) == True{} : Bool}

def Lean.Int16.le(a: Lean.Int16, b: Lean.Int16) -> Type:
  {Lean.Int16.decLe(a, b) == True{} : Bool}

def Lean.Int16.toUInt16(a: Lean.Int16) -> Lean.UInt16:
  Lean.UInt16.mk{Lean.Int16.bits(a)}

# ---- Int32: exactly 2^32 values, the 32-bit word read in twos complement.
def Lean.Int32.bits(x: Lean.Int32) -> Word(32n):
  match x:
    case Lean.Int32.mk{b}:
      b

def Lean.Int32.ofBits(b: Word(32n)) -> Lean.Int32:
  Lean.Int32.mk{b}

# OfNat Int32 n for a literal n <= 4294967295: n mod 2^32.
def Lean.Int32.lit(x: U32) -> Lean.Int32:
  match x:
    case U32{d}:
      Lean.Int32.mk{LexLeanRuntime.W.resize(32n, 32n, False{}, d)}

def Lean.Int32.ofNat(n: Nat) -> Lean.Int32:
  Lean.Int32.mk{LexLeanRuntime.Nat.toWord(32n, n)}

def Lean.Int32.toInt.fin(s: Bool, b: Word(32n)) -> L.Lean.Int:
  match s:
    case False{}:
      L.ofNat{Word.to_nat(32n, b)}
    case True{}:
      L.negSucc{Word.to_nat(32n, Word.not(32n, b))}

def Lean.Int32.toInt(x: Lean.Int32) -> L.Lean.Int:
  +b = Lean.Int32.bits(x)
  Lean.Int32.toInt.fin(LexLeanRuntime.W.msb(32n, b), b)

def Lean.Int32.toNatClampNeg.fin(s: Bool, b: Word(32n)) -> Nat:
  match s:
    case False{}:
      Word.to_nat(32n, b)
    case True{}:
      0n

def Lean.Int32.toNatClampNeg(x: Lean.Int32) -> Nat:
  +b = Lean.Int32.bits(x)
  Lean.Int32.toNatClampNeg.fin(LexLeanRuntime.W.msb(32n, b), b)

# BitVec.ofInt 32 i, that is i mod 2^32; for i = -(m + 1) that is the complement of m mod 2^32.
def Lean.Int32.ofInt(i: L.Lean.Int) -> Lean.Int32:
  match i:
    case L.ofNat{n}:
      Lean.Int32.mk{LexLeanRuntime.Nat.toWord(32n, n)}
    case L.negSucc{m}:
      Lean.Int32.mk{Word.not(32n, LexLeanRuntime.Nat.toWord(32n, m))}

def Lean.Int32.add(a: Lean.Int32, b: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{Word.add(32n, Lean.Int32.bits(a), Lean.Int32.bits(b))}

def Lean.Int32.sub(a: Lean.Int32, b: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{Word.sub(32n, Lean.Int32.bits(a), Lean.Int32.bits(b))}

def Lean.Int32.mul(a: Lean.Int32, b: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{Word.mul(32n, Lean.Int32.bits(a), Lean.Int32.bits(b))}

def Lean.Int32.neg(a: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{LexLeanRuntime.W.neg(32n, Lean.Int32.bits(a))}

# BitVec.sdiv and BitVec.srem: truncating; x / 0 = 0, x % 0 = x, min / -1 = min.
def Lean.Int32.div(a: Lean.Int32, b: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{LexLeanRuntime.W.sdiv(32n, Lean.Int32.bits(a), Lean.Int32.bits(b))}

def Lean.Int32.mod(a: Lean.Int32, b: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{LexLeanRuntime.W.srem(32n, Lean.Int32.bits(a), Lean.Int32.bits(b))}

def Lean.Int32.land(a: Lean.Int32, b: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{Word.and(32n, Lean.Int32.bits(a), Lean.Int32.bits(b))}

def Lean.Int32.lor(a: Lean.Int32, b: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{Word.or(32n, Lean.Int32.bits(a), Lean.Int32.bits(b))}

def Lean.Int32.xor(a: Lean.Int32, b: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{Word.xor(32n, Lean.Int32.bits(a), Lean.Int32.bits(b))}

def Lean.Int32.complement(a: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{Word.not(32n, Lean.Int32.bits(a))}

# The shift amount is b mod 32, the low 5 bits of b (smod by a power of two).
def Lean.Int32.shiftLeft(a: Lean.Int32, b: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{LexLeanRuntime.W.shlBy(LexLeanRuntime.W.lowNat(5n, 32n, Lean.Int32.bits(b)), 32n, Lean.Int32.bits(a))}

def Lean.Int32.shiftRight(a: Lean.Int32, b: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mk{LexLeanRuntime.W.ashrBy(LexLeanRuntime.W.lowNat(5n, 32n, Lean.Int32.bits(b)), 32n, Lean.Int32.bits(a))}

def Lean.Int32.beq(a: Lean.Int32, b: Lean.Int32) -> Bool:
  LexLeanRuntime.W.eq(32n, Lean.Int32.bits(a), Lean.Int32.bits(b))

def Lean.Int32.cmp(a: Lean.Int32, b: Lean.Int32) -> Cmp:
  LexLeanRuntime.W.scmp(32n, Lean.Int32.bits(a), Lean.Int32.bits(b))

def Lean.Int32.decLt(a: Lean.Int32, b: Lean.Int32) -> Bool:
  Cmp.is_lt(Lean.Int32.cmp(a, b))

def Lean.Int32.decLe(a: Lean.Int32, b: Lean.Int32) -> Bool:
  Cmp.is_le(Lean.Int32.cmp(a, b))

def Lean.Int32.lt(a: Lean.Int32, b: Lean.Int32) -> Type:
  {Lean.Int32.decLt(a, b) == True{} : Bool}

def Lean.Int32.le(a: Lean.Int32, b: Lean.Int32) -> Type:
  {Lean.Int32.decLe(a, b) == True{} : Bool}

def Lean.Int32.toUInt32(a: Lean.Int32) -> U32:
  U32{Lean.Int32.bits(a)}

# ---- Int64: exactly 2^64 values, the 64-bit word read in twos complement.
def Lean.Int64.bits(x: Lean.Int64) -> Word(64n):
  match x:
    case Lean.Int64.mk{b}:
      b

def Lean.Int64.ofBits(b: Word(64n)) -> Lean.Int64:
  Lean.Int64.mk{b}

# OfNat Int64 n for a literal n <= 4294967295: n mod 2^64.
def Lean.Int64.lit(x: U32) -> Lean.Int64:
  match x:
    case U32{d}:
      Lean.Int64.mk{LexLeanRuntime.W.resize(64n, 32n, False{}, d)}

# OfNat Int64 (hi * 2^32 + lo), for literals above 4294967295.
def Lean.Int64.lit2(hi: U32, lo: U32) -> Lean.Int64:
  match hi lo:
    case U32{h} U32{l}:
      Lean.Int64.mk{LexLeanRuntime.W.concat(32n, l, 32n, h)}

def Lean.Int64.ofNat(n: Nat) -> Lean.Int64:
  Lean.Int64.mk{LexLeanRuntime.Nat.toWord(64n, n)}

def Lean.Int64.toInt.fin(s: Bool, b: Word(64n)) -> L.Lean.Int:
  match s:
    case False{}:
      L.ofNat{Word.to_nat(64n, b)}
    case True{}:
      L.negSucc{Word.to_nat(64n, Word.not(64n, b))}

def Lean.Int64.toInt(x: Lean.Int64) -> L.Lean.Int:
  +b = Lean.Int64.bits(x)
  Lean.Int64.toInt.fin(LexLeanRuntime.W.msb(64n, b), b)

def Lean.Int64.toNatClampNeg.fin(s: Bool, b: Word(64n)) -> Nat:
  match s:
    case False{}:
      Word.to_nat(64n, b)
    case True{}:
      0n

def Lean.Int64.toNatClampNeg(x: Lean.Int64) -> Nat:
  +b = Lean.Int64.bits(x)
  Lean.Int64.toNatClampNeg.fin(LexLeanRuntime.W.msb(64n, b), b)

# BitVec.ofInt 64 i, that is i mod 2^64; for i = -(m + 1) that is the complement of m mod 2^64.
def Lean.Int64.ofInt(i: L.Lean.Int) -> Lean.Int64:
  match i:
    case L.ofNat{n}:
      Lean.Int64.mk{LexLeanRuntime.Nat.toWord(64n, n)}
    case L.negSucc{m}:
      Lean.Int64.mk{Word.not(64n, LexLeanRuntime.Nat.toWord(64n, m))}

def Lean.Int64.add(a: Lean.Int64, b: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{Word.add(64n, Lean.Int64.bits(a), Lean.Int64.bits(b))}

def Lean.Int64.sub(a: Lean.Int64, b: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{Word.sub(64n, Lean.Int64.bits(a), Lean.Int64.bits(b))}

def Lean.Int64.mul(a: Lean.Int64, b: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{Word.mul(64n, Lean.Int64.bits(a), Lean.Int64.bits(b))}

def Lean.Int64.neg(a: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{LexLeanRuntime.W.neg(64n, Lean.Int64.bits(a))}

# BitVec.sdiv and BitVec.srem: truncating; x / 0 = 0, x % 0 = x, min / -1 = min.
def Lean.Int64.div(a: Lean.Int64, b: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{LexLeanRuntime.W.sdiv(64n, Lean.Int64.bits(a), Lean.Int64.bits(b))}

def Lean.Int64.mod(a: Lean.Int64, b: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{LexLeanRuntime.W.srem(64n, Lean.Int64.bits(a), Lean.Int64.bits(b))}

def Lean.Int64.land(a: Lean.Int64, b: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{Word.and(64n, Lean.Int64.bits(a), Lean.Int64.bits(b))}

def Lean.Int64.lor(a: Lean.Int64, b: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{Word.or(64n, Lean.Int64.bits(a), Lean.Int64.bits(b))}

def Lean.Int64.xor(a: Lean.Int64, b: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{Word.xor(64n, Lean.Int64.bits(a), Lean.Int64.bits(b))}

def Lean.Int64.complement(a: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{Word.not(64n, Lean.Int64.bits(a))}

# The shift amount is b mod 64, the low 6 bits of b (smod by a power of two).
def Lean.Int64.shiftLeft(a: Lean.Int64, b: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{LexLeanRuntime.W.shlBy(LexLeanRuntime.W.lowNat(6n, 64n, Lean.Int64.bits(b)), 64n, Lean.Int64.bits(a))}

def Lean.Int64.shiftRight(a: Lean.Int64, b: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mk{LexLeanRuntime.W.ashrBy(LexLeanRuntime.W.lowNat(6n, 64n, Lean.Int64.bits(b)), 64n, Lean.Int64.bits(a))}

def Lean.Int64.beq(a: Lean.Int64, b: Lean.Int64) -> Bool:
  LexLeanRuntime.W.eq(64n, Lean.Int64.bits(a), Lean.Int64.bits(b))

def Lean.Int64.cmp(a: Lean.Int64, b: Lean.Int64) -> Cmp:
  LexLeanRuntime.W.scmp(64n, Lean.Int64.bits(a), Lean.Int64.bits(b))

def Lean.Int64.decLt(a: Lean.Int64, b: Lean.Int64) -> Bool:
  Cmp.is_lt(Lean.Int64.cmp(a, b))

def Lean.Int64.decLe(a: Lean.Int64, b: Lean.Int64) -> Bool:
  Cmp.is_le(Lean.Int64.cmp(a, b))

def Lean.Int64.lt(a: Lean.Int64, b: Lean.Int64) -> Type:
  {Lean.Int64.decLt(a, b) == True{} : Bool}

def Lean.Int64.le(a: Lean.Int64, b: Lean.Int64) -> Type:
  {Lean.Int64.decLe(a, b) == True{} : Bool}

def Lean.Int64.toUInt64(a: Lean.Int64) -> Lean.UInt64:
  Lean.UInt64.mk{Lean.Int64.bits(a)}

# ---------------------------------------------------------------------------
# LexLeanRuntime: generic helpers.
# ---------------------------------------------------------------------------

# Lean `if bad then none else some x`.
def LexLeanRuntime.Maybe.unless(-A: Data, bad: Bool, x: A) -> Maybe<&2, A>:
  match bad:
    case True{}:
      None{}
    case False{}:
      Some{x}

def Lean.Bool.beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}
    case False{} False{}:
      True{}

# `a != b` on Bool: bne a b = !(a == b).
def Lean.Bool.bne(a: Bool, b: Bool) -> Bool:
  L.Lean.Bool.not(Lean.Bool.beq(a, b))

def Lean.Char.beq(a: Char, b: Char) -> Bool:
  U32.is_eq(Char.to_u32(a), Char.to_u32(b))

def Lean.String.beq(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{bh, bt}:
      False{}
    case SCon{ah, at} SNil{}:
      False{}
    case SCon{ah, at} SCon{bh, bt}:
      L.Lean.Bool.and(Lean.Char.beq(ah, bh), Lean.String.beq(at, bt))

def Lean.String.isEmpty(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, t}:
      False{}

def Lean.String.length(s: String) -> Nat:
  String.length(s)

def Lean.String.isPrefixOf(p: String, s: String) -> Bool:
  match p s:
    case SNil{} _:
      True{}
    case SCon{ph, pt} SNil{}:
      False{}
    case SCon{ph, pt} SCon{sh, st}:
      L.Lean.Bool.and(Lean.Char.beq(ph, sh), Lean.String.isPrefixOf(pt, st))

def Lean.List.drop(-A: Data, n: Nat, xs: List<&2, A>) -> List<&2, A>:
  match n xs:
    case 0n _:
      xs
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      Lean.List.drop(A, p, t)

def Lean.List.take(-A: Data, n: Nat, xs: List<&2, A>) -> List<&2, A>:
  match n xs:
    case 0n _:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      Con{h, Lean.List.take(A, p, t)}

# m.toNat < n for a UInt32 m, walking n down so no Nat of 2^32 is built.
def LexLeanRuntime.U32.toNatLt(n: Nat, +m: U32) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      Bool.pick(Bool, U32.is_zero(m), True{}, LexLeanRuntime.U32.toNatLt(p, U32.sub(m, 1)))

# ---------------------------------------------------------------------------
# ByteArray: a one-field wrapper of the byte list (Lean: a wrapper of Array UInt8).
# ---------------------------------------------------------------------------

type Lean.ByteArray is Data:
  Lean.ByteArray.mk{data: List<&2, Lean.UInt8>}

def Lean.ByteArray.data(b: Lean.ByteArray) -> List<&2, Lean.UInt8>:
  match b:
    case Lean.ByteArray.mk{d}:
      d

def Lean.ByteArray.size(b: Lean.ByteArray) -> Nat:
  L.Lean.List.length(Lean.UInt8, Lean.ByteArray.data(b))

def Lean.ByteArray.append(a: Lean.ByteArray, b: Lean.ByteArray) -> Lean.ByteArray:
  Lean.ByteArray.mk{L.Lean.List.append(Lean.UInt8, Lean.ByteArray.data(a), Lean.ByteArray.data(b))}

# ByteArray.extract a b e = a.copySlice b empty 0 (e - b): the bytes in [b, e).
def Lean.ByteArray.extract(a: Lean.ByteArray, +b: Nat, e: Nat) -> Lean.ByteArray:
  Lean.ByteArray.mk{Lean.List.take(Lean.UInt8, L.Lean.Nat.sub(e, b), Lean.List.drop(Lean.UInt8, b, Lean.ByteArray.data(a)))}

def Lean.ByteArray.beq.go(a: List<&2, Lean.UInt8>, b: List<&2, Lean.UInt8>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{bh, bt}:
      False{}
    case Con{ah, at} Nil{}:
      False{}
    case Con{ah, at} Con{bh, bt}:
      L.Lean.Bool.and(Lean.UInt8.beq(ah, bh), Lean.ByteArray.beq.go(at, bt))

def Lean.ByteArray.beq(a: Lean.ByteArray, b: Lean.ByteArray) -> Bool:
  Lean.ByteArray.beq.go(Lean.ByteArray.data(a), Lean.ByteArray.data(b))

def Lean.UInt8.toUInt32(x: Lean.UInt8) -> U32:
  U32{LexLeanRuntime.W.resize(32n, 8n, False{}, Lean.UInt8.bits(x))}

# ---------------------------------------------------------------------------
# ToMathInt and Fixed instances, and the checked operations.
# A checked operation widens both operands to W = 2w + 2 bits, where the
# exact mathematical result always fits, computes there, and narrows: the
# result is the exact value when it lies in [minimum, maximum] and none
# otherwise, as Lean's checkedFromInt of the exact Int result is.
# ---------------------------------------------------------------------------

def LexLeanRuntime.ToMathInt.toInt.Int(value: L.Lean.Int) -> L.Lean.Int:
  value

def LexLeanRuntime.ToMathInt.toInt.UInt8(value: Lean.UInt8) -> L.Lean.Int:
  L.ofNat{Lean.UInt8.toNat(value)}

def LexLeanRuntime.Fixed.fromInt.UInt8(value: L.Lean.Int) -> Lean.UInt8:
  Lean.UInt8.ofInt(value)

def LexLeanRuntime.Fixed.minimum.UInt8() -> L.Lean.Int:
  L.ofNat{0n}

def LexLeanRuntime.Fixed.maximum.UInt8() -> L.Lean.Int:
  L.ofNat{255n}

def LexLeanRuntime.Fixed.bitAnd.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.land(left, right)

def LexLeanRuntime.Fixed.bitOr.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.lor(left, right)

def LexLeanRuntime.Fixed.bitXor.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.xor(left, right)

def LexLeanRuntime.Fixed.bitNot.UInt8(value: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.complement(value)

# if amount.toNat < 8 then some (UInt8.shiftLeft value (UInt8.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftLeft.UInt8(value: Lean.UInt8, +amount: U32) -> Maybe<&2, Lean.UInt8>:
  Bool.pick(Maybe<&2, Lean.UInt8>, U32.is_lt(amount, 8), Some{Lean.UInt8.shiftLeft(value, Lean.UInt8.ofNat(U32.to_nat(amount)))}, None{})

# if amount.toNat < 8 then some (UInt8.shiftRight value (UInt8.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftRight.UInt8(value: Lean.UInt8, +amount: U32) -> Maybe<&2, Lean.UInt8>:
  Bool.pick(Maybe<&2, Lean.UInt8>, U32.is_lt(amount, 8), Some{Lean.UInt8.shiftRight(value, Lean.UInt8.ofNat(U32.to_nat(amount)))}, None{})

def LexLeanRuntime.Fixed.wide.UInt8(x: Lean.UInt8) -> Word(18n):
  b = Lean.UInt8.bits(x)
  LexLeanRuntime.W.resize(18n, 8n, False{}, b)

def LexLeanRuntime.Fixed.wide66.UInt8(x: Lean.UInt8) -> Word(66n):
  b = Lean.UInt8.bits(x)
  LexLeanRuntime.W.resize(66n, 8n, False{}, b)

# Some of the low 8 bits when the n-bit two's complement value lies in the UInt8 range.
def LexLeanRuntime.Fixed.narrow.UInt8(+n: Nat, +v: Word(n)) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Maybe.unless(Lean.UInt8, Bool.not(LexLeanRuntime.W.highSame(8n, n, False{}, v)), Lean.UInt8.mk{LexLeanRuntime.W.resize(8n, n, False{}, v)})

# if value < minimum then none else if maximum < value then none else some (fromInt value)
def LexLeanRuntime.checkedFromInt.UInt8(value: L.Lean.Int) -> Maybe<&2, Lean.UInt8>:
  match value:
    case L.ofNat{+n}:
      LexLeanRuntime.Maybe.unless(Lean.UInt8, Bool.not(LexLeanRuntime.Nat.ltPow2(8n, n)), Lean.UInt8.ofNat(n))
    case L.negSucc{m}:
      None{}

def LexLeanRuntime.checkedAdd.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(18n, Word.add(18n, LexLeanRuntime.Fixed.wide.UInt8(left), LexLeanRuntime.Fixed.wide.UInt8(right)))

def LexLeanRuntime.checkedSubtract.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(18n, Word.sub(18n, LexLeanRuntime.Fixed.wide.UInt8(left), LexLeanRuntime.Fixed.wide.UInt8(right)))

def LexLeanRuntime.checkedMultiply.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(18n, Word.mul(18n, LexLeanRuntime.Fixed.wide.UInt8(left), LexLeanRuntime.Fixed.wide.UInt8(right)))

def LexLeanRuntime.checkedNegate.UInt8(value: Lean.UInt8) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(18n, LexLeanRuntime.W.neg(18n, LexLeanRuntime.Fixed.wide.UInt8(value)))

def LexLeanRuntime.checkedQuotient.fin.UInt8(z: Bool, left: Lean.UInt8, right: Lean.UInt8) -> Maybe<&2, Lean.UInt8>:
  match z:
    case True{}:
      None{}
    case False{}:
      LexLeanRuntime.Fixed.narrow.UInt8(18n, LexLeanRuntime.W.sdiv(18n, LexLeanRuntime.Fixed.wide.UInt8(left), LexLeanRuntime.Fixed.wide.UInt8(right)))

# if toInt right = 0 then none else checkedFromInt (Int.tdiv (toInt left) (toInt right))
def LexLeanRuntime.checkedQuotient.UInt8(left: Lean.UInt8, +right: Lean.UInt8) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.checkedQuotient.fin.UInt8(LexLeanRuntime.W.isZero(8n, Lean.UInt8.bits(right)), left, right)

def LexLeanRuntime.ToMathInt.toInt.UInt16(value: Lean.UInt16) -> L.Lean.Int:
  L.ofNat{Lean.UInt16.toNat(value)}

def LexLeanRuntime.Fixed.fromInt.UInt16(value: L.Lean.Int) -> Lean.UInt16:
  Lean.UInt16.ofInt(value)

def LexLeanRuntime.Fixed.minimum.UInt16() -> L.Lean.Int:
  L.ofNat{0n}

def LexLeanRuntime.Fixed.maximum.UInt16() -> L.Lean.Int:
  L.ofNat{65535n}

def LexLeanRuntime.Fixed.bitAnd.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.land(left, right)

def LexLeanRuntime.Fixed.bitOr.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.lor(left, right)

def LexLeanRuntime.Fixed.bitXor.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.xor(left, right)

def LexLeanRuntime.Fixed.bitNot.UInt16(value: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.complement(value)

# if amount.toNat < 16 then some (UInt16.shiftLeft value (UInt16.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftLeft.UInt16(value: Lean.UInt16, +amount: U32) -> Maybe<&2, Lean.UInt16>:
  Bool.pick(Maybe<&2, Lean.UInt16>, U32.is_lt(amount, 16), Some{Lean.UInt16.shiftLeft(value, Lean.UInt16.ofNat(U32.to_nat(amount)))}, None{})

# if amount.toNat < 16 then some (UInt16.shiftRight value (UInt16.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftRight.UInt16(value: Lean.UInt16, +amount: U32) -> Maybe<&2, Lean.UInt16>:
  Bool.pick(Maybe<&2, Lean.UInt16>, U32.is_lt(amount, 16), Some{Lean.UInt16.shiftRight(value, Lean.UInt16.ofNat(U32.to_nat(amount)))}, None{})

def LexLeanRuntime.Fixed.wide.UInt16(x: Lean.UInt16) -> Word(34n):
  b = Lean.UInt16.bits(x)
  LexLeanRuntime.W.resize(34n, 16n, False{}, b)

def LexLeanRuntime.Fixed.wide66.UInt16(x: Lean.UInt16) -> Word(66n):
  b = Lean.UInt16.bits(x)
  LexLeanRuntime.W.resize(66n, 16n, False{}, b)

# Some of the low 16 bits when the n-bit two's complement value lies in the UInt16 range.
def LexLeanRuntime.Fixed.narrow.UInt16(+n: Nat, +v: Word(n)) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Maybe.unless(Lean.UInt16, Bool.not(LexLeanRuntime.W.highSame(16n, n, False{}, v)), Lean.UInt16.mk{LexLeanRuntime.W.resize(16n, n, False{}, v)})

# if value < minimum then none else if maximum < value then none else some (fromInt value)
def LexLeanRuntime.checkedFromInt.UInt16(value: L.Lean.Int) -> Maybe<&2, Lean.UInt16>:
  match value:
    case L.ofNat{+n}:
      LexLeanRuntime.Maybe.unless(Lean.UInt16, Bool.not(LexLeanRuntime.Nat.ltPow2(16n, n)), Lean.UInt16.ofNat(n))
    case L.negSucc{m}:
      None{}

def LexLeanRuntime.checkedAdd.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(34n, Word.add(34n, LexLeanRuntime.Fixed.wide.UInt16(left), LexLeanRuntime.Fixed.wide.UInt16(right)))

def LexLeanRuntime.checkedSubtract.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(34n, Word.sub(34n, LexLeanRuntime.Fixed.wide.UInt16(left), LexLeanRuntime.Fixed.wide.UInt16(right)))

def LexLeanRuntime.checkedMultiply.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(34n, Word.mul(34n, LexLeanRuntime.Fixed.wide.UInt16(left), LexLeanRuntime.Fixed.wide.UInt16(right)))

def LexLeanRuntime.checkedNegate.UInt16(value: Lean.UInt16) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(34n, LexLeanRuntime.W.neg(34n, LexLeanRuntime.Fixed.wide.UInt16(value)))

def LexLeanRuntime.checkedQuotient.fin.UInt16(z: Bool, left: Lean.UInt16, right: Lean.UInt16) -> Maybe<&2, Lean.UInt16>:
  match z:
    case True{}:
      None{}
    case False{}:
      LexLeanRuntime.Fixed.narrow.UInt16(34n, LexLeanRuntime.W.sdiv(34n, LexLeanRuntime.Fixed.wide.UInt16(left), LexLeanRuntime.Fixed.wide.UInt16(right)))

# if toInt right = 0 then none else checkedFromInt (Int.tdiv (toInt left) (toInt right))
def LexLeanRuntime.checkedQuotient.UInt16(left: Lean.UInt16, +right: Lean.UInt16) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.checkedQuotient.fin.UInt16(LexLeanRuntime.W.isZero(16n, Lean.UInt16.bits(right)), left, right)

def LexLeanRuntime.ToMathInt.toInt.UInt32(value: U32) -> L.Lean.Int:
  L.ofNat{Lean.UInt32.toNat(value)}

def LexLeanRuntime.Fixed.fromInt.UInt32(value: L.Lean.Int) -> U32:
  Lean.UInt32.ofInt(value)

def LexLeanRuntime.Fixed.minimum.UInt32() -> L.Lean.Int:
  L.ofNat{0n}

def LexLeanRuntime.Fixed.maximum.UInt32() -> L.Lean.Int:
  L.ofNat{4294967295n}

def LexLeanRuntime.Fixed.bitAnd.UInt32(left: U32, right: U32) -> U32:
  Lean.UInt32.land(left, right)

def LexLeanRuntime.Fixed.bitOr.UInt32(left: U32, right: U32) -> U32:
  Lean.UInt32.lor(left, right)

def LexLeanRuntime.Fixed.bitXor.UInt32(left: U32, right: U32) -> U32:
  Lean.UInt32.xor(left, right)

def LexLeanRuntime.Fixed.bitNot.UInt32(value: U32) -> U32:
  Lean.UInt32.complement(value)

# if amount.toNat < 32 then some (UInt32.shiftLeft value (amount)) else none
def LexLeanRuntime.Fixed.shiftLeft.UInt32(value: U32, +amount: U32) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, U32.is_lt(amount, 32), Some{Lean.UInt32.shiftLeft(value, amount)}, None{})

# if amount.toNat < 32 then some (UInt32.shiftRight value (amount)) else none
def LexLeanRuntime.Fixed.shiftRight.UInt32(value: U32, +amount: U32) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, U32.is_lt(amount, 32), Some{Lean.UInt32.shiftRight(value, amount)}, None{})

def LexLeanRuntime.Fixed.wide.UInt32(x: U32) -> Word(66n):
  b = Lean.UInt32.bits(x)
  LexLeanRuntime.W.resize(66n, 32n, False{}, b)

def LexLeanRuntime.Fixed.wide66.UInt32(x: U32) -> Word(66n):
  b = Lean.UInt32.bits(x)
  LexLeanRuntime.W.resize(66n, 32n, False{}, b)

# Some of the low 32 bits when the n-bit two's complement value lies in the UInt32 range.
def LexLeanRuntime.Fixed.narrow.UInt32(+n: Nat, +v: Word(n)) -> Maybe<&2, U32>:
  LexLeanRuntime.Maybe.unless(U32, Bool.not(LexLeanRuntime.W.highSame(32n, n, False{}, v)), U32{LexLeanRuntime.W.resize(32n, n, False{}, v)})

# if value < minimum then none else if maximum < value then none else some (fromInt value)
def LexLeanRuntime.checkedFromInt.UInt32(value: L.Lean.Int) -> Maybe<&2, U32>:
  match value:
    case L.ofNat{+n}:
      LexLeanRuntime.Maybe.unless(U32, Bool.not(LexLeanRuntime.Nat.ltPow2(32n, n)), Lean.UInt32.ofNat(n))
    case L.negSucc{m}:
      None{}

def LexLeanRuntime.checkedAdd.UInt32(left: U32, right: U32) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, Word.add(66n, LexLeanRuntime.Fixed.wide.UInt32(left), LexLeanRuntime.Fixed.wide.UInt32(right)))

def LexLeanRuntime.checkedSubtract.UInt32(left: U32, right: U32) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, Word.sub(66n, LexLeanRuntime.Fixed.wide.UInt32(left), LexLeanRuntime.Fixed.wide.UInt32(right)))

def LexLeanRuntime.checkedMultiply.UInt32(left: U32, right: U32) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, Word.mul(66n, LexLeanRuntime.Fixed.wide.UInt32(left), LexLeanRuntime.Fixed.wide.UInt32(right)))

def LexLeanRuntime.checkedNegate.UInt32(value: U32) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, LexLeanRuntime.W.neg(66n, LexLeanRuntime.Fixed.wide.UInt32(value)))

def LexLeanRuntime.checkedQuotient.fin.UInt32(z: Bool, left: U32, right: U32) -> Maybe<&2, U32>:
  match z:
    case True{}:
      None{}
    case False{}:
      LexLeanRuntime.Fixed.narrow.UInt32(66n, LexLeanRuntime.W.sdiv(66n, LexLeanRuntime.Fixed.wide.UInt32(left), LexLeanRuntime.Fixed.wide.UInt32(right)))

# if toInt right = 0 then none else checkedFromInt (Int.tdiv (toInt left) (toInt right))
def LexLeanRuntime.checkedQuotient.UInt32(left: U32, +right: U32) -> Maybe<&2, U32>:
  LexLeanRuntime.checkedQuotient.fin.UInt32(LexLeanRuntime.W.isZero(32n, Lean.UInt32.bits(right)), left, right)

def LexLeanRuntime.ToMathInt.toInt.UInt64(value: Lean.UInt64) -> L.Lean.Int:
  L.ofNat{Lean.UInt64.toNat(value)}

def LexLeanRuntime.Fixed.fromInt.UInt64(value: L.Lean.Int) -> Lean.UInt64:
  Lean.UInt64.ofInt(value)

def LexLeanRuntime.Fixed.minimum.UInt64() -> L.Lean.Int:
  L.ofNat{0n}

def LexLeanRuntime.Fixed.maximum.UInt64() -> L.Lean.Int:
  L.ofNat{Word.to_nat(64n, Word.not(64n, Word.zero(64n)))}

def LexLeanRuntime.Fixed.bitAnd.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.land(left, right)

def LexLeanRuntime.Fixed.bitOr.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.lor(left, right)

def LexLeanRuntime.Fixed.bitXor.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.xor(left, right)

def LexLeanRuntime.Fixed.bitNot.UInt64(value: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.complement(value)

# if amount.toNat < 64 then some (UInt64.shiftLeft value (UInt64.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftLeft.UInt64(value: Lean.UInt64, +amount: U32) -> Maybe<&2, Lean.UInt64>:
  Bool.pick(Maybe<&2, Lean.UInt64>, U32.is_lt(amount, 64), Some{Lean.UInt64.shiftLeft(value, Lean.UInt64.ofNat(U32.to_nat(amount)))}, None{})

# if amount.toNat < 64 then some (UInt64.shiftRight value (UInt64.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftRight.UInt64(value: Lean.UInt64, +amount: U32) -> Maybe<&2, Lean.UInt64>:
  Bool.pick(Maybe<&2, Lean.UInt64>, U32.is_lt(amount, 64), Some{Lean.UInt64.shiftRight(value, Lean.UInt64.ofNat(U32.to_nat(amount)))}, None{})

def LexLeanRuntime.Fixed.wide.UInt64(x: Lean.UInt64) -> Word(130n):
  b = Lean.UInt64.bits(x)
  LexLeanRuntime.W.resize(130n, 64n, False{}, b)

def LexLeanRuntime.Fixed.wide66.UInt64(x: Lean.UInt64) -> Word(66n):
  b = Lean.UInt64.bits(x)
  LexLeanRuntime.W.resize(66n, 64n, False{}, b)

# Some of the low 64 bits when the n-bit two's complement value lies in the UInt64 range.
def LexLeanRuntime.Fixed.narrow.UInt64(+n: Nat, +v: Word(n)) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Maybe.unless(Lean.UInt64, Bool.not(LexLeanRuntime.W.highSame(64n, n, False{}, v)), Lean.UInt64.mk{LexLeanRuntime.W.resize(64n, n, False{}, v)})

# if value < minimum then none else if maximum < value then none else some (fromInt value)
def LexLeanRuntime.checkedFromInt.UInt64(value: L.Lean.Int) -> Maybe<&2, Lean.UInt64>:
  match value:
    case L.ofNat{+n}:
      LexLeanRuntime.Maybe.unless(Lean.UInt64, Bool.not(LexLeanRuntime.Nat.ltPow2(64n, n)), Lean.UInt64.ofNat(n))
    case L.negSucc{m}:
      None{}

def LexLeanRuntime.checkedAdd.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(130n, Word.add(130n, LexLeanRuntime.Fixed.wide.UInt64(left), LexLeanRuntime.Fixed.wide.UInt64(right)))

def LexLeanRuntime.checkedSubtract.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(130n, Word.sub(130n, LexLeanRuntime.Fixed.wide.UInt64(left), LexLeanRuntime.Fixed.wide.UInt64(right)))

def LexLeanRuntime.checkedMultiply.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(130n, Word.mul(130n, LexLeanRuntime.Fixed.wide.UInt64(left), LexLeanRuntime.Fixed.wide.UInt64(right)))

def LexLeanRuntime.checkedNegate.UInt64(value: Lean.UInt64) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(130n, LexLeanRuntime.W.neg(130n, LexLeanRuntime.Fixed.wide.UInt64(value)))

def LexLeanRuntime.checkedQuotient.fin.UInt64(z: Bool, left: Lean.UInt64, right: Lean.UInt64) -> Maybe<&2, Lean.UInt64>:
  match z:
    case True{}:
      None{}
    case False{}:
      LexLeanRuntime.Fixed.narrow.UInt64(130n, LexLeanRuntime.W.sdiv(130n, LexLeanRuntime.Fixed.wide.UInt64(left), LexLeanRuntime.Fixed.wide.UInt64(right)))

# if toInt right = 0 then none else checkedFromInt (Int.tdiv (toInt left) (toInt right))
def LexLeanRuntime.checkedQuotient.UInt64(left: Lean.UInt64, +right: Lean.UInt64) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.checkedQuotient.fin.UInt64(LexLeanRuntime.W.isZero(64n, Lean.UInt64.bits(right)), left, right)

def LexLeanRuntime.ToMathInt.toInt.Int8(value: Lean.Int8) -> L.Lean.Int:
  Lean.Int8.toInt(value)

def LexLeanRuntime.Fixed.fromInt.Int8(value: L.Lean.Int) -> Lean.Int8:
  Lean.Int8.ofInt(value)

def LexLeanRuntime.Fixed.minimum.Int8() -> L.Lean.Int:
  L.negSucc{127n}

def LexLeanRuntime.Fixed.maximum.Int8() -> L.Lean.Int:
  L.ofNat{127n}

def LexLeanRuntime.Fixed.bitAnd.Int8(left: Lean.Int8, right: Lean.Int8) -> Lean.Int8:
  Lean.Int8.land(left, right)

def LexLeanRuntime.Fixed.bitOr.Int8(left: Lean.Int8, right: Lean.Int8) -> Lean.Int8:
  Lean.Int8.lor(left, right)

def LexLeanRuntime.Fixed.bitXor.Int8(left: Lean.Int8, right: Lean.Int8) -> Lean.Int8:
  Lean.Int8.xor(left, right)

def LexLeanRuntime.Fixed.bitNot.Int8(value: Lean.Int8) -> Lean.Int8:
  Lean.Int8.complement(value)

# if amount.toNat < 8 then some (Int8.shiftLeft value (Int8.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftLeft.Int8(value: Lean.Int8, +amount: U32) -> Maybe<&2, Lean.Int8>:
  Bool.pick(Maybe<&2, Lean.Int8>, U32.is_lt(amount, 8), Some{Lean.Int8.shiftLeft(value, Lean.Int8.ofNat(U32.to_nat(amount)))}, None{})

# if amount.toNat < 8 then some (Int8.shiftRight value (Int8.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftRight.Int8(value: Lean.Int8, +amount: U32) -> Maybe<&2, Lean.Int8>:
  Bool.pick(Maybe<&2, Lean.Int8>, U32.is_lt(amount, 8), Some{Lean.Int8.shiftRight(value, Lean.Int8.ofNat(U32.to_nat(amount)))}, None{})

def LexLeanRuntime.Fixed.wide.Int8(x: Lean.Int8) -> Word(18n):
  +b = Lean.Int8.bits(x)
  LexLeanRuntime.W.resize(18n, 8n, LexLeanRuntime.W.msb(8n, b), b)

def LexLeanRuntime.Fixed.wide66.Int8(x: Lean.Int8) -> Word(66n):
  +b = Lean.Int8.bits(x)
  LexLeanRuntime.W.resize(66n, 8n, LexLeanRuntime.W.msb(8n, b), b)

# Some of the low 8 bits when the n-bit two's complement value lies in the Int8 range.
def LexLeanRuntime.Fixed.narrow.Int8(+n: Nat, +v: Word(n)) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Maybe.unless(Lean.Int8, Bool.not(LexLeanRuntime.W.highSame(7n, n, LexLeanRuntime.W.msb(n, v), v)), Lean.Int8.mk{LexLeanRuntime.W.resize(8n, n, False{}, v)})

# if value < minimum then none else if maximum < value then none else some (fromInt value)
def LexLeanRuntime.checkedFromInt.Int8(value: L.Lean.Int) -> Maybe<&2, Lean.Int8>:
  match value:
    case L.ofNat{+n}:
      LexLeanRuntime.Maybe.unless(Lean.Int8, Bool.not(LexLeanRuntime.Nat.ltPow2(7n, n)), Lean.Int8.ofNat(n))
    case L.negSucc{+m}:
      LexLeanRuntime.Maybe.unless(Lean.Int8, Bool.not(LexLeanRuntime.Nat.ltPow2(7n, m)), Lean.Int8.mk{Word.not(8n, LexLeanRuntime.Nat.toWord(8n, m))})

def LexLeanRuntime.checkedAdd.Int8(left: Lean.Int8, right: Lean.Int8) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(18n, Word.add(18n, LexLeanRuntime.Fixed.wide.Int8(left), LexLeanRuntime.Fixed.wide.Int8(right)))

def LexLeanRuntime.checkedSubtract.Int8(left: Lean.Int8, right: Lean.Int8) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(18n, Word.sub(18n, LexLeanRuntime.Fixed.wide.Int8(left), LexLeanRuntime.Fixed.wide.Int8(right)))

def LexLeanRuntime.checkedMultiply.Int8(left: Lean.Int8, right: Lean.Int8) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(18n, Word.mul(18n, LexLeanRuntime.Fixed.wide.Int8(left), LexLeanRuntime.Fixed.wide.Int8(right)))

def LexLeanRuntime.checkedNegate.Int8(value: Lean.Int8) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(18n, LexLeanRuntime.W.neg(18n, LexLeanRuntime.Fixed.wide.Int8(value)))

def LexLeanRuntime.checkedQuotient.fin.Int8(z: Bool, left: Lean.Int8, right: Lean.Int8) -> Maybe<&2, Lean.Int8>:
  match z:
    case True{}:
      None{}
    case False{}:
      LexLeanRuntime.Fixed.narrow.Int8(18n, LexLeanRuntime.W.sdiv(18n, LexLeanRuntime.Fixed.wide.Int8(left), LexLeanRuntime.Fixed.wide.Int8(right)))

# if toInt right = 0 then none else checkedFromInt (Int.tdiv (toInt left) (toInt right))
def LexLeanRuntime.checkedQuotient.Int8(left: Lean.Int8, +right: Lean.Int8) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.checkedQuotient.fin.Int8(LexLeanRuntime.W.isZero(8n, Lean.Int8.bits(right)), left, right)

def LexLeanRuntime.ToMathInt.toInt.Int16(value: Lean.Int16) -> L.Lean.Int:
  Lean.Int16.toInt(value)

def LexLeanRuntime.Fixed.fromInt.Int16(value: L.Lean.Int) -> Lean.Int16:
  Lean.Int16.ofInt(value)

def LexLeanRuntime.Fixed.minimum.Int16() -> L.Lean.Int:
  L.negSucc{32767n}

def LexLeanRuntime.Fixed.maximum.Int16() -> L.Lean.Int:
  L.ofNat{32767n}

def LexLeanRuntime.Fixed.bitAnd.Int16(left: Lean.Int16, right: Lean.Int16) -> Lean.Int16:
  Lean.Int16.land(left, right)

def LexLeanRuntime.Fixed.bitOr.Int16(left: Lean.Int16, right: Lean.Int16) -> Lean.Int16:
  Lean.Int16.lor(left, right)

def LexLeanRuntime.Fixed.bitXor.Int16(left: Lean.Int16, right: Lean.Int16) -> Lean.Int16:
  Lean.Int16.xor(left, right)

def LexLeanRuntime.Fixed.bitNot.Int16(value: Lean.Int16) -> Lean.Int16:
  Lean.Int16.complement(value)

# if amount.toNat < 16 then some (Int16.shiftLeft value (Int16.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftLeft.Int16(value: Lean.Int16, +amount: U32) -> Maybe<&2, Lean.Int16>:
  Bool.pick(Maybe<&2, Lean.Int16>, U32.is_lt(amount, 16), Some{Lean.Int16.shiftLeft(value, Lean.Int16.ofNat(U32.to_nat(amount)))}, None{})

# if amount.toNat < 16 then some (Int16.shiftRight value (Int16.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftRight.Int16(value: Lean.Int16, +amount: U32) -> Maybe<&2, Lean.Int16>:
  Bool.pick(Maybe<&2, Lean.Int16>, U32.is_lt(amount, 16), Some{Lean.Int16.shiftRight(value, Lean.Int16.ofNat(U32.to_nat(amount)))}, None{})

def LexLeanRuntime.Fixed.wide.Int16(x: Lean.Int16) -> Word(34n):
  +b = Lean.Int16.bits(x)
  LexLeanRuntime.W.resize(34n, 16n, LexLeanRuntime.W.msb(16n, b), b)

def LexLeanRuntime.Fixed.wide66.Int16(x: Lean.Int16) -> Word(66n):
  +b = Lean.Int16.bits(x)
  LexLeanRuntime.W.resize(66n, 16n, LexLeanRuntime.W.msb(16n, b), b)

# Some of the low 16 bits when the n-bit two's complement value lies in the Int16 range.
def LexLeanRuntime.Fixed.narrow.Int16(+n: Nat, +v: Word(n)) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Maybe.unless(Lean.Int16, Bool.not(LexLeanRuntime.W.highSame(15n, n, LexLeanRuntime.W.msb(n, v), v)), Lean.Int16.mk{LexLeanRuntime.W.resize(16n, n, False{}, v)})

# if value < minimum then none else if maximum < value then none else some (fromInt value)
def LexLeanRuntime.checkedFromInt.Int16(value: L.Lean.Int) -> Maybe<&2, Lean.Int16>:
  match value:
    case L.ofNat{+n}:
      LexLeanRuntime.Maybe.unless(Lean.Int16, Bool.not(LexLeanRuntime.Nat.ltPow2(15n, n)), Lean.Int16.ofNat(n))
    case L.negSucc{+m}:
      LexLeanRuntime.Maybe.unless(Lean.Int16, Bool.not(LexLeanRuntime.Nat.ltPow2(15n, m)), Lean.Int16.mk{Word.not(16n, LexLeanRuntime.Nat.toWord(16n, m))})

def LexLeanRuntime.checkedAdd.Int16(left: Lean.Int16, right: Lean.Int16) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(34n, Word.add(34n, LexLeanRuntime.Fixed.wide.Int16(left), LexLeanRuntime.Fixed.wide.Int16(right)))

def LexLeanRuntime.checkedSubtract.Int16(left: Lean.Int16, right: Lean.Int16) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(34n, Word.sub(34n, LexLeanRuntime.Fixed.wide.Int16(left), LexLeanRuntime.Fixed.wide.Int16(right)))

def LexLeanRuntime.checkedMultiply.Int16(left: Lean.Int16, right: Lean.Int16) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(34n, Word.mul(34n, LexLeanRuntime.Fixed.wide.Int16(left), LexLeanRuntime.Fixed.wide.Int16(right)))

def LexLeanRuntime.checkedNegate.Int16(value: Lean.Int16) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(34n, LexLeanRuntime.W.neg(34n, LexLeanRuntime.Fixed.wide.Int16(value)))

def LexLeanRuntime.checkedQuotient.fin.Int16(z: Bool, left: Lean.Int16, right: Lean.Int16) -> Maybe<&2, Lean.Int16>:
  match z:
    case True{}:
      None{}
    case False{}:
      LexLeanRuntime.Fixed.narrow.Int16(34n, LexLeanRuntime.W.sdiv(34n, LexLeanRuntime.Fixed.wide.Int16(left), LexLeanRuntime.Fixed.wide.Int16(right)))

# if toInt right = 0 then none else checkedFromInt (Int.tdiv (toInt left) (toInt right))
def LexLeanRuntime.checkedQuotient.Int16(left: Lean.Int16, +right: Lean.Int16) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.checkedQuotient.fin.Int16(LexLeanRuntime.W.isZero(16n, Lean.Int16.bits(right)), left, right)

def LexLeanRuntime.ToMathInt.toInt.Int32(value: Lean.Int32) -> L.Lean.Int:
  Lean.Int32.toInt(value)

def LexLeanRuntime.Fixed.fromInt.Int32(value: L.Lean.Int) -> Lean.Int32:
  Lean.Int32.ofInt(value)

def LexLeanRuntime.Fixed.minimum.Int32() -> L.Lean.Int:
  L.negSucc{2147483647n}

def LexLeanRuntime.Fixed.maximum.Int32() -> L.Lean.Int:
  L.ofNat{2147483647n}

def LexLeanRuntime.Fixed.bitAnd.Int32(left: Lean.Int32, right: Lean.Int32) -> Lean.Int32:
  Lean.Int32.land(left, right)

def LexLeanRuntime.Fixed.bitOr.Int32(left: Lean.Int32, right: Lean.Int32) -> Lean.Int32:
  Lean.Int32.lor(left, right)

def LexLeanRuntime.Fixed.bitXor.Int32(left: Lean.Int32, right: Lean.Int32) -> Lean.Int32:
  Lean.Int32.xor(left, right)

def LexLeanRuntime.Fixed.bitNot.Int32(value: Lean.Int32) -> Lean.Int32:
  Lean.Int32.complement(value)

# if amount.toNat < 32 then some (Int32.shiftLeft value (Int32.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftLeft.Int32(value: Lean.Int32, +amount: U32) -> Maybe<&2, Lean.Int32>:
  Bool.pick(Maybe<&2, Lean.Int32>, U32.is_lt(amount, 32), Some{Lean.Int32.shiftLeft(value, Lean.Int32.ofNat(U32.to_nat(amount)))}, None{})

# if amount.toNat < 32 then some (Int32.shiftRight value (Int32.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftRight.Int32(value: Lean.Int32, +amount: U32) -> Maybe<&2, Lean.Int32>:
  Bool.pick(Maybe<&2, Lean.Int32>, U32.is_lt(amount, 32), Some{Lean.Int32.shiftRight(value, Lean.Int32.ofNat(U32.to_nat(amount)))}, None{})

def LexLeanRuntime.Fixed.wide.Int32(x: Lean.Int32) -> Word(66n):
  +b = Lean.Int32.bits(x)
  LexLeanRuntime.W.resize(66n, 32n, LexLeanRuntime.W.msb(32n, b), b)

def LexLeanRuntime.Fixed.wide66.Int32(x: Lean.Int32) -> Word(66n):
  +b = Lean.Int32.bits(x)
  LexLeanRuntime.W.resize(66n, 32n, LexLeanRuntime.W.msb(32n, b), b)

# Some of the low 32 bits when the n-bit two's complement value lies in the Int32 range.
def LexLeanRuntime.Fixed.narrow.Int32(+n: Nat, +v: Word(n)) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Maybe.unless(Lean.Int32, Bool.not(LexLeanRuntime.W.highSame(31n, n, LexLeanRuntime.W.msb(n, v), v)), Lean.Int32.mk{LexLeanRuntime.W.resize(32n, n, False{}, v)})

# if value < minimum then none else if maximum < value then none else some (fromInt value)
def LexLeanRuntime.checkedFromInt.Int32(value: L.Lean.Int) -> Maybe<&2, Lean.Int32>:
  match value:
    case L.ofNat{+n}:
      LexLeanRuntime.Maybe.unless(Lean.Int32, Bool.not(LexLeanRuntime.Nat.ltPow2(31n, n)), Lean.Int32.ofNat(n))
    case L.negSucc{+m}:
      LexLeanRuntime.Maybe.unless(Lean.Int32, Bool.not(LexLeanRuntime.Nat.ltPow2(31n, m)), Lean.Int32.mk{Word.not(32n, LexLeanRuntime.Nat.toWord(32n, m))})

def LexLeanRuntime.checkedAdd.Int32(left: Lean.Int32, right: Lean.Int32) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, Word.add(66n, LexLeanRuntime.Fixed.wide.Int32(left), LexLeanRuntime.Fixed.wide.Int32(right)))

def LexLeanRuntime.checkedSubtract.Int32(left: Lean.Int32, right: Lean.Int32) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, Word.sub(66n, LexLeanRuntime.Fixed.wide.Int32(left), LexLeanRuntime.Fixed.wide.Int32(right)))

def LexLeanRuntime.checkedMultiply.Int32(left: Lean.Int32, right: Lean.Int32) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, Word.mul(66n, LexLeanRuntime.Fixed.wide.Int32(left), LexLeanRuntime.Fixed.wide.Int32(right)))

def LexLeanRuntime.checkedNegate.Int32(value: Lean.Int32) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, LexLeanRuntime.W.neg(66n, LexLeanRuntime.Fixed.wide.Int32(value)))

def LexLeanRuntime.checkedQuotient.fin.Int32(z: Bool, left: Lean.Int32, right: Lean.Int32) -> Maybe<&2, Lean.Int32>:
  match z:
    case True{}:
      None{}
    case False{}:
      LexLeanRuntime.Fixed.narrow.Int32(66n, LexLeanRuntime.W.sdiv(66n, LexLeanRuntime.Fixed.wide.Int32(left), LexLeanRuntime.Fixed.wide.Int32(right)))

# if toInt right = 0 then none else checkedFromInt (Int.tdiv (toInt left) (toInt right))
def LexLeanRuntime.checkedQuotient.Int32(left: Lean.Int32, +right: Lean.Int32) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.checkedQuotient.fin.Int32(LexLeanRuntime.W.isZero(32n, Lean.Int32.bits(right)), left, right)

def LexLeanRuntime.ToMathInt.toInt.Int64(value: Lean.Int64) -> L.Lean.Int:
  Lean.Int64.toInt(value)

def LexLeanRuntime.Fixed.fromInt.Int64(value: L.Lean.Int) -> Lean.Int64:
  Lean.Int64.ofInt(value)

def LexLeanRuntime.Fixed.minimum.Int64() -> L.Lean.Int:
  L.negSucc{Word.to_nat(63n, Word.not(63n, Word.zero(63n)))}

def LexLeanRuntime.Fixed.maximum.Int64() -> L.Lean.Int:
  L.ofNat{Word.to_nat(63n, Word.not(63n, Word.zero(63n)))}

def LexLeanRuntime.Fixed.bitAnd.Int64(left: Lean.Int64, right: Lean.Int64) -> Lean.Int64:
  Lean.Int64.land(left, right)

def LexLeanRuntime.Fixed.bitOr.Int64(left: Lean.Int64, right: Lean.Int64) -> Lean.Int64:
  Lean.Int64.lor(left, right)

def LexLeanRuntime.Fixed.bitXor.Int64(left: Lean.Int64, right: Lean.Int64) -> Lean.Int64:
  Lean.Int64.xor(left, right)

def LexLeanRuntime.Fixed.bitNot.Int64(value: Lean.Int64) -> Lean.Int64:
  Lean.Int64.complement(value)

# if amount.toNat < 64 then some (Int64.shiftLeft value (Int64.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftLeft.Int64(value: Lean.Int64, +amount: U32) -> Maybe<&2, Lean.Int64>:
  Bool.pick(Maybe<&2, Lean.Int64>, U32.is_lt(amount, 64), Some{Lean.Int64.shiftLeft(value, Lean.Int64.ofNat(U32.to_nat(amount)))}, None{})

# if amount.toNat < 64 then some (Int64.shiftRight value (Int64.ofNat amount.toNat)) else none
def LexLeanRuntime.Fixed.shiftRight.Int64(value: Lean.Int64, +amount: U32) -> Maybe<&2, Lean.Int64>:
  Bool.pick(Maybe<&2, Lean.Int64>, U32.is_lt(amount, 64), Some{Lean.Int64.shiftRight(value, Lean.Int64.ofNat(U32.to_nat(amount)))}, None{})

def LexLeanRuntime.Fixed.wide.Int64(x: Lean.Int64) -> Word(130n):
  +b = Lean.Int64.bits(x)
  LexLeanRuntime.W.resize(130n, 64n, LexLeanRuntime.W.msb(64n, b), b)

def LexLeanRuntime.Fixed.wide66.Int64(x: Lean.Int64) -> Word(66n):
  +b = Lean.Int64.bits(x)
  LexLeanRuntime.W.resize(66n, 64n, LexLeanRuntime.W.msb(64n, b), b)

# Some of the low 64 bits when the n-bit two's complement value lies in the Int64 range.
def LexLeanRuntime.Fixed.narrow.Int64(+n: Nat, +v: Word(n)) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Maybe.unless(Lean.Int64, Bool.not(LexLeanRuntime.W.highSame(63n, n, LexLeanRuntime.W.msb(n, v), v)), Lean.Int64.mk{LexLeanRuntime.W.resize(64n, n, False{}, v)})

# if value < minimum then none else if maximum < value then none else some (fromInt value)
def LexLeanRuntime.checkedFromInt.Int64(value: L.Lean.Int) -> Maybe<&2, Lean.Int64>:
  match value:
    case L.ofNat{+n}:
      LexLeanRuntime.Maybe.unless(Lean.Int64, Bool.not(LexLeanRuntime.Nat.ltPow2(63n, n)), Lean.Int64.ofNat(n))
    case L.negSucc{+m}:
      LexLeanRuntime.Maybe.unless(Lean.Int64, Bool.not(LexLeanRuntime.Nat.ltPow2(63n, m)), Lean.Int64.mk{Word.not(64n, LexLeanRuntime.Nat.toWord(64n, m))})

def LexLeanRuntime.checkedAdd.Int64(left: Lean.Int64, right: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(130n, Word.add(130n, LexLeanRuntime.Fixed.wide.Int64(left), LexLeanRuntime.Fixed.wide.Int64(right)))

def LexLeanRuntime.checkedSubtract.Int64(left: Lean.Int64, right: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(130n, Word.sub(130n, LexLeanRuntime.Fixed.wide.Int64(left), LexLeanRuntime.Fixed.wide.Int64(right)))

def LexLeanRuntime.checkedMultiply.Int64(left: Lean.Int64, right: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(130n, Word.mul(130n, LexLeanRuntime.Fixed.wide.Int64(left), LexLeanRuntime.Fixed.wide.Int64(right)))

def LexLeanRuntime.checkedNegate.Int64(value: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(130n, LexLeanRuntime.W.neg(130n, LexLeanRuntime.Fixed.wide.Int64(value)))

def LexLeanRuntime.checkedQuotient.fin.Int64(z: Bool, left: Lean.Int64, right: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  match z:
    case True{}:
      None{}
    case False{}:
      LexLeanRuntime.Fixed.narrow.Int64(130n, LexLeanRuntime.W.sdiv(130n, LexLeanRuntime.Fixed.wide.Int64(left), LexLeanRuntime.Fixed.wide.Int64(right)))

# if toInt right = 0 then none else checkedFromInt (Int.tdiv (toInt left) (toInt right))
def LexLeanRuntime.checkedQuotient.Int64(left: Lean.Int64, +right: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.checkedQuotient.fin.Int64(LexLeanRuntime.W.isZero(64n, Lean.Int64.bits(right)), left, right)

# checkedConvert value = checkedFromInt (toInt value): from Int through
# checkedFromInt; from a fixed type through the exact 66-bit widening.
def LexLeanRuntime.checkedConvert.Int.UInt8(value: L.Lean.Int) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.checkedFromInt.UInt8(value)

def LexLeanRuntime.checkedConvert.Int.UInt16(value: L.Lean.Int) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.checkedFromInt.UInt16(value)

def LexLeanRuntime.checkedConvert.Int.UInt32(value: L.Lean.Int) -> Maybe<&2, U32>:
  LexLeanRuntime.checkedFromInt.UInt32(value)

def LexLeanRuntime.checkedConvert.Int.UInt64(value: L.Lean.Int) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.checkedFromInt.UInt64(value)

def LexLeanRuntime.checkedConvert.Int.Int8(value: L.Lean.Int) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.checkedFromInt.Int8(value)

def LexLeanRuntime.checkedConvert.Int.Int16(value: L.Lean.Int) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.checkedFromInt.Int16(value)

def LexLeanRuntime.checkedConvert.Int.Int32(value: L.Lean.Int) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.checkedFromInt.Int32(value)

def LexLeanRuntime.checkedConvert.Int.Int64(value: L.Lean.Int) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.checkedFromInt.Int64(value)

def LexLeanRuntime.checkedConvert.UInt8.UInt8(value: Lean.UInt8) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(66n, LexLeanRuntime.Fixed.wide66.UInt8(value))

def LexLeanRuntime.checkedConvert.UInt8.UInt16(value: Lean.UInt8) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(66n, LexLeanRuntime.Fixed.wide66.UInt8(value))

def LexLeanRuntime.checkedConvert.UInt8.UInt32(value: Lean.UInt8) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, LexLeanRuntime.Fixed.wide66.UInt8(value))

def LexLeanRuntime.checkedConvert.UInt8.UInt64(value: Lean.UInt8) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(66n, LexLeanRuntime.Fixed.wide66.UInt8(value))

def LexLeanRuntime.checkedConvert.UInt8.Int8(value: Lean.UInt8) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(66n, LexLeanRuntime.Fixed.wide66.UInt8(value))

def LexLeanRuntime.checkedConvert.UInt8.Int16(value: Lean.UInt8) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(66n, LexLeanRuntime.Fixed.wide66.UInt8(value))

def LexLeanRuntime.checkedConvert.UInt8.Int32(value: Lean.UInt8) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, LexLeanRuntime.Fixed.wide66.UInt8(value))

def LexLeanRuntime.checkedConvert.UInt8.Int64(value: Lean.UInt8) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(66n, LexLeanRuntime.Fixed.wide66.UInt8(value))

def LexLeanRuntime.checkedConvert.UInt16.UInt8(value: Lean.UInt16) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(66n, LexLeanRuntime.Fixed.wide66.UInt16(value))

def LexLeanRuntime.checkedConvert.UInt16.UInt16(value: Lean.UInt16) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(66n, LexLeanRuntime.Fixed.wide66.UInt16(value))

def LexLeanRuntime.checkedConvert.UInt16.UInt32(value: Lean.UInt16) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, LexLeanRuntime.Fixed.wide66.UInt16(value))

def LexLeanRuntime.checkedConvert.UInt16.UInt64(value: Lean.UInt16) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(66n, LexLeanRuntime.Fixed.wide66.UInt16(value))

def LexLeanRuntime.checkedConvert.UInt16.Int8(value: Lean.UInt16) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(66n, LexLeanRuntime.Fixed.wide66.UInt16(value))

def LexLeanRuntime.checkedConvert.UInt16.Int16(value: Lean.UInt16) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(66n, LexLeanRuntime.Fixed.wide66.UInt16(value))

def LexLeanRuntime.checkedConvert.UInt16.Int32(value: Lean.UInt16) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, LexLeanRuntime.Fixed.wide66.UInt16(value))

def LexLeanRuntime.checkedConvert.UInt16.Int64(value: Lean.UInt16) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(66n, LexLeanRuntime.Fixed.wide66.UInt16(value))

def LexLeanRuntime.checkedConvert.UInt32.UInt8(value: U32) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(66n, LexLeanRuntime.Fixed.wide66.UInt32(value))

def LexLeanRuntime.checkedConvert.UInt32.UInt16(value: U32) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(66n, LexLeanRuntime.Fixed.wide66.UInt32(value))

def LexLeanRuntime.checkedConvert.UInt32.UInt32(value: U32) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, LexLeanRuntime.Fixed.wide66.UInt32(value))

def LexLeanRuntime.checkedConvert.UInt32.UInt64(value: U32) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(66n, LexLeanRuntime.Fixed.wide66.UInt32(value))

def LexLeanRuntime.checkedConvert.UInt32.Int8(value: U32) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(66n, LexLeanRuntime.Fixed.wide66.UInt32(value))

def LexLeanRuntime.checkedConvert.UInt32.Int16(value: U32) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(66n, LexLeanRuntime.Fixed.wide66.UInt32(value))

def LexLeanRuntime.checkedConvert.UInt32.Int32(value: U32) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, LexLeanRuntime.Fixed.wide66.UInt32(value))

def LexLeanRuntime.checkedConvert.UInt32.Int64(value: U32) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(66n, LexLeanRuntime.Fixed.wide66.UInt32(value))

def LexLeanRuntime.checkedConvert.UInt64.UInt8(value: Lean.UInt64) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(66n, LexLeanRuntime.Fixed.wide66.UInt64(value))

def LexLeanRuntime.checkedConvert.UInt64.UInt16(value: Lean.UInt64) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(66n, LexLeanRuntime.Fixed.wide66.UInt64(value))

def LexLeanRuntime.checkedConvert.UInt64.UInt32(value: Lean.UInt64) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, LexLeanRuntime.Fixed.wide66.UInt64(value))

def LexLeanRuntime.checkedConvert.UInt64.UInt64(value: Lean.UInt64) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(66n, LexLeanRuntime.Fixed.wide66.UInt64(value))

def LexLeanRuntime.checkedConvert.UInt64.Int8(value: Lean.UInt64) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(66n, LexLeanRuntime.Fixed.wide66.UInt64(value))

def LexLeanRuntime.checkedConvert.UInt64.Int16(value: Lean.UInt64) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(66n, LexLeanRuntime.Fixed.wide66.UInt64(value))

def LexLeanRuntime.checkedConvert.UInt64.Int32(value: Lean.UInt64) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, LexLeanRuntime.Fixed.wide66.UInt64(value))

def LexLeanRuntime.checkedConvert.UInt64.Int64(value: Lean.UInt64) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(66n, LexLeanRuntime.Fixed.wide66.UInt64(value))

def LexLeanRuntime.checkedConvert.Int8.UInt8(value: Lean.Int8) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(66n, LexLeanRuntime.Fixed.wide66.Int8(value))

def LexLeanRuntime.checkedConvert.Int8.UInt16(value: Lean.Int8) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(66n, LexLeanRuntime.Fixed.wide66.Int8(value))

def LexLeanRuntime.checkedConvert.Int8.UInt32(value: Lean.Int8) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, LexLeanRuntime.Fixed.wide66.Int8(value))

def LexLeanRuntime.checkedConvert.Int8.UInt64(value: Lean.Int8) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(66n, LexLeanRuntime.Fixed.wide66.Int8(value))

def LexLeanRuntime.checkedConvert.Int8.Int8(value: Lean.Int8) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(66n, LexLeanRuntime.Fixed.wide66.Int8(value))

def LexLeanRuntime.checkedConvert.Int8.Int16(value: Lean.Int8) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(66n, LexLeanRuntime.Fixed.wide66.Int8(value))

def LexLeanRuntime.checkedConvert.Int8.Int32(value: Lean.Int8) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, LexLeanRuntime.Fixed.wide66.Int8(value))

def LexLeanRuntime.checkedConvert.Int8.Int64(value: Lean.Int8) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(66n, LexLeanRuntime.Fixed.wide66.Int8(value))

def LexLeanRuntime.checkedConvert.Int16.UInt8(value: Lean.Int16) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(66n, LexLeanRuntime.Fixed.wide66.Int16(value))

def LexLeanRuntime.checkedConvert.Int16.UInt16(value: Lean.Int16) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(66n, LexLeanRuntime.Fixed.wide66.Int16(value))

def LexLeanRuntime.checkedConvert.Int16.UInt32(value: Lean.Int16) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, LexLeanRuntime.Fixed.wide66.Int16(value))

def LexLeanRuntime.checkedConvert.Int16.UInt64(value: Lean.Int16) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(66n, LexLeanRuntime.Fixed.wide66.Int16(value))

def LexLeanRuntime.checkedConvert.Int16.Int8(value: Lean.Int16) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(66n, LexLeanRuntime.Fixed.wide66.Int16(value))

def LexLeanRuntime.checkedConvert.Int16.Int16(value: Lean.Int16) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(66n, LexLeanRuntime.Fixed.wide66.Int16(value))

def LexLeanRuntime.checkedConvert.Int16.Int32(value: Lean.Int16) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, LexLeanRuntime.Fixed.wide66.Int16(value))

def LexLeanRuntime.checkedConvert.Int16.Int64(value: Lean.Int16) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(66n, LexLeanRuntime.Fixed.wide66.Int16(value))

def LexLeanRuntime.checkedConvert.Int32.UInt8(value: Lean.Int32) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(66n, LexLeanRuntime.Fixed.wide66.Int32(value))

def LexLeanRuntime.checkedConvert.Int32.UInt16(value: Lean.Int32) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(66n, LexLeanRuntime.Fixed.wide66.Int32(value))

def LexLeanRuntime.checkedConvert.Int32.UInt32(value: Lean.Int32) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, LexLeanRuntime.Fixed.wide66.Int32(value))

def LexLeanRuntime.checkedConvert.Int32.UInt64(value: Lean.Int32) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(66n, LexLeanRuntime.Fixed.wide66.Int32(value))

def LexLeanRuntime.checkedConvert.Int32.Int8(value: Lean.Int32) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(66n, LexLeanRuntime.Fixed.wide66.Int32(value))

def LexLeanRuntime.checkedConvert.Int32.Int16(value: Lean.Int32) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(66n, LexLeanRuntime.Fixed.wide66.Int32(value))

def LexLeanRuntime.checkedConvert.Int32.Int32(value: Lean.Int32) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, LexLeanRuntime.Fixed.wide66.Int32(value))

def LexLeanRuntime.checkedConvert.Int32.Int64(value: Lean.Int32) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(66n, LexLeanRuntime.Fixed.wide66.Int32(value))

def LexLeanRuntime.checkedConvert.Int64.UInt8(value: Lean.Int64) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.narrow.UInt8(66n, LexLeanRuntime.Fixed.wide66.Int64(value))

def LexLeanRuntime.checkedConvert.Int64.UInt16(value: Lean.Int64) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.narrow.UInt16(66n, LexLeanRuntime.Fixed.wide66.Int64(value))

def LexLeanRuntime.checkedConvert.Int64.UInt32(value: Lean.Int64) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.narrow.UInt32(66n, LexLeanRuntime.Fixed.wide66.Int64(value))

def LexLeanRuntime.checkedConvert.Int64.UInt64(value: Lean.Int64) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.narrow.UInt64(66n, LexLeanRuntime.Fixed.wide66.Int64(value))

def LexLeanRuntime.checkedConvert.Int64.Int8(value: Lean.Int64) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.narrow.Int8(66n, LexLeanRuntime.Fixed.wide66.Int64(value))

def LexLeanRuntime.checkedConvert.Int64.Int16(value: Lean.Int64) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.narrow.Int16(66n, LexLeanRuntime.Fixed.wide66.Int64(value))

def LexLeanRuntime.checkedConvert.Int64.Int32(value: Lean.Int64) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.narrow.Int32(66n, LexLeanRuntime.Fixed.wide66.Int64(value))

def LexLeanRuntime.checkedConvert.Int64.Int64(value: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.narrow.Int64(66n, LexLeanRuntime.Fixed.wide66.Int64(value))

# ---------------------------------------------------------------------------
# The Int64 checked operations, transcribed: wrapping Int64/UInt64 arithmetic
# and the fuelled magnitude division and multiplication (fuel 64).
# ---------------------------------------------------------------------------

def LexLeanRuntime.checkedAddInt64(+left: Lean.Int64, +right: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  +value = Lean.Int64.add(left, right)
  LexLeanRuntime.Maybe.unless(Lean.Int64, L.Lean.Bool.or(L.Lean.Bool.and(Lean.Int64.decLt(Lean.Int64.lit(0), right), Lean.Int64.decLt(value, left)), L.Lean.Bool.and(Lean.Int64.decLt(right, Lean.Int64.lit(0)), Lean.Int64.decLt(left, value))), value)

def LexLeanRuntime.checkedSubtractInt64(+left: Lean.Int64, +right: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  +value = Lean.Int64.sub(left, right)
  LexLeanRuntime.Maybe.unless(Lean.Int64, L.Lean.Bool.or(L.Lean.Bool.and(Lean.Int64.decLt(Lean.Int64.lit(0), right), Lean.Int64.decLt(left, value)), L.Lean.Bool.and(Lean.Int64.decLt(right, Lean.Int64.lit(0)), Lean.Int64.decLt(value, left))), value)

def LexLeanRuntime.checkedNegateInt64(+value: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Maybe.unless(Lean.Int64, Lean.Int64.beq(value, Lean.Int64.neg(Lean.Int64.lit2(2147483648, 0))), Lean.Int64.neg(value))

def LexLeanRuntime.magnitudeInt64(+value: Lean.Int64) -> Lean.UInt64:
  +bits = Lean.Int64.toUInt64(value)
  Bool.pick(Lean.UInt64, Lean.Int64.decLt(value, Lean.Int64.lit(0)), Lean.UInt64.sub(Lean.UInt64.lit(0), bits), bits)

def LexLeanRuntime.signedMagnitudeInt64(negative: Bool, +value: Lean.UInt64) -> Lean.Int64:
  Lean.UInt64.toInt64(Bool.pick(Lean.UInt64, negative, Lean.UInt64.sub(Lean.UInt64.lit(0), value), value))

def LexLeanRuntime.divideMagnitudeInt64(fuel: Nat, +source: Lean.UInt64, +divisor: Lean.UInt64, +remainder: Lean.UInt64, +quotient: Lean.UInt64) -> Lean.UInt64:
  match fuel:
    case 0n:
      quotient
    case 1n+f:
      +high = Lean.UInt64.decLe(Lean.UInt64.lit2(2147483648, 0), source)
      +rem2 = Lean.UInt64.add(Lean.UInt64.add(remainder, remainder), Bool.pick(Lean.UInt64, high, Lean.UInt64.lit(1), Lean.UInt64.lit(0)))
      +quo2 = Lean.UInt64.add(quotient, quotient)
      +fits = Lean.UInt64.decLe(divisor, rem2)
      LexLeanRuntime.divideMagnitudeInt64(f, Lean.UInt64.add(source, source), divisor, Bool.pick(Lean.UInt64, fits, Lean.UInt64.sub(rem2, divisor), rem2), Bool.pick(Lean.UInt64, fits, Lean.UInt64.add(quo2, Lean.UInt64.lit(1)), quo2))

def LexLeanRuntime.checkedQuotientInt64(+left: Lean.Int64, +right: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  +negative = Lean.Bool.bne(Lean.Int64.decLt(left, Lean.Int64.lit(0)), Lean.Int64.decLt(right, Lean.Int64.lit(0)))
  Bool.pick(Maybe<&2, Lean.Int64>, Lean.Int64.beq(right, Lean.Int64.lit(0)), None{}, Bool.pick(Maybe<&2, Lean.Int64>, L.Lean.Bool.and(Lean.Int64.beq(left, Lean.Int64.neg(Lean.Int64.lit2(2147483648, 0))), Lean.Int64.beq(right, Lean.Int64.neg(Lean.Int64.lit(1)))), None{}, Some{LexLeanRuntime.signedMagnitudeInt64(negative, LexLeanRuntime.divideMagnitudeInt64(64n, LexLeanRuntime.magnitudeInt64(left), LexLeanRuntime.magnitudeInt64(right), Lean.UInt64.lit(0), Lean.UInt64.lit(0)))}))

def LexLeanRuntime.multiplyMagnitudeInt64(fuel: Nat, +source: Lean.UInt64, +multiplicand: Lean.UInt64, +accumulator: Lean.UInt64, +negative: Bool) -> Maybe<&2, Lean.UInt64>:
  match fuel:
    case 0n:
      Some{accumulator}
    case 1n+f:
      +high = Lean.UInt64.decLe(Lean.UInt64.lit2(2147483648, 0), source)
      +limit = Bool.pick(Lean.UInt64, negative, Lean.UInt64.lit2(2147483648, 0), Lean.UInt64.lit2(2147483647, 4294967295))
      +halfLimit = Bool.pick(Lean.UInt64, negative, Lean.UInt64.lit2(1073741824, 0), Lean.UInt64.lit2(1073741823, 4294967295))
      +doubled = Lean.UInt64.add(accumulator, accumulator)
      +next = LexLeanRuntime.multiplyMagnitudeInt64(f, Lean.UInt64.add(source, source), multiplicand, Bool.pick(Lean.UInt64, high, Lean.UInt64.add(doubled, multiplicand), doubled), negative)
      Bool.pick(Maybe<&2, Lean.UInt64>, Lean.UInt64.decLt(halfLimit, accumulator), None{}, Bool.pick(Maybe<&2, Lean.UInt64>, high, Bool.pick(Maybe<&2, Lean.UInt64>, L.Lean.Bool.or(Lean.UInt64.decLt(limit, multiplicand), Lean.UInt64.decLt(Lean.UInt64.sub(limit, multiplicand), doubled)), None{}, next), next))

def LexLeanRuntime.checkedMultiplyInt64.fin(m: Maybe<&2, Lean.UInt64>, negative: Bool) -> Maybe<&2, Lean.Int64>:
  match m:
    case None{}:
      None{}
    case Some{value}:
      Some{LexLeanRuntime.signedMagnitudeInt64(negative, value)}

def LexLeanRuntime.checkedMultiplyInt64(+left: Lean.Int64, +right: Lean.Int64) -> Maybe<&2, Lean.Int64>:
  +negative = Lean.Bool.bne(Lean.Int64.decLt(left, Lean.Int64.lit(0)), Lean.Int64.decLt(right, Lean.Int64.lit(0)))
  LexLeanRuntime.checkedMultiplyInt64.fin(LexLeanRuntime.multiplyMagnitudeInt64(64n, LexLeanRuntime.magnitudeInt64(right), LexLeanRuntime.magnitudeInt64(left), Lean.UInt64.lit(0), negative), negative)

# ---------------------------------------------------------------------------
# subtract, multiply, negate (Sub, Mul, Neg instances), Quotient, bit operations.
# ---------------------------------------------------------------------------

def LexLeanRuntime.subtract.Nat(left: Nat, right: Nat) -> Nat:
  L.Lean.Nat.sub(left, right)

def LexLeanRuntime.multiply.Nat(left: Nat, right: Nat) -> Nat:
  L.Lean.Nat.mul(left, right)

def LexLeanRuntime.subtract.Int(left: L.Lean.Int, right: L.Lean.Int) -> L.Lean.Int:
  L.Lean.Int.sub(left, right)

def LexLeanRuntime.multiply.Int(left: L.Lean.Int, right: L.Lean.Int) -> L.Lean.Int:
  L.Lean.Int.mul(left, right)

def LexLeanRuntime.negate.Int(value: L.Lean.Int) -> L.Lean.Int:
  L.Lean.Int.neg(value)

def LexLeanRuntime.subtract.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.sub(left, right)

def LexLeanRuntime.multiply.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.mul(left, right)

def LexLeanRuntime.negate.UInt8(value: Lean.UInt8) -> Lean.UInt8:
  Lean.UInt8.neg(value)

def LexLeanRuntime.subtract.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.sub(left, right)

def LexLeanRuntime.multiply.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.mul(left, right)

def LexLeanRuntime.negate.UInt16(value: Lean.UInt16) -> Lean.UInt16:
  Lean.UInt16.neg(value)

def LexLeanRuntime.subtract.UInt32(left: U32, right: U32) -> U32:
  Lean.UInt32.sub(left, right)

def LexLeanRuntime.multiply.UInt32(left: U32, right: U32) -> U32:
  Lean.UInt32.mul(left, right)

def LexLeanRuntime.negate.UInt32(value: U32) -> U32:
  Lean.UInt32.neg(value)

def LexLeanRuntime.subtract.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.sub(left, right)

def LexLeanRuntime.multiply.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.mul(left, right)

def LexLeanRuntime.negate.UInt64(value: Lean.UInt64) -> Lean.UInt64:
  Lean.UInt64.neg(value)

def LexLeanRuntime.subtract.Int8(left: Lean.Int8, right: Lean.Int8) -> Lean.Int8:
  Lean.Int8.sub(left, right)

def LexLeanRuntime.multiply.Int8(left: Lean.Int8, right: Lean.Int8) -> Lean.Int8:
  Lean.Int8.mul(left, right)

def LexLeanRuntime.negate.Int8(value: Lean.Int8) -> Lean.Int8:
  Lean.Int8.neg(value)

def LexLeanRuntime.subtract.Int16(left: Lean.Int16, right: Lean.Int16) -> Lean.Int16:
  Lean.Int16.sub(left, right)

def LexLeanRuntime.multiply.Int16(left: Lean.Int16, right: Lean.Int16) -> Lean.Int16:
  Lean.Int16.mul(left, right)

def LexLeanRuntime.negate.Int16(value: Lean.Int16) -> Lean.Int16:
  Lean.Int16.neg(value)

def LexLeanRuntime.subtract.Int32(left: Lean.Int32, right: Lean.Int32) -> Lean.Int32:
  Lean.Int32.sub(left, right)

def LexLeanRuntime.multiply.Int32(left: Lean.Int32, right: Lean.Int32) -> Lean.Int32:
  Lean.Int32.mul(left, right)

def LexLeanRuntime.negate.Int32(value: Lean.Int32) -> Lean.Int32:
  Lean.Int32.neg(value)

def LexLeanRuntime.subtract.Int64(left: Lean.Int64, right: Lean.Int64) -> Lean.Int64:
  Lean.Int64.sub(left, right)

def LexLeanRuntime.multiply.Int64(left: Lean.Int64, right: Lean.Int64) -> Lean.Int64:
  Lean.Int64.mul(left, right)

def LexLeanRuntime.negate.Int64(value: Lean.Int64) -> Lean.Int64:
  Lean.Int64.neg(value)

def LexLeanRuntime.Quotient.quotient.Nat(left: Nat, right: Nat) -> Nat:
  L.Lean.Nat.div(left, right)

def LexLeanRuntime.Quotient.remainder.Nat(left: Nat, right: Nat) -> Nat:
  L.Lean.Nat.mod(left, right)

def LexLeanRuntime.Quotient.isZero.Nat(value: Nat) -> Bool:
  L.Lean.Nat.beq(value, 0n)

def LexLeanRuntime.Quotient.quotient.Int(left: L.Lean.Int, right: L.Lean.Int) -> L.Lean.Int:
  Lean.Int.tdiv(left, right)

def LexLeanRuntime.Quotient.remainder.Int(left: L.Lean.Int, right: L.Lean.Int) -> L.Lean.Int:
  Lean.Int.tmod(left, right)

def LexLeanRuntime.Quotient.isZero.Int(value: L.Lean.Int) -> Bool:
  Lean.Int.beq(value, L.ofNat{0n})

def LexLeanRuntime.quotient.fin.Nat(z: Bool, left: Nat, right: Nat, zeroCase: Nat) -> Nat:
  match z:
    case True{}:
      zeroCase
    case False{}:
      LexLeanRuntime.Quotient.quotient.Nat(left, right)

# if Quotient.isZero right then zeroCase else Quotient.quotient left right
def LexLeanRuntime.quotient.Nat(left: Nat, +right: Nat, zeroCase: Nat) -> Nat:
  LexLeanRuntime.quotient.fin.Nat(LexLeanRuntime.Quotient.isZero.Nat(right), left, right, zeroCase)

def LexLeanRuntime.remainder.fin.Nat(z: Bool, left: Nat, right: Nat, zeroCase: Nat) -> Nat:
  match z:
    case True{}:
      zeroCase
    case False{}:
      LexLeanRuntime.Quotient.remainder.Nat(left, right)

# if Quotient.isZero right then zeroCase else Quotient.remainder left right
def LexLeanRuntime.remainder.Nat(left: Nat, +right: Nat, zeroCase: Nat) -> Nat:
  LexLeanRuntime.remainder.fin.Nat(LexLeanRuntime.Quotient.isZero.Nat(right), left, right, zeroCase)

def LexLeanRuntime.quotient.fin.Int(z: Bool, left: L.Lean.Int, right: L.Lean.Int, zeroCase: L.Lean.Int) -> L.Lean.Int:
  match z:
    case True{}:
      zeroCase
    case False{}:
      LexLeanRuntime.Quotient.quotient.Int(left, right)

# if Quotient.isZero right then zeroCase else Quotient.quotient left right
def LexLeanRuntime.quotient.Int(left: L.Lean.Int, +right: L.Lean.Int, zeroCase: L.Lean.Int) -> L.Lean.Int:
  LexLeanRuntime.quotient.fin.Int(LexLeanRuntime.Quotient.isZero.Int(right), left, right, zeroCase)

def LexLeanRuntime.remainder.fin.Int(z: Bool, left: L.Lean.Int, right: L.Lean.Int, zeroCase: L.Lean.Int) -> L.Lean.Int:
  match z:
    case True{}:
      zeroCase
    case False{}:
      LexLeanRuntime.Quotient.remainder.Int(left, right)

# if Quotient.isZero right then zeroCase else Quotient.remainder left right
def LexLeanRuntime.remainder.Int(left: L.Lean.Int, +right: L.Lean.Int, zeroCase: L.Lean.Int) -> L.Lean.Int:
  LexLeanRuntime.remainder.fin.Int(LexLeanRuntime.Quotient.isZero.Int(right), left, right, zeroCase)

def LexLeanRuntime.bitAnd.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Lean.UInt8:
  LexLeanRuntime.Fixed.bitAnd.UInt8(left, right)

def LexLeanRuntime.bitOr.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Lean.UInt8:
  LexLeanRuntime.Fixed.bitOr.UInt8(left, right)

def LexLeanRuntime.bitXor.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Lean.UInt8:
  LexLeanRuntime.Fixed.bitXor.UInt8(left, right)

def LexLeanRuntime.bitNot.UInt8(value: Lean.UInt8) -> Lean.UInt8:
  LexLeanRuntime.Fixed.bitNot.UInt8(value)

def LexLeanRuntime.shiftLeft.UInt8(value: Lean.UInt8, amount: U32) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.shiftLeft.UInt8(value, amount)

def LexLeanRuntime.shiftRight.UInt8(value: Lean.UInt8, amount: U32) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Fixed.shiftRight.UInt8(value, amount)

def LexLeanRuntime.bitAnd.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Lean.UInt16:
  LexLeanRuntime.Fixed.bitAnd.UInt16(left, right)

def LexLeanRuntime.bitOr.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Lean.UInt16:
  LexLeanRuntime.Fixed.bitOr.UInt16(left, right)

def LexLeanRuntime.bitXor.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Lean.UInt16:
  LexLeanRuntime.Fixed.bitXor.UInt16(left, right)

def LexLeanRuntime.bitNot.UInt16(value: Lean.UInt16) -> Lean.UInt16:
  LexLeanRuntime.Fixed.bitNot.UInt16(value)

def LexLeanRuntime.shiftLeft.UInt16(value: Lean.UInt16, amount: U32) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.shiftLeft.UInt16(value, amount)

def LexLeanRuntime.shiftRight.UInt16(value: Lean.UInt16, amount: U32) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Fixed.shiftRight.UInt16(value, amount)

def LexLeanRuntime.bitAnd.UInt32(left: U32, right: U32) -> U32:
  LexLeanRuntime.Fixed.bitAnd.UInt32(left, right)

def LexLeanRuntime.bitOr.UInt32(left: U32, right: U32) -> U32:
  LexLeanRuntime.Fixed.bitOr.UInt32(left, right)

def LexLeanRuntime.bitXor.UInt32(left: U32, right: U32) -> U32:
  LexLeanRuntime.Fixed.bitXor.UInt32(left, right)

def LexLeanRuntime.bitNot.UInt32(value: U32) -> U32:
  LexLeanRuntime.Fixed.bitNot.UInt32(value)

def LexLeanRuntime.shiftLeft.UInt32(value: U32, amount: U32) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.shiftLeft.UInt32(value, amount)

def LexLeanRuntime.shiftRight.UInt32(value: U32, amount: U32) -> Maybe<&2, U32>:
  LexLeanRuntime.Fixed.shiftRight.UInt32(value, amount)

def LexLeanRuntime.bitAnd.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Lean.UInt64:
  LexLeanRuntime.Fixed.bitAnd.UInt64(left, right)

def LexLeanRuntime.bitOr.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Lean.UInt64:
  LexLeanRuntime.Fixed.bitOr.UInt64(left, right)

def LexLeanRuntime.bitXor.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Lean.UInt64:
  LexLeanRuntime.Fixed.bitXor.UInt64(left, right)

def LexLeanRuntime.bitNot.UInt64(value: Lean.UInt64) -> Lean.UInt64:
  LexLeanRuntime.Fixed.bitNot.UInt64(value)

def LexLeanRuntime.shiftLeft.UInt64(value: Lean.UInt64, amount: U32) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.shiftLeft.UInt64(value, amount)

def LexLeanRuntime.shiftRight.UInt64(value: Lean.UInt64, amount: U32) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Fixed.shiftRight.UInt64(value, amount)

def LexLeanRuntime.bitAnd.Int8(left: Lean.Int8, right: Lean.Int8) -> Lean.Int8:
  LexLeanRuntime.Fixed.bitAnd.Int8(left, right)

def LexLeanRuntime.bitOr.Int8(left: Lean.Int8, right: Lean.Int8) -> Lean.Int8:
  LexLeanRuntime.Fixed.bitOr.Int8(left, right)

def LexLeanRuntime.bitXor.Int8(left: Lean.Int8, right: Lean.Int8) -> Lean.Int8:
  LexLeanRuntime.Fixed.bitXor.Int8(left, right)

def LexLeanRuntime.bitNot.Int8(value: Lean.Int8) -> Lean.Int8:
  LexLeanRuntime.Fixed.bitNot.Int8(value)

def LexLeanRuntime.shiftLeft.Int8(value: Lean.Int8, amount: U32) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.shiftLeft.Int8(value, amount)

def LexLeanRuntime.shiftRight.Int8(value: Lean.Int8, amount: U32) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Fixed.shiftRight.Int8(value, amount)

def LexLeanRuntime.bitAnd.Int16(left: Lean.Int16, right: Lean.Int16) -> Lean.Int16:
  LexLeanRuntime.Fixed.bitAnd.Int16(left, right)

def LexLeanRuntime.bitOr.Int16(left: Lean.Int16, right: Lean.Int16) -> Lean.Int16:
  LexLeanRuntime.Fixed.bitOr.Int16(left, right)

def LexLeanRuntime.bitXor.Int16(left: Lean.Int16, right: Lean.Int16) -> Lean.Int16:
  LexLeanRuntime.Fixed.bitXor.Int16(left, right)

def LexLeanRuntime.bitNot.Int16(value: Lean.Int16) -> Lean.Int16:
  LexLeanRuntime.Fixed.bitNot.Int16(value)

def LexLeanRuntime.shiftLeft.Int16(value: Lean.Int16, amount: U32) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.shiftLeft.Int16(value, amount)

def LexLeanRuntime.shiftRight.Int16(value: Lean.Int16, amount: U32) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Fixed.shiftRight.Int16(value, amount)

def LexLeanRuntime.bitAnd.Int32(left: Lean.Int32, right: Lean.Int32) -> Lean.Int32:
  LexLeanRuntime.Fixed.bitAnd.Int32(left, right)

def LexLeanRuntime.bitOr.Int32(left: Lean.Int32, right: Lean.Int32) -> Lean.Int32:
  LexLeanRuntime.Fixed.bitOr.Int32(left, right)

def LexLeanRuntime.bitXor.Int32(left: Lean.Int32, right: Lean.Int32) -> Lean.Int32:
  LexLeanRuntime.Fixed.bitXor.Int32(left, right)

def LexLeanRuntime.bitNot.Int32(value: Lean.Int32) -> Lean.Int32:
  LexLeanRuntime.Fixed.bitNot.Int32(value)

def LexLeanRuntime.shiftLeft.Int32(value: Lean.Int32, amount: U32) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.shiftLeft.Int32(value, amount)

def LexLeanRuntime.shiftRight.Int32(value: Lean.Int32, amount: U32) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Fixed.shiftRight.Int32(value, amount)

def LexLeanRuntime.bitAnd.Int64(left: Lean.Int64, right: Lean.Int64) -> Lean.Int64:
  LexLeanRuntime.Fixed.bitAnd.Int64(left, right)

def LexLeanRuntime.bitOr.Int64(left: Lean.Int64, right: Lean.Int64) -> Lean.Int64:
  LexLeanRuntime.Fixed.bitOr.Int64(left, right)

def LexLeanRuntime.bitXor.Int64(left: Lean.Int64, right: Lean.Int64) -> Lean.Int64:
  LexLeanRuntime.Fixed.bitXor.Int64(left, right)

def LexLeanRuntime.bitNot.Int64(value: Lean.Int64) -> Lean.Int64:
  LexLeanRuntime.Fixed.bitNot.Int64(value)

def LexLeanRuntime.shiftLeft.Int64(value: Lean.Int64, amount: U32) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.shiftLeft.Int64(value, amount)

def LexLeanRuntime.shiftRight.Int64(value: Lean.Int64, amount: U32) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Fixed.shiftRight.Int64(value, amount)

# ---------------------------------------------------------------------------
# append, length, index, slice (Appendable, Lengthable, Indexable, Sliceable).
# ---------------------------------------------------------------------------

def LexLeanRuntime.Appendable.append.List(-A: Data, left: List<&2, A>, right: List<&2, A>) -> List<&2, A>:
  L.Lean.List.append(A, left, right)

def LexLeanRuntime.Appendable.append.ByteArray(left: Lean.ByteArray, right: Lean.ByteArray) -> Lean.ByteArray:
  Lean.ByteArray.append(left, right)

def LexLeanRuntime.append.List(-A: Data, left: List<&2, A>, right: List<&2, A>) -> List<&2, A>:
  LexLeanRuntime.Appendable.append.List(A, left, right)

def LexLeanRuntime.append.ByteArray(left: Lean.ByteArray, right: Lean.ByteArray) -> Lean.ByteArray:
  LexLeanRuntime.Appendable.append.ByteArray(left, right)

def LexLeanRuntime.Lengthable.length.List(-A: Data, value: List<&2, A>) -> Nat:
  L.Lean.List.length(A, value)

def LexLeanRuntime.Lengthable.length.ByteArray(value: Lean.ByteArray) -> Nat:
  Lean.ByteArray.size(value)

def LexLeanRuntime.Lengthable.length.String(value: String) -> Nat:
  Lean.String.length(value)

def LexLeanRuntime.length.List(-A: Data, value: List<&2, A>) -> Nat:
  LexLeanRuntime.Lengthable.length.List(A, value)

def LexLeanRuntime.length.ByteArray(value: Lean.ByteArray) -> Nat:
  LexLeanRuntime.Lengthable.length.ByteArray(value)

def LexLeanRuntime.length.String(value: String) -> Nat:
  LexLeanRuntime.Lengthable.length.String(value)

def LexLeanRuntime.listIndex(-A: Data, xs: List<&2, A>, i: Nat) -> Maybe<&2, A>:
  match xs i:
    case Nil{} _:
      None{}
    case Con{head, tail} 0n:
      Some{head}
    case Con{head, tail} 1n+index:
      LexLeanRuntime.listIndex(A, tail, index)

def LexLeanRuntime.Indexable.index.List(-A: Data, value: List<&2, A>, offset: Nat) -> Maybe<&2, A>:
  LexLeanRuntime.listIndex(A, value, offset)

# value.data[offset]? : the byte at offset, if offset < size.
def LexLeanRuntime.Indexable.index.ByteArray(value: Lean.ByteArray, offset: Nat) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.listIndex(Lean.UInt8, Lean.ByteArray.data(value), offset)

def LexLeanRuntime.index.List(-A: Data, value: List<&2, A>, offset: Nat) -> Maybe<&2, A>:
  LexLeanRuntime.Indexable.index.List(A, value, offset)

def LexLeanRuntime.index.ByteArray(value: Lean.ByteArray, offset: Nat) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Indexable.index.ByteArray(value, offset)

# if start + count <= value.length then some ((value.drop start).take count) else none
def LexLeanRuntime.Sliceable.slice.List(-A: Data, +value: List<&2, A>, +start: Nat, +count: Nat) -> Maybe<&2, List<&2, A>>:
  Bool.pick(Maybe<&2, List<&2, A>>, L.Lean.Nat.ble(L.Lean.Nat.add(start, count), L.Lean.List.length(A, value)), Some{Lean.List.take(A, count, Lean.List.drop(A, start, value))}, None{})

# if start + count <= value.size then some (value.extract start (start + count)) else none
def LexLeanRuntime.Sliceable.slice.ByteArray(+value: Lean.ByteArray, +start: Nat, +count: Nat) -> Maybe<&2, Lean.ByteArray>:
  Bool.pick(Maybe<&2, Lean.ByteArray>, L.Lean.Nat.ble(L.Lean.Nat.add(start, count), Lean.ByteArray.size(value)), Some{Lean.ByteArray.extract(value, start, L.Lean.Nat.add(start, count))}, None{})

def LexLeanRuntime.slice.List(-A: Data, value: List<&2, A>, start: Nat, count: Nat) -> Maybe<&2, List<&2, A>>:
  LexLeanRuntime.Sliceable.slice.List(A, value, start, count)

def LexLeanRuntime.slice.ByteArray(value: Lean.ByteArray, start: Nat, count: Nat) -> Maybe<&2, Lean.ByteArray>:
  LexLeanRuntime.Sliceable.slice.ByteArray(value, start, count)

# ---------------------------------------------------------------------------
# UTF-8, byte comparison, equality, splitting and joining.
# ---------------------------------------------------------------------------

# String.utf8EncodeChar on the code point v.
def LexLeanRuntime.Utf8.encodeChar(+v: U32) -> List<&2, Lean.UInt8>:
  Bool.pick(List<&2, Lean.UInt8>, U32.is_le(v, 127), [Lean.UInt8.lit(v)], Bool.pick(List<&2, Lean.UInt8>, U32.is_le(v, 2047), [Lean.UInt8.lit(U32.or(U32.and(U32.shrn(v, 6n), 31), 192)), Lean.UInt8.lit(U32.or(U32.and(v, 63), 128))], Bool.pick(List<&2, Lean.UInt8>, U32.is_le(v, 65535), [Lean.UInt8.lit(U32.or(U32.and(U32.shrn(v, 12n), 15), 224)), Lean.UInt8.lit(U32.or(U32.and(U32.shrn(v, 6n), 63), 128)), Lean.UInt8.lit(U32.or(U32.and(v, 63), 128))], [Lean.UInt8.lit(U32.or(U32.and(U32.shrn(v, 18n), 7), 240)), Lean.UInt8.lit(U32.or(U32.and(U32.shrn(v, 12n), 63), 128)), Lean.UInt8.lit(U32.or(U32.and(U32.shrn(v, 6n), 63), 128)), Lean.UInt8.lit(U32.or(U32.and(v, 63), 128))])))

def LexLeanRuntime.Utf8.encode(s: String) -> List<&2, Lean.UInt8>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      L.Lean.List.append(Lean.UInt8, LexLeanRuntime.Utf8.encodeChar(Char.to_u32(c)), LexLeanRuntime.Utf8.encode(t))

# A decoder step: a malformed byte, a sequence still needing `need` bytes with
# the next one in [lo, hi], or a finished code point.
type LexLeanRuntime.Utf8.Step is Data:
  LexLeanRuntime.Utf8.Step.err{}
  LexLeanRuntime.Utf8.Step.more{need: Nat, lo: U32, hi: U32, acc: U32}
  LexLeanRuntime.Utf8.Step.emit{code: U32}

# The well-formed UTF-8 byte sequences (Unicode Table 3-7): no overlong form,
# no surrogate, nothing above U+10FFFF.
def LexLeanRuntime.Utf8.lead(+v: U32) -> LexLeanRuntime.Utf8.Step:
  Bool.pick(LexLeanRuntime.Utf8.Step, U32.is_lt(v, 128), LexLeanRuntime.Utf8.Step.emit{v}, Bool.pick(LexLeanRuntime.Utf8.Step, U32.is_lt(v, 194), LexLeanRuntime.Utf8.Step.err{}, Bool.pick(LexLeanRuntime.Utf8.Step, U32.is_lt(v, 224), LexLeanRuntime.Utf8.Step.more{1n, 128, 191, U32.and(v, 31)}, Bool.pick(LexLeanRuntime.Utf8.Step, U32.is_eq(v, 224), LexLeanRuntime.Utf8.Step.more{2n, 160, 191, 0}, Bool.pick(LexLeanRuntime.Utf8.Step, U32.is_lt(v, 237), LexLeanRuntime.Utf8.Step.more{2n, 128, 191, U32.and(v, 15)}, Bool.pick(LexLeanRuntime.Utf8.Step, U32.is_eq(v, 237), LexLeanRuntime.Utf8.Step.more{2n, 128, 159, 13}, Bool.pick(LexLeanRuntime.Utf8.Step, U32.is_lt(v, 240), LexLeanRuntime.Utf8.Step.more{2n, 128, 191, U32.and(v, 15)}, Bool.pick(LexLeanRuntime.Utf8.Step, U32.is_eq(v, 240), LexLeanRuntime.Utf8.Step.more{3n, 144, 191, 0}, Bool.pick(LexLeanRuntime.Utf8.Step, U32.is_lt(v, 244), LexLeanRuntime.Utf8.Step.more{3n, 128, 191, U32.and(v, 7)}, Bool.pick(LexLeanRuntime.Utf8.Step, U32.is_eq(v, 244), LexLeanRuntime.Utf8.Step.more{3n, 128, 143, 4}, LexLeanRuntime.Utf8.Step.err{}))))))))))

def LexLeanRuntime.Utf8.cont(+p: Nat, +lo: U32, +hi: U32, acc: U32, +v: U32) -> LexLeanRuntime.Utf8.Step:
  +a = U32.or(U32.shln(acc, 6n), U32.and(v, 63))
  Bool.pick(LexLeanRuntime.Utf8.Step, L.Lean.Bool.and(U32.is_le(lo, v), U32.is_le(v, hi)), Bool.pick(LexLeanRuntime.Utf8.Step, L.Lean.Nat.beq(p, 0n), LexLeanRuntime.Utf8.Step.emit{a}, LexLeanRuntime.Utf8.Step.more{p, 128, 191, a}), LexLeanRuntime.Utf8.Step.err{})

def LexLeanRuntime.Utf8.next(st: LexLeanRuntime.Utf8.Step, v: U32) -> LexLeanRuntime.Utf8.Step:
  match st:
    case LexLeanRuntime.Utf8.Step.err{}:
      LexLeanRuntime.Utf8.Step.err{}
    case LexLeanRuntime.Utf8.Step.emit{c}:
      LexLeanRuntime.Utf8.lead(v)
    case LexLeanRuntime.Utf8.Step.more{need, lo, hi, acc}:
      match need:
        case 0n:
          LexLeanRuntime.Utf8.lead(v)
        case 1n+p:
          LexLeanRuntime.Utf8.cont(p, lo, hi, acc, v)

def LexLeanRuntime.Utf8.after(st: LexLeanRuntime.Utf8.Step) -> LexLeanRuntime.Utf8.Step:
  match st:
    case LexLeanRuntime.Utf8.Step.err{}:
      LexLeanRuntime.Utf8.Step.err{}
    case LexLeanRuntime.Utf8.Step.emit{c}:
      LexLeanRuntime.Utf8.Step.more{0n, 0, 0, 0}
    case LexLeanRuntime.Utf8.Step.more{need, lo, hi, acc}:
      LexLeanRuntime.Utf8.Step.more{need, lo, hi, acc}

def LexLeanRuntime.Utf8.cons(c: U32, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match r:
    case None{}:
      None{}
    case Some{s}:
      Some{SCon{Chr{c}, s}}

def LexLeanRuntime.Utf8.fin(st: LexLeanRuntime.Utf8.Step, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match st:
    case LexLeanRuntime.Utf8.Step.err{}:
      None{}
    case LexLeanRuntime.Utf8.Step.emit{c}:
      LexLeanRuntime.Utf8.cons(c, r)
    case LexLeanRuntime.Utf8.Step.more{need, lo, hi, acc}:
      r

def LexLeanRuntime.Utf8.done(st: LexLeanRuntime.Utf8.Step) -> Maybe<&2, String>:
  match st:
    case LexLeanRuntime.Utf8.Step.err{}:
      None{}
    case LexLeanRuntime.Utf8.Step.emit{c}:
      Some{SNil{}}
    case LexLeanRuntime.Utf8.Step.more{need, lo, hi, acc}:
      Bool.pick(Maybe<&2, String>, L.Lean.Nat.beq(need, 0n), Some{SNil{}}, None{})

def LexLeanRuntime.Utf8.decode(bytes: List<&2, Lean.UInt8>, st: LexLeanRuntime.Utf8.Step) -> Maybe<&2, String>:
  match bytes:
    case Nil{}:
      LexLeanRuntime.Utf8.done(st)
    case Con{b, t}:
      +s2 = LexLeanRuntime.Utf8.next(st, Lean.UInt8.toUInt32(b))
      LexLeanRuntime.Utf8.fin(s2, LexLeanRuntime.Utf8.decode(t, LexLeanRuntime.Utf8.after(s2)))

def LexLeanRuntime.utf8Encode(value: String) -> Lean.ByteArray:
  Lean.ByteArray.mk{LexLeanRuntime.Utf8.encode(value)}

# String.fromUTF8? value: the decoded string when the bytes are well-formed UTF-8.
def LexLeanRuntime.utf8Decode(value: Lean.ByteArray) -> Maybe<&2, String>:
  LexLeanRuntime.Utf8.decode(Lean.ByteArray.data(value), LexLeanRuntime.Utf8.Step.more{0n, 0, 0, 0})

def LexLeanRuntime.compareBytes.lex(c: Cmp, rest: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      rest
    case GT{}:
      GT{}

def LexLeanRuntime.compareBytes.go(left: List<&2, Lean.UInt8>, right: List<&2, Lean.UInt8>) -> Cmp:
  match left right:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{rh, rt}:
      LT{}
    case Con{lh, lt} Nil{}:
      GT{}
    case Con{lh, lt} Con{rh, rt}:
      LexLeanRuntime.compareBytes.lex(Lean.UInt8.cmp(lh, rh), LexLeanRuntime.compareBytes.go(lt, rt))

# compare left.toList right.toList: lexicographic, a proper prefix first.
def LexLeanRuntime.compareBytes(left: Lean.ByteArray, right: Lean.ByteArray) -> Cmp:
  LexLeanRuntime.compareBytes.go(Lean.ByteArray.data(left), Lean.ByteArray.data(right))

def LexLeanRuntime.equal.Nat(left: Nat, right: Nat) -> Bool:
  L.Lean.Nat.beq(left, right)

def LexLeanRuntime.equal.Int(left: L.Lean.Int, right: L.Lean.Int) -> Bool:
  Lean.Int.beq(left, right)

def LexLeanRuntime.equal.Bool(left: Bool, right: Bool) -> Bool:
  Lean.Bool.beq(left, right)

def LexLeanRuntime.equal.Char(left: Char, right: Char) -> Bool:
  Lean.Char.beq(left, right)

def LexLeanRuntime.equal.String(left: String, right: String) -> Bool:
  Lean.String.beq(left, right)

def LexLeanRuntime.equal.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Bool:
  Lean.UInt8.beq(left, right)

def LexLeanRuntime.equal.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Bool:
  Lean.UInt16.beq(left, right)

def LexLeanRuntime.equal.UInt32(left: U32, right: U32) -> Bool:
  Lean.UInt32.beq(left, right)

def LexLeanRuntime.equal.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Bool:
  Lean.UInt64.beq(left, right)

def LexLeanRuntime.equal.Int8(left: Lean.Int8, right: Lean.Int8) -> Bool:
  Lean.Int8.beq(left, right)

def LexLeanRuntime.equal.Int16(left: Lean.Int16, right: Lean.Int16) -> Bool:
  Lean.Int16.beq(left, right)

def LexLeanRuntime.equal.Int32(left: Lean.Int32, right: Lean.Int32) -> Bool:
  Lean.Int32.beq(left, right)

def LexLeanRuntime.equal.Int64(left: Lean.Int64, right: Lean.Int64) -> Bool:
  Lean.Int64.beq(left, right)

def LexLeanRuntime.equal.ByteArray(left: Lean.ByteArray, right: Lean.ByteArray) -> Bool:
  Lean.ByteArray.beq(left, right)

# Lean's Ordering derives its equality: two orderings are equal exactly when
# they are the same constructor.
def LexLeanRuntime.equal.Ordering(left: Cmp, right: Cmp) -> Bool:
  match left:
    case LT{}:
      Cmp.is_lt(right)
    case EQ{}:
      Cmp.is_eq(right)
    case GT{}:
      Cmp.is_gt(right)

# String.splitOn s sep for a non-empty sep: the leftmost non-overlapping
# occurrences of sep cut s; `skip` counts the separator characters still to
# pass, `cur` is the current field reversed and `acc` the fields reversed.
def Lean.String.splitOn.go(s: String, +sep: String, +skip: Nat, +cur: String, +acc: List<&2, String>) -> List<&2, String>:
  match s:
    case SNil{}:
      List.reverse(&2, String, Con{String.reverse(cur), acc})
    case SCon{+c, +t}:
      +sk = Bool.not(L.Lean.Nat.beq(skip, 0n))
      +cut = L.Lean.Bool.and(Bool.not(sk), Lean.String.isPrefixOf(sep, SCon{c, t}))
      Lean.String.splitOn.go(t, sep, Bool.pick(Nat, sk, L.Lean.Nat.pred(skip), Bool.pick(Nat, cut, L.Lean.Nat.pred(Lean.String.length(sep)), 0n)), Bool.pick(String, sk, cur, Bool.pick(String, cut, SNil{}, SCon{c, cur})), Bool.pick(List<&2, String>, cut, Con{String.reverse(cur), acc}, acc))

# String.splitOn s sep: [s] when sep is empty.
def Lean.String.splitOn(+s: String, +sep: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, Lean.String.isEmpty(sep), [s], Lean.String.splitOn.go(s, sep, 0n, SNil{}, Nil{}))

# let fields := value.splitOn delimiter
# if delimiter.isEmpty || maximum.toNat < fields.length then none else some fields
def LexLeanRuntime.splitExact(value: String, +delimiter: String, maximum: U32) -> Maybe<&2, List<&2, String>>:
  +fields = Lean.String.splitOn(value, delimiter)
  LexLeanRuntime.Maybe.unless(List<&2, String>, L.Lean.Bool.or(Lean.String.isEmpty(delimiter), LexLeanRuntime.U32.toNatLt(L.Lean.List.length(String, fields), maximum)), fields)

def Lean.String.intercalate.go(xs: List<&2, String>, +s: String, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{a, rest}:
      Lean.String.intercalate.go(rest, s, String.append(String.append(acc, s), a))

def Lean.String.intercalate(s: String, xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{a, rest}:
      Lean.String.intercalate.go(rest, s, a)

def LexLeanRuntime.join(values: List<&2, String>, delimiter: String) -> String:
  Lean.String.intercalate(delimiter, values)

# ---------------------------------------------------------------------------
# Decimal: parse accepts exactly the canonical decimal spelling (Lean's parse
# is toInt? followed by `toString parsed = value`, which holds exactly for the
# canonical spelling: digits, no leading zero, an optional '-' before a
# non-zero value); format is toString.
# ---------------------------------------------------------------------------

def LexLeanRuntime.Decimal.inRange(+v: U32) -> Bool:
  L.Lean.Bool.and(U32.is_le(48, v), U32.is_le(v, 57))

def LexLeanRuntime.Decimal.isDigit(c: Char) -> Bool:
  LexLeanRuntime.Decimal.inRange(Char.to_u32(c))

def LexLeanRuntime.Decimal.allDigits(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, t}:
      L.Lean.Bool.and(LexLeanRuntime.Decimal.isDigit(h), LexLeanRuntime.Decimal.allDigits(t))

# A non-empty digit string with no leading zero; `zero` also admits "0".
def LexLeanRuntime.Decimal.natural(zero: Bool, s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+h, +t}:
      Bool.pick(Bool, U32.is_eq(Char.to_u32(h), 48), L.Lean.Bool.and(zero, Lean.String.isEmpty(t)), L.Lean.Bool.and(LexLeanRuntime.Decimal.isDigit(h), LexLeanRuntime.Decimal.allDigits(t)))

def LexLeanRuntime.Decimal.isMinus(c: Char) -> Bool:
  U32.is_eq(Char.to_u32(c), 45)

def LexLeanRuntime.Decimal.canonical(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+h, +t}:
      Bool.pick(Bool, LexLeanRuntime.Decimal.isMinus(h), LexLeanRuntime.Decimal.natural(False{}, t), LexLeanRuntime.Decimal.natural(True{}, SCon{h, t}))

def LexLeanRuntime.Decimal.digit(c: Char) -> Nat:
  U32.to_nat(U32.sub(Char.to_u32(c), 48))

def LexLeanRuntime.Decimal.toNat(s: String, acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      LexLeanRuntime.Decimal.toNat(t, L.Lean.Nat.add(L.Lean.Nat.mul(acc, 10n), LexLeanRuntime.Decimal.digit(h)))

def LexLeanRuntime.Decimal.toInt(s: String) -> L.Lean.Int:
  match s:
    case SNil{}:
      L.ofNat{0n}
    case SCon{+h, +t}:
      Bool.pick(L.Lean.Int, LexLeanRuntime.Decimal.isMinus(h), L.Lean.Int.negOfNat(LexLeanRuntime.Decimal.toNat(t, 0n)), L.ofNat{LexLeanRuntime.Decimal.toNat(SCon{h, t}, 0n)})

def LexLeanRuntime.Decimal.bits(c: Char) -> Word(32n):
  Lean.UInt32.bits(U32.sub(Char.to_u32(c), 48))

# The digits of s accumulated in n bits; the flag records a value past 2^(n-4),
# which no fixed-width range reaches.
def LexLeanRuntime.Decimal.toWord.step(+n: Nat, ov: Bool, +acc: Word(n), c: Char) -> Bool & Word(n):
  (L.Lean.Bool.or(ov, Bool.not(LexLeanRuntime.W.highSame(L.Lean.Nat.sub(n, 4n), n, False{}, acc))), Word.add(n, Word.mul(n, acc, LexLeanRuntime.Nat.toWord(n, 10n)), LexLeanRuntime.W.resize(n, 32n, False{}, LexLeanRuntime.Decimal.bits(c))))

def LexLeanRuntime.Decimal.toWord(+n: Nat, s: String, st: Bool & Word(n)) -> Bool & Word(n):
  match s:
    case SNil{}:
      st
    case SCon{h, t}:
      (ov, acc) = st
      LexLeanRuntime.Decimal.toWord(n, t, LexLeanRuntime.Decimal.toWord.step(n, ov, acc, h))

def LexLeanRuntime.Decimal.negate(+n: Nat, st: Bool & Word(n)) -> Bool & Word(n):
  (ov, acc) = st
  (ov, LexLeanRuntime.W.neg(n, acc))

def LexLeanRuntime.Decimal.signed.fin(+n: Nat, minus: Bool, h: Char, t: String) -> Bool & Word(n):
  match minus:
    case True{}:
      LexLeanRuntime.Decimal.negate(n, LexLeanRuntime.Decimal.toWord(n, t, (False{}, Word.zero(n))))
    case False{}:
      LexLeanRuntime.Decimal.toWord(n, SCon{h, t}, (False{}, Word.zero(n)))

def LexLeanRuntime.Decimal.signed(+n: Nat, s: String) -> Bool & Word(n):
  match s:
    case SNil{}:
      (False{}, Word.zero(n))
    case SCon{+h, +t}:
      LexLeanRuntime.Decimal.signed.fin(n, LexLeanRuntime.Decimal.isMinus(h), h, t)

def LexLeanRuntime.Decimal.digits.fin(+n: Nat, z: Bool, acc: String, more: String) -> String:
  match z:
    case True{}:
      acc
    case False{}:
      more

# The decimal digits of the unsigned n-bit word w, prepended to acc.
def LexLeanRuntime.Decimal.digits(fuel: Nat, +n: Nat, +w: Word(n), +acc: String) -> String:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      +qr = LexLeanRuntime.W.udivmod(n, w, n, LexLeanRuntime.Nat.toWord(n, 10n))
      +q = LexLeanRuntime.W.quo(n, qr)
      +acc2 = {SCon{Chr{U32.add(U32{LexLeanRuntime.W.resize(32n, n, False{}, LexLeanRuntime.W.rem(n, qr))}, 48)}, acc} : String}
      LexLeanRuntime.Decimal.digits.fin(n, LexLeanRuntime.W.isZero(n, q), acc2, LexLeanRuntime.Decimal.digits(f, n, q, acc2))

def LexLeanRuntime.Decimal.parse.Int(+value: String) -> Maybe<&2, L.Lean.Int>:
  LexLeanRuntime.Maybe.unless(L.Lean.Int, Bool.not(LexLeanRuntime.Decimal.canonical(value)), LexLeanRuntime.Decimal.toInt(value))

def LexLeanRuntime.Decimal.format.Int(value: L.Lean.Int) -> String:
  Lean.Int.repr(value)

def LexLeanRuntime.parseDecimal.Int(value: String) -> Maybe<&2, L.Lean.Int>:
  LexLeanRuntime.Decimal.parse.Int(value)

def LexLeanRuntime.formatDecimal.Int(value: L.Lean.Int) -> String:
  LexLeanRuntime.Decimal.format.Int(value)

def LexLeanRuntime.Decimal.parse.fin.UInt8(st: Bool & Word(18n)) -> Maybe<&2, Lean.UInt8>:
  (ov, v) = st
  Bool.pick(Maybe<&2, Lean.UInt8>, ov, None{}, LexLeanRuntime.Fixed.narrow.UInt8(18n, v))

def LexLeanRuntime.Decimal.parse.UInt8(+value: String) -> Maybe<&2, Lean.UInt8>:
  Bool.pick(Maybe<&2, Lean.UInt8>, LexLeanRuntime.Decimal.canonical(value), LexLeanRuntime.Decimal.parse.fin.UInt8(LexLeanRuntime.Decimal.signed(18n, value)), None{})

def LexLeanRuntime.Decimal.format.UInt8(value: Lean.UInt8) -> String:
  LexLeanRuntime.Decimal.digits(8n, 8n, Lean.UInt8.bits(value), SNil{})

def LexLeanRuntime.parseDecimal.UInt8(value: String) -> Maybe<&2, Lean.UInt8>:
  LexLeanRuntime.Decimal.parse.UInt8(value)

def LexLeanRuntime.formatDecimal.UInt8(value: Lean.UInt8) -> String:
  LexLeanRuntime.Decimal.format.UInt8(value)

def LexLeanRuntime.Decimal.parse.fin.UInt16(st: Bool & Word(34n)) -> Maybe<&2, Lean.UInt16>:
  (ov, v) = st
  Bool.pick(Maybe<&2, Lean.UInt16>, ov, None{}, LexLeanRuntime.Fixed.narrow.UInt16(34n, v))

def LexLeanRuntime.Decimal.parse.UInt16(+value: String) -> Maybe<&2, Lean.UInt16>:
  Bool.pick(Maybe<&2, Lean.UInt16>, LexLeanRuntime.Decimal.canonical(value), LexLeanRuntime.Decimal.parse.fin.UInt16(LexLeanRuntime.Decimal.signed(34n, value)), None{})

def LexLeanRuntime.Decimal.format.UInt16(value: Lean.UInt16) -> String:
  LexLeanRuntime.Decimal.digits(16n, 16n, Lean.UInt16.bits(value), SNil{})

def LexLeanRuntime.parseDecimal.UInt16(value: String) -> Maybe<&2, Lean.UInt16>:
  LexLeanRuntime.Decimal.parse.UInt16(value)

def LexLeanRuntime.formatDecimal.UInt16(value: Lean.UInt16) -> String:
  LexLeanRuntime.Decimal.format.UInt16(value)

def LexLeanRuntime.Decimal.parse.fin.UInt32(st: Bool & Word(66n)) -> Maybe<&2, U32>:
  (ov, v) = st
  Bool.pick(Maybe<&2, U32>, ov, None{}, LexLeanRuntime.Fixed.narrow.UInt32(66n, v))

def LexLeanRuntime.Decimal.parse.UInt32(+value: String) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, LexLeanRuntime.Decimal.canonical(value), LexLeanRuntime.Decimal.parse.fin.UInt32(LexLeanRuntime.Decimal.signed(66n, value)), None{})

def LexLeanRuntime.Decimal.format.UInt32(value: U32) -> String:
  LexLeanRuntime.Decimal.digits(32n, 32n, Lean.UInt32.bits(value), SNil{})

def LexLeanRuntime.parseDecimal.UInt32(value: String) -> Maybe<&2, U32>:
  LexLeanRuntime.Decimal.parse.UInt32(value)

def LexLeanRuntime.formatDecimal.UInt32(value: U32) -> String:
  LexLeanRuntime.Decimal.format.UInt32(value)

def LexLeanRuntime.Decimal.parse.fin.UInt64(st: Bool & Word(130n)) -> Maybe<&2, Lean.UInt64>:
  (ov, v) = st
  Bool.pick(Maybe<&2, Lean.UInt64>, ov, None{}, LexLeanRuntime.Fixed.narrow.UInt64(130n, v))

def LexLeanRuntime.Decimal.parse.UInt64(+value: String) -> Maybe<&2, Lean.UInt64>:
  Bool.pick(Maybe<&2, Lean.UInt64>, LexLeanRuntime.Decimal.canonical(value), LexLeanRuntime.Decimal.parse.fin.UInt64(LexLeanRuntime.Decimal.signed(130n, value)), None{})

def LexLeanRuntime.Decimal.format.UInt64(value: Lean.UInt64) -> String:
  LexLeanRuntime.Decimal.digits(64n, 64n, Lean.UInt64.bits(value), SNil{})

def LexLeanRuntime.parseDecimal.UInt64(value: String) -> Maybe<&2, Lean.UInt64>:
  LexLeanRuntime.Decimal.parse.UInt64(value)

def LexLeanRuntime.formatDecimal.UInt64(value: Lean.UInt64) -> String:
  LexLeanRuntime.Decimal.format.UInt64(value)

def LexLeanRuntime.Decimal.parse.fin.Int8(st: Bool & Word(18n)) -> Maybe<&2, Lean.Int8>:
  (ov, v) = st
  Bool.pick(Maybe<&2, Lean.Int8>, ov, None{}, LexLeanRuntime.Fixed.narrow.Int8(18n, v))

def LexLeanRuntime.Decimal.parse.Int8(+value: String) -> Maybe<&2, Lean.Int8>:
  Bool.pick(Maybe<&2, Lean.Int8>, LexLeanRuntime.Decimal.canonical(value), LexLeanRuntime.Decimal.parse.fin.Int8(LexLeanRuntime.Decimal.signed(18n, value)), None{})

def LexLeanRuntime.Decimal.format.fin.Int8(s: Bool, b: Word(8n)) -> String:
  match s:
    case True{}:
      SCon{'-', LexLeanRuntime.Decimal.digits(8n, 8n, LexLeanRuntime.W.neg(8n, b), SNil{})}
    case False{}:
      LexLeanRuntime.Decimal.digits(8n, 8n, b, SNil{})

def LexLeanRuntime.Decimal.format.Int8(value: Lean.Int8) -> String:
  +b = Lean.Int8.bits(value)
  LexLeanRuntime.Decimal.format.fin.Int8(LexLeanRuntime.W.msb(8n, b), b)

def LexLeanRuntime.parseDecimal.Int8(value: String) -> Maybe<&2, Lean.Int8>:
  LexLeanRuntime.Decimal.parse.Int8(value)

def LexLeanRuntime.formatDecimal.Int8(value: Lean.Int8) -> String:
  LexLeanRuntime.Decimal.format.Int8(value)

def LexLeanRuntime.Decimal.parse.fin.Int16(st: Bool & Word(34n)) -> Maybe<&2, Lean.Int16>:
  (ov, v) = st
  Bool.pick(Maybe<&2, Lean.Int16>, ov, None{}, LexLeanRuntime.Fixed.narrow.Int16(34n, v))

def LexLeanRuntime.Decimal.parse.Int16(+value: String) -> Maybe<&2, Lean.Int16>:
  Bool.pick(Maybe<&2, Lean.Int16>, LexLeanRuntime.Decimal.canonical(value), LexLeanRuntime.Decimal.parse.fin.Int16(LexLeanRuntime.Decimal.signed(34n, value)), None{})

def LexLeanRuntime.Decimal.format.fin.Int16(s: Bool, b: Word(16n)) -> String:
  match s:
    case True{}:
      SCon{'-', LexLeanRuntime.Decimal.digits(16n, 16n, LexLeanRuntime.W.neg(16n, b), SNil{})}
    case False{}:
      LexLeanRuntime.Decimal.digits(16n, 16n, b, SNil{})

def LexLeanRuntime.Decimal.format.Int16(value: Lean.Int16) -> String:
  +b = Lean.Int16.bits(value)
  LexLeanRuntime.Decimal.format.fin.Int16(LexLeanRuntime.W.msb(16n, b), b)

def LexLeanRuntime.parseDecimal.Int16(value: String) -> Maybe<&2, Lean.Int16>:
  LexLeanRuntime.Decimal.parse.Int16(value)

def LexLeanRuntime.formatDecimal.Int16(value: Lean.Int16) -> String:
  LexLeanRuntime.Decimal.format.Int16(value)

def LexLeanRuntime.Decimal.parse.fin.Int32(st: Bool & Word(66n)) -> Maybe<&2, Lean.Int32>:
  (ov, v) = st
  Bool.pick(Maybe<&2, Lean.Int32>, ov, None{}, LexLeanRuntime.Fixed.narrow.Int32(66n, v))

def LexLeanRuntime.Decimal.parse.Int32(+value: String) -> Maybe<&2, Lean.Int32>:
  Bool.pick(Maybe<&2, Lean.Int32>, LexLeanRuntime.Decimal.canonical(value), LexLeanRuntime.Decimal.parse.fin.Int32(LexLeanRuntime.Decimal.signed(66n, value)), None{})

def LexLeanRuntime.Decimal.format.fin.Int32(s: Bool, b: Word(32n)) -> String:
  match s:
    case True{}:
      SCon{'-', LexLeanRuntime.Decimal.digits(32n, 32n, LexLeanRuntime.W.neg(32n, b), SNil{})}
    case False{}:
      LexLeanRuntime.Decimal.digits(32n, 32n, b, SNil{})

def LexLeanRuntime.Decimal.format.Int32(value: Lean.Int32) -> String:
  +b = Lean.Int32.bits(value)
  LexLeanRuntime.Decimal.format.fin.Int32(LexLeanRuntime.W.msb(32n, b), b)

def LexLeanRuntime.parseDecimal.Int32(value: String) -> Maybe<&2, Lean.Int32>:
  LexLeanRuntime.Decimal.parse.Int32(value)

def LexLeanRuntime.formatDecimal.Int32(value: Lean.Int32) -> String:
  LexLeanRuntime.Decimal.format.Int32(value)

def LexLeanRuntime.Decimal.parse.fin.Int64(st: Bool & Word(130n)) -> Maybe<&2, Lean.Int64>:
  (ov, v) = st
  Bool.pick(Maybe<&2, Lean.Int64>, ov, None{}, LexLeanRuntime.Fixed.narrow.Int64(130n, v))

def LexLeanRuntime.Decimal.parse.Int64(+value: String) -> Maybe<&2, Lean.Int64>:
  Bool.pick(Maybe<&2, Lean.Int64>, LexLeanRuntime.Decimal.canonical(value), LexLeanRuntime.Decimal.parse.fin.Int64(LexLeanRuntime.Decimal.signed(130n, value)), None{})

def LexLeanRuntime.Decimal.format.fin.Int64(s: Bool, b: Word(64n)) -> String:
  match s:
    case True{}:
      SCon{'-', LexLeanRuntime.Decimal.digits(64n, 64n, LexLeanRuntime.W.neg(64n, b), SNil{})}
    case False{}:
      LexLeanRuntime.Decimal.digits(64n, 64n, b, SNil{})

def LexLeanRuntime.Decimal.format.Int64(value: Lean.Int64) -> String:
  +b = Lean.Int64.bits(value)
  LexLeanRuntime.Decimal.format.fin.Int64(LexLeanRuntime.W.msb(64n, b), b)

def LexLeanRuntime.parseDecimal.Int64(value: String) -> Maybe<&2, Lean.Int64>:
  LexLeanRuntime.Decimal.parse.Int64(value)

def LexLeanRuntime.formatDecimal.Int64(value: Lean.Int64) -> String:
  LexLeanRuntime.Decimal.format.Int64(value)

# ---------------------------------------------------------------------------
# LexLeanCollections: the Key universe and its comparison.
# ---------------------------------------------------------------------------

def LexLeanCollections.compareCodes.lex(c: Cmp, rest: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      rest
    case GT{}:
      GT{}

# compareCodes on the character lists of two strings: by code point, a proper
# prefix first.
def LexLeanCollections.compareCodes(left: String, right: String) -> Cmp:
  match left right:
    case SNil{} SNil{}:
      EQ{}
    case SNil{} SCon{r, rights}:
      LT{}
    case SCon{l, lefts} SNil{}:
      GT{}
    case SCon{l, lefts} SCon{r, rights}:
      LexLeanCollections.compareCodes.lex(U32.cmp(Char.to_u32(l), Char.to_u32(r)), LexLeanCollections.compareCodes(lefts, rights))

type LexLeanCollections.Key is Data:
  LexLeanCollections.Key.Nat{}
  LexLeanCollections.Key.Int{}
  LexLeanCollections.Key.Bool{}
  LexLeanCollections.Key.Int8{}
  LexLeanCollections.Key.Int16{}
  LexLeanCollections.Key.Int32{}
  LexLeanCollections.Key.Int64{}
  LexLeanCollections.Key.UInt8{}
  LexLeanCollections.Key.UInt16{}
  LexLeanCollections.Key.UInt32{}
  LexLeanCollections.Key.UInt64{}
  LexLeanCollections.Key.String{}
  LexLeanCollections.Key.Prod{fst: LexLeanCollections.Key, snd: LexLeanCollections.Key}

def LexLeanCollections.Key.carrier(k: LexLeanCollections.Key) -> Data:
  match k:
    case LexLeanCollections.Key.Nat{}:
      Nat
    case LexLeanCollections.Key.Int{}:
      L.Lean.Int
    case LexLeanCollections.Key.Bool{}:
      Bool
    case LexLeanCollections.Key.Int8{}:
      Lean.Int8
    case LexLeanCollections.Key.Int16{}:
      Lean.Int16
    case LexLeanCollections.Key.Int32{}:
      Lean.Int32
    case LexLeanCollections.Key.Int64{}:
      Lean.Int64
    case LexLeanCollections.Key.UInt8{}:
      Lean.UInt8
    case LexLeanCollections.Key.UInt16{}:
      Lean.UInt16
    case LexLeanCollections.Key.UInt32{}:
      U32
    case LexLeanCollections.Key.UInt64{}:
      Lean.UInt64
    case LexLeanCollections.Key.String{}:
      String
    case LexLeanCollections.Key.Prod{a, b}:
      L.Lean.Prod(LexLeanCollections.Key.carrier(a), LexLeanCollections.Key.carrier(b))

def LexLeanCollections.Key.compare(+k: LexLeanCollections.Key, x: LexLeanCollections.Key.carrier(k), y: LexLeanCollections.Key.carrier(k)) -> Cmp:
  match k:
    case LexLeanCollections.Key.Nat{}:
      Nat.cmp(x, y)
    case LexLeanCollections.Key.Int{}:
      Lean.Int.cmp(x, y)
    case LexLeanCollections.Key.Bool{}:
      Bool.cmp(x, y)
    case LexLeanCollections.Key.Int8{}:
      Lean.Int8.cmp(x, y)
    case LexLeanCollections.Key.Int16{}:
      Lean.Int16.cmp(x, y)
    case LexLeanCollections.Key.Int32{}:
      Lean.Int32.cmp(x, y)
    case LexLeanCollections.Key.Int64{}:
      Lean.Int64.cmp(x, y)
    case LexLeanCollections.Key.UInt8{}:
      Lean.UInt8.cmp(x, y)
    case LexLeanCollections.Key.UInt16{}:
      Lean.UInt16.cmp(x, y)
    case LexLeanCollections.Key.UInt32{}:
      Lean.UInt32.cmp(x, y)
    case LexLeanCollections.Key.UInt64{}:
      Lean.UInt64.cmp(x, y)
    case LexLeanCollections.Key.String{}:
      LexLeanCollections.compareCodes(x, y)
    case LexLeanCollections.Key.Prod{+a, +b}:
      match x y:
        case Tuple{x1, x2} Tuple{y1, y2}:
          LexLeanCollections.compareCodes.lex(LexLeanCollections.Key.compare(a, x1, y1), LexLeanCollections.Key.compare(b, x2, y2))

def LexLeanCollections.Key.compare.Nat(left: Nat, right: Nat) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.Nat{}, left, right)

def LexLeanCollections.Key.compare.Int(left: L.Lean.Int, right: L.Lean.Int) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.Int{}, left, right)

def LexLeanCollections.Key.compare.Bool(left: Bool, right: Bool) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.Bool{}, left, right)

def LexLeanCollections.Key.compare.Int8(left: Lean.Int8, right: Lean.Int8) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.Int8{}, left, right)

def LexLeanCollections.Key.compare.Int16(left: Lean.Int16, right: Lean.Int16) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.Int16{}, left, right)

def LexLeanCollections.Key.compare.Int32(left: Lean.Int32, right: Lean.Int32) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.Int32{}, left, right)

def LexLeanCollections.Key.compare.Int64(left: Lean.Int64, right: Lean.Int64) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.Int64{}, left, right)

def LexLeanCollections.Key.compare.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.UInt8{}, left, right)

def LexLeanCollections.Key.compare.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.UInt16{}, left, right)

def LexLeanCollections.Key.compare.UInt32(left: U32, right: U32) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.UInt32{}, left, right)

def LexLeanCollections.Key.compare.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.UInt64{}, left, right)

def LexLeanCollections.Key.compare.String(left: String, right: String) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.String{}, left, right)

def LexLeanCollections.Key.compare.Prod(+ka: LexLeanCollections.Key, +kb: LexLeanCollections.Key, left: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), right: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))) -> Cmp:
  LexLeanCollections.Key.compare(LexLeanCollections.Key.Prod{ka, kb}, left, right)

# Key-free collection functions: generic in the element types.
def LexLeanCollections.mapSize(-K: Data, -V: Data, map: List<&2, L.Lean.Prod(K, V)>) -> Nat:
  L.Lean.List.length(L.Lean.Prod(K, V), map)

def LexLeanCollections.mapKeys(-K: Data, -V: Data, map: List<&2, L.Lean.Prod(K, V)>) -> List<&2, K>:
  match map:
    case Nil{}:
      Nil{}
    case Con{e, rest}:
      Con{Lean.Prod.fst(K, V, e), LexLeanCollections.mapKeys(K, V, rest)}

def LexLeanCollections.mapValues(-K: Data, -V: Data, map: List<&2, L.Lean.Prod(K, V)>) -> List<&2, V>:
  match map:
    case Nil{}:
      Nil{}
    case Con{e, rest}:
      Con{Lean.Prod.snd(K, V, e), LexLeanCollections.mapValues(K, V, rest)}

def LexLeanCollections.mapEntries(-K: Data, -V: Data, map: List<&2, L.Lean.Prod(K, V)>) -> List<&2, L.Lean.Prod(K, V)>:
  map

def LexLeanCollections.setSize(-K: Data, set: List<&2, K>) -> Nat:
  L.Lean.List.length(K, set)

def LexLeanCollections.setElements(-K: Data, set: List<&2, K>) -> List<&2, K>:
  set

# ---------------------------------------------------------------------------
# LexLeanCollections functions. `<f>.Key` takes the Key code; `<f>.<Instance>`
# is the monomorphized instance (`<f>.Prod` takes the codes of both components).
# The Lean `match Key.compare key other with ...` is a helper `.fin` matching
# on the Cmp, given the recursive call as an argument.
# ---------------------------------------------------------------------------

def LexLeanCollections.insertEntry.fin(-K: Data, -V: Data, c: Cmp, key: K, value: V, e: L.Lean.Prod(K, V), rest: List<&2, L.Lean.Prod(K, V)>, recur: List<&2, L.Lean.Prod(K, V)>) -> List<&2, L.Lean.Prod(K, V)>:
  match c:
    case LT{}:
      Con{(key, value), Con{e, rest}}
    case EQ{}:
      Con{(key, value), rest}
    case GT{}:
      Con{e, recur}

def LexLeanCollections.insertEntry.Key(+k: LexLeanCollections.Key, -V: Data, +key: LexLeanCollections.Key.carrier(k), +value: V, m: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), V)>) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), V)>:
  match m:
    case Nil{}:
      [(key, value)]
    case Con{+e, +rest}:
      LexLeanCollections.insertEntry.fin(LexLeanCollections.Key.carrier(k), V, LexLeanCollections.Key.compare(k, key, Lean.Prod.fst(LexLeanCollections.Key.carrier(k), V, e)), key, value, e, rest, LexLeanCollections.insertEntry.Key(k, V, key, value, rest))

def LexLeanCollections.insertEntry.Nat(-V: Data, key: Nat, value: V, m: List<&2, L.Lean.Prod(Nat, V)>) -> List<&2, L.Lean.Prod(Nat, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.Nat{}, V, key, value, m)

def LexLeanCollections.insertEntry.Int(-V: Data, key: L.Lean.Int, value: V, m: List<&2, L.Lean.Prod(L.Lean.Int, V)>) -> List<&2, L.Lean.Prod(L.Lean.Int, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.Int{}, V, key, value, m)

def LexLeanCollections.insertEntry.Bool(-V: Data, key: Bool, value: V, m: List<&2, L.Lean.Prod(Bool, V)>) -> List<&2, L.Lean.Prod(Bool, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.Bool{}, V, key, value, m)

def LexLeanCollections.insertEntry.Int8(-V: Data, key: Lean.Int8, value: V, m: List<&2, L.Lean.Prod(Lean.Int8, V)>) -> List<&2, L.Lean.Prod(Lean.Int8, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.Int8{}, V, key, value, m)

def LexLeanCollections.insertEntry.Int16(-V: Data, key: Lean.Int16, value: V, m: List<&2, L.Lean.Prod(Lean.Int16, V)>) -> List<&2, L.Lean.Prod(Lean.Int16, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.Int16{}, V, key, value, m)

def LexLeanCollections.insertEntry.Int32(-V: Data, key: Lean.Int32, value: V, m: List<&2, L.Lean.Prod(Lean.Int32, V)>) -> List<&2, L.Lean.Prod(Lean.Int32, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.Int32{}, V, key, value, m)

def LexLeanCollections.insertEntry.Int64(-V: Data, key: Lean.Int64, value: V, m: List<&2, L.Lean.Prod(Lean.Int64, V)>) -> List<&2, L.Lean.Prod(Lean.Int64, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.Int64{}, V, key, value, m)

def LexLeanCollections.insertEntry.UInt8(-V: Data, key: Lean.UInt8, value: V, m: List<&2, L.Lean.Prod(Lean.UInt8, V)>) -> List<&2, L.Lean.Prod(Lean.UInt8, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.UInt8{}, V, key, value, m)

def LexLeanCollections.insertEntry.UInt16(-V: Data, key: Lean.UInt16, value: V, m: List<&2, L.Lean.Prod(Lean.UInt16, V)>) -> List<&2, L.Lean.Prod(Lean.UInt16, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.UInt16{}, V, key, value, m)

def LexLeanCollections.insertEntry.UInt32(-V: Data, key: U32, value: V, m: List<&2, L.Lean.Prod(U32, V)>) -> List<&2, L.Lean.Prod(U32, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.UInt32{}, V, key, value, m)

def LexLeanCollections.insertEntry.UInt64(-V: Data, key: Lean.UInt64, value: V, m: List<&2, L.Lean.Prod(Lean.UInt64, V)>) -> List<&2, L.Lean.Prod(Lean.UInt64, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.UInt64{}, V, key, value, m)

def LexLeanCollections.insertEntry.String(-V: Data, key: String, value: V, m: List<&2, L.Lean.Prod(String, V)>) -> List<&2, L.Lean.Prod(String, V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.String{}, V, key, value, m)

def LexLeanCollections.insertEntry.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, -V: Data, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), value: V, m: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), V)>) -> List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), V)>:
  LexLeanCollections.insertEntry.Key(LexLeanCollections.Key.Prod{ka, kb}, V, key, value, m)

def LexLeanCollections.removeEntry.fin(-K: Data, -V: Data, c: Cmp, e: L.Lean.Prod(K, V), rest: List<&2, L.Lean.Prod(K, V)>, recur: List<&2, L.Lean.Prod(K, V)>) -> List<&2, L.Lean.Prod(K, V)>:
  match c:
    case LT{}:
      Con{e, rest}
    case EQ{}:
      rest
    case GT{}:
      Con{e, recur}

def LexLeanCollections.removeEntry.Key(+k: LexLeanCollections.Key, -V: Data, +key: LexLeanCollections.Key.carrier(k), m: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), V)>) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), V)>:
  match m:
    case Nil{}:
      Nil{}
    case Con{+e, +rest}:
      LexLeanCollections.removeEntry.fin(LexLeanCollections.Key.carrier(k), V, LexLeanCollections.Key.compare(k, key, Lean.Prod.fst(LexLeanCollections.Key.carrier(k), V, e)), e, rest, LexLeanCollections.removeEntry.Key(k, V, key, rest))

def LexLeanCollections.removeEntry.Nat(-V: Data, key: Nat, m: List<&2, L.Lean.Prod(Nat, V)>) -> List<&2, L.Lean.Prod(Nat, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.Nat{}, V, key, m)

def LexLeanCollections.removeEntry.Int(-V: Data, key: L.Lean.Int, m: List<&2, L.Lean.Prod(L.Lean.Int, V)>) -> List<&2, L.Lean.Prod(L.Lean.Int, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.Int{}, V, key, m)

def LexLeanCollections.removeEntry.Bool(-V: Data, key: Bool, m: List<&2, L.Lean.Prod(Bool, V)>) -> List<&2, L.Lean.Prod(Bool, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.Bool{}, V, key, m)

def LexLeanCollections.removeEntry.Int8(-V: Data, key: Lean.Int8, m: List<&2, L.Lean.Prod(Lean.Int8, V)>) -> List<&2, L.Lean.Prod(Lean.Int8, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.Int8{}, V, key, m)

def LexLeanCollections.removeEntry.Int16(-V: Data, key: Lean.Int16, m: List<&2, L.Lean.Prod(Lean.Int16, V)>) -> List<&2, L.Lean.Prod(Lean.Int16, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.Int16{}, V, key, m)

def LexLeanCollections.removeEntry.Int32(-V: Data, key: Lean.Int32, m: List<&2, L.Lean.Prod(Lean.Int32, V)>) -> List<&2, L.Lean.Prod(Lean.Int32, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.Int32{}, V, key, m)

def LexLeanCollections.removeEntry.Int64(-V: Data, key: Lean.Int64, m: List<&2, L.Lean.Prod(Lean.Int64, V)>) -> List<&2, L.Lean.Prod(Lean.Int64, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.Int64{}, V, key, m)

def LexLeanCollections.removeEntry.UInt8(-V: Data, key: Lean.UInt8, m: List<&2, L.Lean.Prod(Lean.UInt8, V)>) -> List<&2, L.Lean.Prod(Lean.UInt8, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.UInt8{}, V, key, m)

def LexLeanCollections.removeEntry.UInt16(-V: Data, key: Lean.UInt16, m: List<&2, L.Lean.Prod(Lean.UInt16, V)>) -> List<&2, L.Lean.Prod(Lean.UInt16, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.UInt16{}, V, key, m)

def LexLeanCollections.removeEntry.UInt32(-V: Data, key: U32, m: List<&2, L.Lean.Prod(U32, V)>) -> List<&2, L.Lean.Prod(U32, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.UInt32{}, V, key, m)

def LexLeanCollections.removeEntry.UInt64(-V: Data, key: Lean.UInt64, m: List<&2, L.Lean.Prod(Lean.UInt64, V)>) -> List<&2, L.Lean.Prod(Lean.UInt64, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.UInt64{}, V, key, m)

def LexLeanCollections.removeEntry.String(-V: Data, key: String, m: List<&2, L.Lean.Prod(String, V)>) -> List<&2, L.Lean.Prod(String, V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.String{}, V, key, m)

def LexLeanCollections.removeEntry.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, -V: Data, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), m: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), V)>) -> List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), V)>:
  LexLeanCollections.removeEntry.Key(LexLeanCollections.Key.Prod{ka, kb}, V, key, m)

def LexLeanCollections.lookupEntry.fin(-V: Data, c: Cmp, stored: V, recur: Maybe<&2, V>) -> Maybe<&2, V>:
  match c:
    case LT{}:
      None{}
    case EQ{}:
      Some{stored}
    case GT{}:
      recur

def LexLeanCollections.lookupEntry.Key(+k: LexLeanCollections.Key, -V: Data, +key: LexLeanCollections.Key.carrier(k), m: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), V)>) -> Maybe<&2, V>:
  match m:
    case Nil{}:
      None{}
    case Con{+e, rest}:
      LexLeanCollections.lookupEntry.fin(V, LexLeanCollections.Key.compare(k, key, Lean.Prod.fst(LexLeanCollections.Key.carrier(k), V, e)), Lean.Prod.snd(LexLeanCollections.Key.carrier(k), V, e), LexLeanCollections.lookupEntry.Key(k, V, key, rest))

def LexLeanCollections.lookupEntry.Nat(-V: Data, key: Nat, m: List<&2, L.Lean.Prod(Nat, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.Nat{}, V, key, m)

def LexLeanCollections.lookupEntry.Int(-V: Data, key: L.Lean.Int, m: List<&2, L.Lean.Prod(L.Lean.Int, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.Int{}, V, key, m)

def LexLeanCollections.lookupEntry.Bool(-V: Data, key: Bool, m: List<&2, L.Lean.Prod(Bool, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.Bool{}, V, key, m)

def LexLeanCollections.lookupEntry.Int8(-V: Data, key: Lean.Int8, m: List<&2, L.Lean.Prod(Lean.Int8, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.Int8{}, V, key, m)

def LexLeanCollections.lookupEntry.Int16(-V: Data, key: Lean.Int16, m: List<&2, L.Lean.Prod(Lean.Int16, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.Int16{}, V, key, m)

def LexLeanCollections.lookupEntry.Int32(-V: Data, key: Lean.Int32, m: List<&2, L.Lean.Prod(Lean.Int32, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.Int32{}, V, key, m)

def LexLeanCollections.lookupEntry.Int64(-V: Data, key: Lean.Int64, m: List<&2, L.Lean.Prod(Lean.Int64, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.Int64{}, V, key, m)

def LexLeanCollections.lookupEntry.UInt8(-V: Data, key: Lean.UInt8, m: List<&2, L.Lean.Prod(Lean.UInt8, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.UInt8{}, V, key, m)

def LexLeanCollections.lookupEntry.UInt16(-V: Data, key: Lean.UInt16, m: List<&2, L.Lean.Prod(Lean.UInt16, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.UInt16{}, V, key, m)

def LexLeanCollections.lookupEntry.UInt32(-V: Data, key: U32, m: List<&2, L.Lean.Prod(U32, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.UInt32{}, V, key, m)

def LexLeanCollections.lookupEntry.UInt64(-V: Data, key: Lean.UInt64, m: List<&2, L.Lean.Prod(Lean.UInt64, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.UInt64{}, V, key, m)

def LexLeanCollections.lookupEntry.String(-V: Data, key: String, m: List<&2, L.Lean.Prod(String, V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.String{}, V, key, m)

def LexLeanCollections.lookupEntry.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, -V: Data, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), m: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), V)>) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(LexLeanCollections.Key.Prod{ka, kb}, V, key, m)

def LexLeanCollections.insertElement.fin(-K: Data, c: Cmp, key: K, other: K, rest: List<&2, K>, recur: List<&2, K>) -> List<&2, K>:
  match c:
    case LT{}:
      Con{key, Con{other, rest}}
    case EQ{}:
      Con{other, rest}
    case GT{}:
      Con{other, recur}

def LexLeanCollections.insertElement.Key(+k: LexLeanCollections.Key, +key: LexLeanCollections.Key.carrier(k), s: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  match s:
    case Nil{}:
      [key]
    case Con{+other, +rest}:
      LexLeanCollections.insertElement.fin(LexLeanCollections.Key.carrier(k), LexLeanCollections.Key.compare(k, key, other), key, other, rest, LexLeanCollections.insertElement.Key(k, key, rest))

def LexLeanCollections.insertElement.Nat(key: Nat, s: List<&2, Nat>) -> List<&2, Nat>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.Nat{}, key, s)

def LexLeanCollections.insertElement.Int(key: L.Lean.Int, s: List<&2, L.Lean.Int>) -> List<&2, L.Lean.Int>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.Int{}, key, s)

def LexLeanCollections.insertElement.Bool(key: Bool, s: List<&2, Bool>) -> List<&2, Bool>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.Bool{}, key, s)

def LexLeanCollections.insertElement.Int8(key: Lean.Int8, s: List<&2, Lean.Int8>) -> List<&2, Lean.Int8>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.Int8{}, key, s)

def LexLeanCollections.insertElement.Int16(key: Lean.Int16, s: List<&2, Lean.Int16>) -> List<&2, Lean.Int16>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.Int16{}, key, s)

def LexLeanCollections.insertElement.Int32(key: Lean.Int32, s: List<&2, Lean.Int32>) -> List<&2, Lean.Int32>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.Int32{}, key, s)

def LexLeanCollections.insertElement.Int64(key: Lean.Int64, s: List<&2, Lean.Int64>) -> List<&2, Lean.Int64>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.Int64{}, key, s)

def LexLeanCollections.insertElement.UInt8(key: Lean.UInt8, s: List<&2, Lean.UInt8>) -> List<&2, Lean.UInt8>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.UInt8{}, key, s)

def LexLeanCollections.insertElement.UInt16(key: Lean.UInt16, s: List<&2, Lean.UInt16>) -> List<&2, Lean.UInt16>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.UInt16{}, key, s)

def LexLeanCollections.insertElement.UInt32(key: U32, s: List<&2, U32>) -> List<&2, U32>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.UInt32{}, key, s)

def LexLeanCollections.insertElement.UInt64(key: Lean.UInt64, s: List<&2, Lean.UInt64>) -> List<&2, Lean.UInt64>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.UInt64{}, key, s)

def LexLeanCollections.insertElement.String(key: String, s: List<&2, String>) -> List<&2, String>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.String{}, key, s)

def LexLeanCollections.insertElement.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), s: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>:
  LexLeanCollections.insertElement.Key(LexLeanCollections.Key.Prod{ka, kb}, key, s)

def LexLeanCollections.removeElement.fin(-K: Data, c: Cmp, other: K, rest: List<&2, K>, recur: List<&2, K>) -> List<&2, K>:
  match c:
    case LT{}:
      Con{other, rest}
    case EQ{}:
      rest
    case GT{}:
      Con{other, recur}

def LexLeanCollections.removeElement.Key(+k: LexLeanCollections.Key, +key: LexLeanCollections.Key.carrier(k), s: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  match s:
    case Nil{}:
      Nil{}
    case Con{+other, +rest}:
      LexLeanCollections.removeElement.fin(LexLeanCollections.Key.carrier(k), LexLeanCollections.Key.compare(k, key, other), other, rest, LexLeanCollections.removeElement.Key(k, key, rest))

def LexLeanCollections.removeElement.Nat(key: Nat, s: List<&2, Nat>) -> List<&2, Nat>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.Nat{}, key, s)

def LexLeanCollections.removeElement.Int(key: L.Lean.Int, s: List<&2, L.Lean.Int>) -> List<&2, L.Lean.Int>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.Int{}, key, s)

def LexLeanCollections.removeElement.Bool(key: Bool, s: List<&2, Bool>) -> List<&2, Bool>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.Bool{}, key, s)

def LexLeanCollections.removeElement.Int8(key: Lean.Int8, s: List<&2, Lean.Int8>) -> List<&2, Lean.Int8>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.Int8{}, key, s)

def LexLeanCollections.removeElement.Int16(key: Lean.Int16, s: List<&2, Lean.Int16>) -> List<&2, Lean.Int16>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.Int16{}, key, s)

def LexLeanCollections.removeElement.Int32(key: Lean.Int32, s: List<&2, Lean.Int32>) -> List<&2, Lean.Int32>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.Int32{}, key, s)

def LexLeanCollections.removeElement.Int64(key: Lean.Int64, s: List<&2, Lean.Int64>) -> List<&2, Lean.Int64>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.Int64{}, key, s)

def LexLeanCollections.removeElement.UInt8(key: Lean.UInt8, s: List<&2, Lean.UInt8>) -> List<&2, Lean.UInt8>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.UInt8{}, key, s)

def LexLeanCollections.removeElement.UInt16(key: Lean.UInt16, s: List<&2, Lean.UInt16>) -> List<&2, Lean.UInt16>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.UInt16{}, key, s)

def LexLeanCollections.removeElement.UInt32(key: U32, s: List<&2, U32>) -> List<&2, U32>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.UInt32{}, key, s)

def LexLeanCollections.removeElement.UInt64(key: Lean.UInt64, s: List<&2, Lean.UInt64>) -> List<&2, Lean.UInt64>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.UInt64{}, key, s)

def LexLeanCollections.removeElement.String(key: String, s: List<&2, String>) -> List<&2, String>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.String{}, key, s)

def LexLeanCollections.removeElement.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), s: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>:
  LexLeanCollections.removeElement.Key(LexLeanCollections.Key.Prod{ka, kb}, key, s)

def LexLeanCollections.containsElement.fin(c: Cmp, recur: Bool) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      recur

def LexLeanCollections.containsElement.Key(+k: LexLeanCollections.Key, +key: LexLeanCollections.Key.carrier(k), s: List<&2, LexLeanCollections.Key.carrier(k)>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case Con{other, rest}:
      LexLeanCollections.containsElement.fin(LexLeanCollections.Key.compare(k, key, other), LexLeanCollections.containsElement.Key(k, key, rest))

def LexLeanCollections.containsElement.Nat(key: Nat, s: List<&2, Nat>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.Nat{}, key, s)

def LexLeanCollections.containsElement.Int(key: L.Lean.Int, s: List<&2, L.Lean.Int>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.Int{}, key, s)

def LexLeanCollections.containsElement.Bool(key: Bool, s: List<&2, Bool>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.Bool{}, key, s)

def LexLeanCollections.containsElement.Int8(key: Lean.Int8, s: List<&2, Lean.Int8>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.Int8{}, key, s)

def LexLeanCollections.containsElement.Int16(key: Lean.Int16, s: List<&2, Lean.Int16>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.Int16{}, key, s)

def LexLeanCollections.containsElement.Int32(key: Lean.Int32, s: List<&2, Lean.Int32>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.Int32{}, key, s)

def LexLeanCollections.containsElement.Int64(key: Lean.Int64, s: List<&2, Lean.Int64>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.Int64{}, key, s)

def LexLeanCollections.containsElement.UInt8(key: Lean.UInt8, s: List<&2, Lean.UInt8>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.UInt8{}, key, s)

def LexLeanCollections.containsElement.UInt16(key: Lean.UInt16, s: List<&2, Lean.UInt16>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.UInt16{}, key, s)

def LexLeanCollections.containsElement.UInt32(key: U32, s: List<&2, U32>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.UInt32{}, key, s)

def LexLeanCollections.containsElement.UInt64(key: Lean.UInt64, s: List<&2, Lean.UInt64>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.UInt64{}, key, s)

def LexLeanCollections.containsElement.String(key: String, s: List<&2, String>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.String{}, key, s)

def LexLeanCollections.containsElement.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), s: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>) -> Bool:
  LexLeanCollections.containsElement.Key(LexLeanCollections.Key.Prod{ka, kb}, key, s)

def LexLeanCollections.mapInsert.Key(+k: LexLeanCollections.Key, -V: Data, map: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), V)>, key: LexLeanCollections.Key.carrier(k), value: V) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), V)>:
  LexLeanCollections.insertEntry.Key(k, V, key, value, map)

def LexLeanCollections.mapInsert.Nat(-V: Data, map: List<&2, L.Lean.Prod(Nat, V)>, key: Nat, value: V) -> List<&2, L.Lean.Prod(Nat, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.Nat{}, V, map, key, value)

def LexLeanCollections.mapInsert.Int(-V: Data, map: List<&2, L.Lean.Prod(L.Lean.Int, V)>, key: L.Lean.Int, value: V) -> List<&2, L.Lean.Prod(L.Lean.Int, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.Int{}, V, map, key, value)

def LexLeanCollections.mapInsert.Bool(-V: Data, map: List<&2, L.Lean.Prod(Bool, V)>, key: Bool, value: V) -> List<&2, L.Lean.Prod(Bool, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.Bool{}, V, map, key, value)

def LexLeanCollections.mapInsert.Int8(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int8, V)>, key: Lean.Int8, value: V) -> List<&2, L.Lean.Prod(Lean.Int8, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.Int8{}, V, map, key, value)

def LexLeanCollections.mapInsert.Int16(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int16, V)>, key: Lean.Int16, value: V) -> List<&2, L.Lean.Prod(Lean.Int16, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.Int16{}, V, map, key, value)

def LexLeanCollections.mapInsert.Int32(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int32, V)>, key: Lean.Int32, value: V) -> List<&2, L.Lean.Prod(Lean.Int32, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.Int32{}, V, map, key, value)

def LexLeanCollections.mapInsert.Int64(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int64, V)>, key: Lean.Int64, value: V) -> List<&2, L.Lean.Prod(Lean.Int64, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.Int64{}, V, map, key, value)

def LexLeanCollections.mapInsert.UInt8(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt8, V)>, key: Lean.UInt8, value: V) -> List<&2, L.Lean.Prod(Lean.UInt8, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.UInt8{}, V, map, key, value)

def LexLeanCollections.mapInsert.UInt16(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt16, V)>, key: Lean.UInt16, value: V) -> List<&2, L.Lean.Prod(Lean.UInt16, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.UInt16{}, V, map, key, value)

def LexLeanCollections.mapInsert.UInt32(-V: Data, map: List<&2, L.Lean.Prod(U32, V)>, key: U32, value: V) -> List<&2, L.Lean.Prod(U32, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.UInt32{}, V, map, key, value)

def LexLeanCollections.mapInsert.UInt64(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt64, V)>, key: Lean.UInt64, value: V) -> List<&2, L.Lean.Prod(Lean.UInt64, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.UInt64{}, V, map, key, value)

def LexLeanCollections.mapInsert.String(-V: Data, map: List<&2, L.Lean.Prod(String, V)>, key: String, value: V) -> List<&2, L.Lean.Prod(String, V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.String{}, V, map, key, value)

def LexLeanCollections.mapInsert.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, -V: Data, map: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), V)>, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), value: V) -> List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), V)>:
  LexLeanCollections.mapInsert.Key(LexLeanCollections.Key.Prod{ka, kb}, V, map, key, value)

def LexLeanCollections.mapRemove.Key(+k: LexLeanCollections.Key, -V: Data, map: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), V)>, key: LexLeanCollections.Key.carrier(k)) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), V)>:
  LexLeanCollections.removeEntry.Key(k, V, key, map)

def LexLeanCollections.mapRemove.Nat(-V: Data, map: List<&2, L.Lean.Prod(Nat, V)>, key: Nat) -> List<&2, L.Lean.Prod(Nat, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.Nat{}, V, map, key)

def LexLeanCollections.mapRemove.Int(-V: Data, map: List<&2, L.Lean.Prod(L.Lean.Int, V)>, key: L.Lean.Int) -> List<&2, L.Lean.Prod(L.Lean.Int, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.Int{}, V, map, key)

def LexLeanCollections.mapRemove.Bool(-V: Data, map: List<&2, L.Lean.Prod(Bool, V)>, key: Bool) -> List<&2, L.Lean.Prod(Bool, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.Bool{}, V, map, key)

def LexLeanCollections.mapRemove.Int8(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int8, V)>, key: Lean.Int8) -> List<&2, L.Lean.Prod(Lean.Int8, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.Int8{}, V, map, key)

def LexLeanCollections.mapRemove.Int16(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int16, V)>, key: Lean.Int16) -> List<&2, L.Lean.Prod(Lean.Int16, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.Int16{}, V, map, key)

def LexLeanCollections.mapRemove.Int32(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int32, V)>, key: Lean.Int32) -> List<&2, L.Lean.Prod(Lean.Int32, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.Int32{}, V, map, key)

def LexLeanCollections.mapRemove.Int64(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int64, V)>, key: Lean.Int64) -> List<&2, L.Lean.Prod(Lean.Int64, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.Int64{}, V, map, key)

def LexLeanCollections.mapRemove.UInt8(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt8, V)>, key: Lean.UInt8) -> List<&2, L.Lean.Prod(Lean.UInt8, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.UInt8{}, V, map, key)

def LexLeanCollections.mapRemove.UInt16(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt16, V)>, key: Lean.UInt16) -> List<&2, L.Lean.Prod(Lean.UInt16, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.UInt16{}, V, map, key)

def LexLeanCollections.mapRemove.UInt32(-V: Data, map: List<&2, L.Lean.Prod(U32, V)>, key: U32) -> List<&2, L.Lean.Prod(U32, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.UInt32{}, V, map, key)

def LexLeanCollections.mapRemove.UInt64(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt64, V)>, key: Lean.UInt64) -> List<&2, L.Lean.Prod(Lean.UInt64, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.UInt64{}, V, map, key)

def LexLeanCollections.mapRemove.String(-V: Data, map: List<&2, L.Lean.Prod(String, V)>, key: String) -> List<&2, L.Lean.Prod(String, V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.String{}, V, map, key)

def LexLeanCollections.mapRemove.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, -V: Data, map: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), V)>, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))) -> List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), V)>:
  LexLeanCollections.mapRemove.Key(LexLeanCollections.Key.Prod{ka, kb}, V, map, key)

def LexLeanCollections.mapLookup.Key(+k: LexLeanCollections.Key, -V: Data, map: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), V)>, key: LexLeanCollections.Key.carrier(k)) -> Maybe<&2, V>:
  LexLeanCollections.lookupEntry.Key(k, V, key, map)

def LexLeanCollections.mapLookup.Nat(-V: Data, map: List<&2, L.Lean.Prod(Nat, V)>, key: Nat) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.Nat{}, V, map, key)

def LexLeanCollections.mapLookup.Int(-V: Data, map: List<&2, L.Lean.Prod(L.Lean.Int, V)>, key: L.Lean.Int) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.Int{}, V, map, key)

def LexLeanCollections.mapLookup.Bool(-V: Data, map: List<&2, L.Lean.Prod(Bool, V)>, key: Bool) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.Bool{}, V, map, key)

def LexLeanCollections.mapLookup.Int8(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int8, V)>, key: Lean.Int8) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.Int8{}, V, map, key)

def LexLeanCollections.mapLookup.Int16(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int16, V)>, key: Lean.Int16) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.Int16{}, V, map, key)

def LexLeanCollections.mapLookup.Int32(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int32, V)>, key: Lean.Int32) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.Int32{}, V, map, key)

def LexLeanCollections.mapLookup.Int64(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int64, V)>, key: Lean.Int64) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.Int64{}, V, map, key)

def LexLeanCollections.mapLookup.UInt8(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt8, V)>, key: Lean.UInt8) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.UInt8{}, V, map, key)

def LexLeanCollections.mapLookup.UInt16(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt16, V)>, key: Lean.UInt16) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.UInt16{}, V, map, key)

def LexLeanCollections.mapLookup.UInt32(-V: Data, map: List<&2, L.Lean.Prod(U32, V)>, key: U32) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.UInt32{}, V, map, key)

def LexLeanCollections.mapLookup.UInt64(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt64, V)>, key: Lean.UInt64) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.UInt64{}, V, map, key)

def LexLeanCollections.mapLookup.String(-V: Data, map: List<&2, L.Lean.Prod(String, V)>, key: String) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.String{}, V, map, key)

def LexLeanCollections.mapLookup.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, -V: Data, map: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), V)>, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))) -> Maybe<&2, V>:
  LexLeanCollections.mapLookup.Key(LexLeanCollections.Key.Prod{ka, kb}, V, map, key)

def LexLeanCollections.mapContains.Key(+k: LexLeanCollections.Key, -V: Data, map: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), V)>, key: LexLeanCollections.Key.carrier(k)) -> Bool:
  Maybe.is_some(&2, V, LexLeanCollections.lookupEntry.Key(k, V, key, map))

def LexLeanCollections.mapContains.Nat(-V: Data, map: List<&2, L.Lean.Prod(Nat, V)>, key: Nat) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.Nat{}, V, map, key)

def LexLeanCollections.mapContains.Int(-V: Data, map: List<&2, L.Lean.Prod(L.Lean.Int, V)>, key: L.Lean.Int) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.Int{}, V, map, key)

def LexLeanCollections.mapContains.Bool(-V: Data, map: List<&2, L.Lean.Prod(Bool, V)>, key: Bool) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.Bool{}, V, map, key)

def LexLeanCollections.mapContains.Int8(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int8, V)>, key: Lean.Int8) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.Int8{}, V, map, key)

def LexLeanCollections.mapContains.Int16(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int16, V)>, key: Lean.Int16) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.Int16{}, V, map, key)

def LexLeanCollections.mapContains.Int32(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int32, V)>, key: Lean.Int32) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.Int32{}, V, map, key)

def LexLeanCollections.mapContains.Int64(-V: Data, map: List<&2, L.Lean.Prod(Lean.Int64, V)>, key: Lean.Int64) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.Int64{}, V, map, key)

def LexLeanCollections.mapContains.UInt8(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt8, V)>, key: Lean.UInt8) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.UInt8{}, V, map, key)

def LexLeanCollections.mapContains.UInt16(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt16, V)>, key: Lean.UInt16) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.UInt16{}, V, map, key)

def LexLeanCollections.mapContains.UInt32(-V: Data, map: List<&2, L.Lean.Prod(U32, V)>, key: U32) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.UInt32{}, V, map, key)

def LexLeanCollections.mapContains.UInt64(-V: Data, map: List<&2, L.Lean.Prod(Lean.UInt64, V)>, key: Lean.UInt64) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.UInt64{}, V, map, key)

def LexLeanCollections.mapContains.String(-V: Data, map: List<&2, L.Lean.Prod(String, V)>, key: String) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.String{}, V, map, key)

def LexLeanCollections.mapContains.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, -V: Data, map: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), V)>, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))) -> Bool:
  LexLeanCollections.mapContains.Key(LexLeanCollections.Key.Prod{ka, kb}, V, map, key)

def LexLeanCollections.setInsert.Key(+k: LexLeanCollections.Key, set: List<&2, LexLeanCollections.Key.carrier(k)>, key: LexLeanCollections.Key.carrier(k)) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  LexLeanCollections.insertElement.Key(k, key, set)

def LexLeanCollections.setInsert.Nat(set: List<&2, Nat>, key: Nat) -> List<&2, Nat>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.Nat{}, set, key)

def LexLeanCollections.setInsert.Int(set: List<&2, L.Lean.Int>, key: L.Lean.Int) -> List<&2, L.Lean.Int>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.Int{}, set, key)

def LexLeanCollections.setInsert.Bool(set: List<&2, Bool>, key: Bool) -> List<&2, Bool>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.Bool{}, set, key)

def LexLeanCollections.setInsert.Int8(set: List<&2, Lean.Int8>, key: Lean.Int8) -> List<&2, Lean.Int8>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.Int8{}, set, key)

def LexLeanCollections.setInsert.Int16(set: List<&2, Lean.Int16>, key: Lean.Int16) -> List<&2, Lean.Int16>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.Int16{}, set, key)

def LexLeanCollections.setInsert.Int32(set: List<&2, Lean.Int32>, key: Lean.Int32) -> List<&2, Lean.Int32>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.Int32{}, set, key)

def LexLeanCollections.setInsert.Int64(set: List<&2, Lean.Int64>, key: Lean.Int64) -> List<&2, Lean.Int64>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.Int64{}, set, key)

def LexLeanCollections.setInsert.UInt8(set: List<&2, Lean.UInt8>, key: Lean.UInt8) -> List<&2, Lean.UInt8>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.UInt8{}, set, key)

def LexLeanCollections.setInsert.UInt16(set: List<&2, Lean.UInt16>, key: Lean.UInt16) -> List<&2, Lean.UInt16>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.UInt16{}, set, key)

def LexLeanCollections.setInsert.UInt32(set: List<&2, U32>, key: U32) -> List<&2, U32>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.UInt32{}, set, key)

def LexLeanCollections.setInsert.UInt64(set: List<&2, Lean.UInt64>, key: Lean.UInt64) -> List<&2, Lean.UInt64>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.UInt64{}, set, key)

def LexLeanCollections.setInsert.String(set: List<&2, String>, key: String) -> List<&2, String>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.String{}, set, key)

def LexLeanCollections.setInsert.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, set: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>:
  LexLeanCollections.setInsert.Key(LexLeanCollections.Key.Prod{ka, kb}, set, key)

def LexLeanCollections.setRemove.Key(+k: LexLeanCollections.Key, set: List<&2, LexLeanCollections.Key.carrier(k)>, key: LexLeanCollections.Key.carrier(k)) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  LexLeanCollections.removeElement.Key(k, key, set)

def LexLeanCollections.setRemove.Nat(set: List<&2, Nat>, key: Nat) -> List<&2, Nat>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.Nat{}, set, key)

def LexLeanCollections.setRemove.Int(set: List<&2, L.Lean.Int>, key: L.Lean.Int) -> List<&2, L.Lean.Int>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.Int{}, set, key)

def LexLeanCollections.setRemove.Bool(set: List<&2, Bool>, key: Bool) -> List<&2, Bool>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.Bool{}, set, key)

def LexLeanCollections.setRemove.Int8(set: List<&2, Lean.Int8>, key: Lean.Int8) -> List<&2, Lean.Int8>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.Int8{}, set, key)

def LexLeanCollections.setRemove.Int16(set: List<&2, Lean.Int16>, key: Lean.Int16) -> List<&2, Lean.Int16>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.Int16{}, set, key)

def LexLeanCollections.setRemove.Int32(set: List<&2, Lean.Int32>, key: Lean.Int32) -> List<&2, Lean.Int32>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.Int32{}, set, key)

def LexLeanCollections.setRemove.Int64(set: List<&2, Lean.Int64>, key: Lean.Int64) -> List<&2, Lean.Int64>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.Int64{}, set, key)

def LexLeanCollections.setRemove.UInt8(set: List<&2, Lean.UInt8>, key: Lean.UInt8) -> List<&2, Lean.UInt8>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.UInt8{}, set, key)

def LexLeanCollections.setRemove.UInt16(set: List<&2, Lean.UInt16>, key: Lean.UInt16) -> List<&2, Lean.UInt16>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.UInt16{}, set, key)

def LexLeanCollections.setRemove.UInt32(set: List<&2, U32>, key: U32) -> List<&2, U32>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.UInt32{}, set, key)

def LexLeanCollections.setRemove.UInt64(set: List<&2, Lean.UInt64>, key: Lean.UInt64) -> List<&2, Lean.UInt64>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.UInt64{}, set, key)

def LexLeanCollections.setRemove.String(set: List<&2, String>, key: String) -> List<&2, String>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.String{}, set, key)

def LexLeanCollections.setRemove.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, set: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>:
  LexLeanCollections.setRemove.Key(LexLeanCollections.Key.Prod{ka, kb}, set, key)

def LexLeanCollections.setContains.Key(+k: LexLeanCollections.Key, set: List<&2, LexLeanCollections.Key.carrier(k)>, key: LexLeanCollections.Key.carrier(k)) -> Bool:
  LexLeanCollections.containsElement.Key(k, key, set)

def LexLeanCollections.setContains.Nat(set: List<&2, Nat>, key: Nat) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.Nat{}, set, key)

def LexLeanCollections.setContains.Int(set: List<&2, L.Lean.Int>, key: L.Lean.Int) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.Int{}, set, key)

def LexLeanCollections.setContains.Bool(set: List<&2, Bool>, key: Bool) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.Bool{}, set, key)

def LexLeanCollections.setContains.Int8(set: List<&2, Lean.Int8>, key: Lean.Int8) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.Int8{}, set, key)

def LexLeanCollections.setContains.Int16(set: List<&2, Lean.Int16>, key: Lean.Int16) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.Int16{}, set, key)

def LexLeanCollections.setContains.Int32(set: List<&2, Lean.Int32>, key: Lean.Int32) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.Int32{}, set, key)

def LexLeanCollections.setContains.Int64(set: List<&2, Lean.Int64>, key: Lean.Int64) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.Int64{}, set, key)

def LexLeanCollections.setContains.UInt8(set: List<&2, Lean.UInt8>, key: Lean.UInt8) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.UInt8{}, set, key)

def LexLeanCollections.setContains.UInt16(set: List<&2, Lean.UInt16>, key: Lean.UInt16) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.UInt16{}, set, key)

def LexLeanCollections.setContains.UInt32(set: List<&2, U32>, key: U32) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.UInt32{}, set, key)

def LexLeanCollections.setContains.UInt64(set: List<&2, Lean.UInt64>, key: Lean.UInt64) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.UInt64{}, set, key)

def LexLeanCollections.setContains.String(set: List<&2, String>, key: String) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.String{}, set, key)

def LexLeanCollections.setContains.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, set: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>, key: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))) -> Bool:
  LexLeanCollections.setContains.Key(LexLeanCollections.Key.Prod{ka, kb}, set, key)

# right.foldl (fun acc key => insertElement key acc) left
def LexLeanCollections.setUnion.go(+k: LexLeanCollections.Key, right: List<&2, LexLeanCollections.Key.carrier(k)>, acc: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  match right:
    case Nil{}:
      acc
    case Con{key, rest}:
      LexLeanCollections.setUnion.go(k, rest, LexLeanCollections.insertElement.Key(k, key, acc))

def LexLeanCollections.filter.put(-K: Data, keep: Bool, key: K, rest: List<&2, K>) -> List<&2, K>:
  match keep:
    case True{}:
      Con{key, rest}
    case False{}:
      rest

def LexLeanCollections.setUnion.Key(+k: LexLeanCollections.Key, left: List<&2, LexLeanCollections.Key.carrier(k)>, right: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  LexLeanCollections.setUnion.go(k, right, left)

def LexLeanCollections.setUnion.Nat(left: List<&2, Nat>, right: List<&2, Nat>) -> List<&2, Nat>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.Nat{}, left, right)

def LexLeanCollections.setUnion.Int(left: List<&2, L.Lean.Int>, right: List<&2, L.Lean.Int>) -> List<&2, L.Lean.Int>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.Int{}, left, right)

def LexLeanCollections.setUnion.Bool(left: List<&2, Bool>, right: List<&2, Bool>) -> List<&2, Bool>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.Bool{}, left, right)

def LexLeanCollections.setUnion.Int8(left: List<&2, Lean.Int8>, right: List<&2, Lean.Int8>) -> List<&2, Lean.Int8>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.Int8{}, left, right)

def LexLeanCollections.setUnion.Int16(left: List<&2, Lean.Int16>, right: List<&2, Lean.Int16>) -> List<&2, Lean.Int16>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.Int16{}, left, right)

def LexLeanCollections.setUnion.Int32(left: List<&2, Lean.Int32>, right: List<&2, Lean.Int32>) -> List<&2, Lean.Int32>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.Int32{}, left, right)

def LexLeanCollections.setUnion.Int64(left: List<&2, Lean.Int64>, right: List<&2, Lean.Int64>) -> List<&2, Lean.Int64>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.Int64{}, left, right)

def LexLeanCollections.setUnion.UInt8(left: List<&2, Lean.UInt8>, right: List<&2, Lean.UInt8>) -> List<&2, Lean.UInt8>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.UInt8{}, left, right)

def LexLeanCollections.setUnion.UInt16(left: List<&2, Lean.UInt16>, right: List<&2, Lean.UInt16>) -> List<&2, Lean.UInt16>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.UInt16{}, left, right)

def LexLeanCollections.setUnion.UInt32(left: List<&2, U32>, right: List<&2, U32>) -> List<&2, U32>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.UInt32{}, left, right)

def LexLeanCollections.setUnion.UInt64(left: List<&2, Lean.UInt64>, right: List<&2, Lean.UInt64>) -> List<&2, Lean.UInt64>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.UInt64{}, left, right)

def LexLeanCollections.setUnion.String(left: List<&2, String>, right: List<&2, String>) -> List<&2, String>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.String{}, left, right)

def LexLeanCollections.setUnion.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, left: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>, right: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>:
  LexLeanCollections.setUnion.Key(LexLeanCollections.Key.Prod{ka, kb}, left, right)

def LexLeanCollections.setIntersection.Key(+k: LexLeanCollections.Key, left: List<&2, LexLeanCollections.Key.carrier(k)>, +right: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  match left:
    case Nil{}:
      Nil{}
    case Con{+key, rest}:
      LexLeanCollections.filter.put(LexLeanCollections.Key.carrier(k), LexLeanCollections.containsElement.Key(k, key, right), key, LexLeanCollections.setIntersection.Key(k, rest, right))

def LexLeanCollections.setIntersection.Nat(left: List<&2, Nat>, right: List<&2, Nat>) -> List<&2, Nat>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.Nat{}, left, right)

def LexLeanCollections.setIntersection.Int(left: List<&2, L.Lean.Int>, right: List<&2, L.Lean.Int>) -> List<&2, L.Lean.Int>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.Int{}, left, right)

def LexLeanCollections.setIntersection.Bool(left: List<&2, Bool>, right: List<&2, Bool>) -> List<&2, Bool>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.Bool{}, left, right)

def LexLeanCollections.setIntersection.Int8(left: List<&2, Lean.Int8>, right: List<&2, Lean.Int8>) -> List<&2, Lean.Int8>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.Int8{}, left, right)

def LexLeanCollections.setIntersection.Int16(left: List<&2, Lean.Int16>, right: List<&2, Lean.Int16>) -> List<&2, Lean.Int16>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.Int16{}, left, right)

def LexLeanCollections.setIntersection.Int32(left: List<&2, Lean.Int32>, right: List<&2, Lean.Int32>) -> List<&2, Lean.Int32>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.Int32{}, left, right)

def LexLeanCollections.setIntersection.Int64(left: List<&2, Lean.Int64>, right: List<&2, Lean.Int64>) -> List<&2, Lean.Int64>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.Int64{}, left, right)

def LexLeanCollections.setIntersection.UInt8(left: List<&2, Lean.UInt8>, right: List<&2, Lean.UInt8>) -> List<&2, Lean.UInt8>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.UInt8{}, left, right)

def LexLeanCollections.setIntersection.UInt16(left: List<&2, Lean.UInt16>, right: List<&2, Lean.UInt16>) -> List<&2, Lean.UInt16>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.UInt16{}, left, right)

def LexLeanCollections.setIntersection.UInt32(left: List<&2, U32>, right: List<&2, U32>) -> List<&2, U32>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.UInt32{}, left, right)

def LexLeanCollections.setIntersection.UInt64(left: List<&2, Lean.UInt64>, right: List<&2, Lean.UInt64>) -> List<&2, Lean.UInt64>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.UInt64{}, left, right)

def LexLeanCollections.setIntersection.String(left: List<&2, String>, right: List<&2, String>) -> List<&2, String>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.String{}, left, right)

def LexLeanCollections.setIntersection.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, left: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>, right: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>:
  LexLeanCollections.setIntersection.Key(LexLeanCollections.Key.Prod{ka, kb}, left, right)

def LexLeanCollections.setDifference.Key(+k: LexLeanCollections.Key, left: List<&2, LexLeanCollections.Key.carrier(k)>, +right: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  match left:
    case Nil{}:
      Nil{}
    case Con{+key, rest}:
      LexLeanCollections.filter.put(LexLeanCollections.Key.carrier(k), L.Lean.Bool.not(LexLeanCollections.containsElement.Key(k, key, right)), key, LexLeanCollections.setDifference.Key(k, rest, right))

def LexLeanCollections.setDifference.Nat(left: List<&2, Nat>, right: List<&2, Nat>) -> List<&2, Nat>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.Nat{}, left, right)

def LexLeanCollections.setDifference.Int(left: List<&2, L.Lean.Int>, right: List<&2, L.Lean.Int>) -> List<&2, L.Lean.Int>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.Int{}, left, right)

def LexLeanCollections.setDifference.Bool(left: List<&2, Bool>, right: List<&2, Bool>) -> List<&2, Bool>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.Bool{}, left, right)

def LexLeanCollections.setDifference.Int8(left: List<&2, Lean.Int8>, right: List<&2, Lean.Int8>) -> List<&2, Lean.Int8>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.Int8{}, left, right)

def LexLeanCollections.setDifference.Int16(left: List<&2, Lean.Int16>, right: List<&2, Lean.Int16>) -> List<&2, Lean.Int16>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.Int16{}, left, right)

def LexLeanCollections.setDifference.Int32(left: List<&2, Lean.Int32>, right: List<&2, Lean.Int32>) -> List<&2, Lean.Int32>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.Int32{}, left, right)

def LexLeanCollections.setDifference.Int64(left: List<&2, Lean.Int64>, right: List<&2, Lean.Int64>) -> List<&2, Lean.Int64>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.Int64{}, left, right)

def LexLeanCollections.setDifference.UInt8(left: List<&2, Lean.UInt8>, right: List<&2, Lean.UInt8>) -> List<&2, Lean.UInt8>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.UInt8{}, left, right)

def LexLeanCollections.setDifference.UInt16(left: List<&2, Lean.UInt16>, right: List<&2, Lean.UInt16>) -> List<&2, Lean.UInt16>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.UInt16{}, left, right)

def LexLeanCollections.setDifference.UInt32(left: List<&2, U32>, right: List<&2, U32>) -> List<&2, U32>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.UInt32{}, left, right)

def LexLeanCollections.setDifference.UInt64(left: List<&2, Lean.UInt64>, right: List<&2, Lean.UInt64>) -> List<&2, Lean.UInt64>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.UInt64{}, left, right)

def LexLeanCollections.setDifference.String(left: List<&2, String>, right: List<&2, String>) -> List<&2, String>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.String{}, left, right)

def LexLeanCollections.setDifference.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, left: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>, right: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>:
  LexLeanCollections.setDifference.Key(LexLeanCollections.Key.Prod{ka, kb}, left, right)

def LexLeanCollections.graphSuccessors.Key(+k: LexLeanCollections.Key, graph: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>)>, node: LexLeanCollections.Key.carrier(k)) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  Maybe.default(&2, List<&2, LexLeanCollections.Key.carrier(k)>, LexLeanCollections.lookupEntry.Key(k, List<&2, LexLeanCollections.Key.carrier(k)>, node, graph), Nil{})

def LexLeanCollections.graphSuccessors.Nat(graph: List<&2, L.Lean.Prod(Nat, List<&2, Nat>)>, node: Nat) -> List<&2, Nat>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.Nat{}, graph, node)

def LexLeanCollections.graphSuccessors.Int(graph: List<&2, L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>)>, node: L.Lean.Int) -> List<&2, L.Lean.Int>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.Int{}, graph, node)

def LexLeanCollections.graphSuccessors.Bool(graph: List<&2, L.Lean.Prod(Bool, List<&2, Bool>)>, node: Bool) -> List<&2, Bool>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.Bool{}, graph, node)

def LexLeanCollections.graphSuccessors.Int8(graph: List<&2, L.Lean.Prod(Lean.Int8, List<&2, Lean.Int8>)>, node: Lean.Int8) -> List<&2, Lean.Int8>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.Int8{}, graph, node)

def LexLeanCollections.graphSuccessors.Int16(graph: List<&2, L.Lean.Prod(Lean.Int16, List<&2, Lean.Int16>)>, node: Lean.Int16) -> List<&2, Lean.Int16>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.Int16{}, graph, node)

def LexLeanCollections.graphSuccessors.Int32(graph: List<&2, L.Lean.Prod(Lean.Int32, List<&2, Lean.Int32>)>, node: Lean.Int32) -> List<&2, Lean.Int32>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.Int32{}, graph, node)

def LexLeanCollections.graphSuccessors.Int64(graph: List<&2, L.Lean.Prod(Lean.Int64, List<&2, Lean.Int64>)>, node: Lean.Int64) -> List<&2, Lean.Int64>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.Int64{}, graph, node)

def LexLeanCollections.graphSuccessors.UInt8(graph: List<&2, L.Lean.Prod(Lean.UInt8, List<&2, Lean.UInt8>)>, node: Lean.UInt8) -> List<&2, Lean.UInt8>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.UInt8{}, graph, node)

def LexLeanCollections.graphSuccessors.UInt16(graph: List<&2, L.Lean.Prod(Lean.UInt16, List<&2, Lean.UInt16>)>, node: Lean.UInt16) -> List<&2, Lean.UInt16>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.UInt16{}, graph, node)

def LexLeanCollections.graphSuccessors.UInt32(graph: List<&2, L.Lean.Prod(U32, List<&2, U32>)>, node: U32) -> List<&2, U32>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.UInt32{}, graph, node)

def LexLeanCollections.graphSuccessors.UInt64(graph: List<&2, L.Lean.Prod(Lean.UInt64, List<&2, Lean.UInt64>)>, node: Lean.UInt64) -> List<&2, Lean.UInt64>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.UInt64{}, graph, node)

def LexLeanCollections.graphSuccessors.String(graph: List<&2, L.Lean.Prod(String, List<&2, String>)>, node: String) -> List<&2, String>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.String{}, graph, node)

def LexLeanCollections.graphSuccessors.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, graph: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>)>, node: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>:
  LexLeanCollections.graphSuccessors.Key(LexLeanCollections.Key.Prod{ka, kb}, graph, node)

# xs.foldl (fun acc key => insertElement key acc) acc
def LexLeanCollections.insertAll(+k: LexLeanCollections.Key, xs: List<&2, LexLeanCollections.Key.carrier(k)>, acc: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  LexLeanCollections.setUnion.go(k, xs, acc)

def LexLeanCollections.graphNodes.go(+k: LexLeanCollections.Key, graph: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>)>, acc: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  match graph:
    case Nil{}:
      acc
    case Con{+entry, rest}:
      LexLeanCollections.graphNodes.go(k, rest, LexLeanCollections.insertAll(k, Lean.Prod.snd(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>, entry), LexLeanCollections.insertElement.Key(k, Lean.Prod.fst(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>, entry), acc)))

def LexLeanCollections.graphNodes.Key(+k: LexLeanCollections.Key, graph: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  LexLeanCollections.graphNodes.go(k, graph, Nil{})

def LexLeanCollections.graphNodes.Nat(graph: List<&2, L.Lean.Prod(Nat, List<&2, Nat>)>) -> List<&2, Nat>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.Nat{}, graph)

def LexLeanCollections.graphNodes.Int(graph: List<&2, L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>)>) -> List<&2, L.Lean.Int>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.Int{}, graph)

def LexLeanCollections.graphNodes.Bool(graph: List<&2, L.Lean.Prod(Bool, List<&2, Bool>)>) -> List<&2, Bool>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.Bool{}, graph)

def LexLeanCollections.graphNodes.Int8(graph: List<&2, L.Lean.Prod(Lean.Int8, List<&2, Lean.Int8>)>) -> List<&2, Lean.Int8>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.Int8{}, graph)

def LexLeanCollections.graphNodes.Int16(graph: List<&2, L.Lean.Prod(Lean.Int16, List<&2, Lean.Int16>)>) -> List<&2, Lean.Int16>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.Int16{}, graph)

def LexLeanCollections.graphNodes.Int32(graph: List<&2, L.Lean.Prod(Lean.Int32, List<&2, Lean.Int32>)>) -> List<&2, Lean.Int32>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.Int32{}, graph)

def LexLeanCollections.graphNodes.Int64(graph: List<&2, L.Lean.Prod(Lean.Int64, List<&2, Lean.Int64>)>) -> List<&2, Lean.Int64>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.Int64{}, graph)

def LexLeanCollections.graphNodes.UInt8(graph: List<&2, L.Lean.Prod(Lean.UInt8, List<&2, Lean.UInt8>)>) -> List<&2, Lean.UInt8>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.UInt8{}, graph)

def LexLeanCollections.graphNodes.UInt16(graph: List<&2, L.Lean.Prod(Lean.UInt16, List<&2, Lean.UInt16>)>) -> List<&2, Lean.UInt16>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.UInt16{}, graph)

def LexLeanCollections.graphNodes.UInt32(graph: List<&2, L.Lean.Prod(U32, List<&2, U32>)>) -> List<&2, U32>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.UInt32{}, graph)

def LexLeanCollections.graphNodes.UInt64(graph: List<&2, L.Lean.Prod(Lean.UInt64, List<&2, Lean.UInt64>)>) -> List<&2, Lean.UInt64>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.UInt64{}, graph)

def LexLeanCollections.graphNodes.String(graph: List<&2, L.Lean.Prod(String, List<&2, String>)>) -> List<&2, String>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.String{}, graph)

def LexLeanCollections.graphNodes.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, graph: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>)>) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>:
  LexLeanCollections.graphNodes.Key(LexLeanCollections.Key.Prod{ka, kb}, graph)

def LexLeanCollections.reach.inner(+k: LexLeanCollections.Key, succs: List<&2, LexLeanCollections.Key.carrier(k)>, +seen: List<&2, LexLeanCollections.Key.carrier(k)>, +acc: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  match succs:
    case Nil{}:
      acc
    case Con{+succ, rest}:
      LexLeanCollections.reach.inner(k, rest, seen, Bool.pick(List<&2, LexLeanCollections.Key.carrier(k)>, L.Lean.Bool.or(LexLeanCollections.containsElement.Key(k, succ, seen), LexLeanCollections.containsElement.Key(k, succ, acc)), acc, LexLeanCollections.insertElement.Key(k, succ, acc)))

def LexLeanCollections.reach.outer(+k: LexLeanCollections.Key, +graph: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>)>, frontier: List<&2, LexLeanCollections.Key.carrier(k)>, +seen: List<&2, LexLeanCollections.Key.carrier(k)>, acc: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  match frontier:
    case Nil{}:
      acc
    case Con{node, rest}:
      LexLeanCollections.reach.outer(k, graph, rest, seen, LexLeanCollections.reach.inner(k, LexLeanCollections.graphSuccessors.Key(k, graph, node), seen, acc))

def LexLeanCollections.reachableFrom.Key(+k: LexLeanCollections.Key, +graph: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>)>, fuel: Nat, frontier: List<&2, LexLeanCollections.Key.carrier(k)>, +seen: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  match fuel:
    case 0n:
      seen
    case 1n+f:
      +next = LexLeanCollections.reach.outer(k, graph, frontier, seen, Nil{})
      Bool.pick(List<&2, LexLeanCollections.Key.carrier(k)>, List.is_empty(&2, LexLeanCollections.Key.carrier(k), next), seen, LexLeanCollections.reachableFrom.Key(k, graph, f, next, LexLeanCollections.insertAll(k, next, seen)))

def LexLeanCollections.reachableFrom.Nat(graph: List<&2, L.Lean.Prod(Nat, List<&2, Nat>)>, fuel: Nat, frontier: List<&2, Nat>, seen: List<&2, Nat>) -> List<&2, Nat>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.Nat{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.Int(graph: List<&2, L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>)>, fuel: Nat, frontier: List<&2, L.Lean.Int>, seen: List<&2, L.Lean.Int>) -> List<&2, L.Lean.Int>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.Int{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.Bool(graph: List<&2, L.Lean.Prod(Bool, List<&2, Bool>)>, fuel: Nat, frontier: List<&2, Bool>, seen: List<&2, Bool>) -> List<&2, Bool>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.Bool{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.Int8(graph: List<&2, L.Lean.Prod(Lean.Int8, List<&2, Lean.Int8>)>, fuel: Nat, frontier: List<&2, Lean.Int8>, seen: List<&2, Lean.Int8>) -> List<&2, Lean.Int8>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.Int8{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.Int16(graph: List<&2, L.Lean.Prod(Lean.Int16, List<&2, Lean.Int16>)>, fuel: Nat, frontier: List<&2, Lean.Int16>, seen: List<&2, Lean.Int16>) -> List<&2, Lean.Int16>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.Int16{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.Int32(graph: List<&2, L.Lean.Prod(Lean.Int32, List<&2, Lean.Int32>)>, fuel: Nat, frontier: List<&2, Lean.Int32>, seen: List<&2, Lean.Int32>) -> List<&2, Lean.Int32>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.Int32{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.Int64(graph: List<&2, L.Lean.Prod(Lean.Int64, List<&2, Lean.Int64>)>, fuel: Nat, frontier: List<&2, Lean.Int64>, seen: List<&2, Lean.Int64>) -> List<&2, Lean.Int64>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.Int64{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.UInt8(graph: List<&2, L.Lean.Prod(Lean.UInt8, List<&2, Lean.UInt8>)>, fuel: Nat, frontier: List<&2, Lean.UInt8>, seen: List<&2, Lean.UInt8>) -> List<&2, Lean.UInt8>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.UInt8{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.UInt16(graph: List<&2, L.Lean.Prod(Lean.UInt16, List<&2, Lean.UInt16>)>, fuel: Nat, frontier: List<&2, Lean.UInt16>, seen: List<&2, Lean.UInt16>) -> List<&2, Lean.UInt16>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.UInt16{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.UInt32(graph: List<&2, L.Lean.Prod(U32, List<&2, U32>)>, fuel: Nat, frontier: List<&2, U32>, seen: List<&2, U32>) -> List<&2, U32>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.UInt32{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.UInt64(graph: List<&2, L.Lean.Prod(Lean.UInt64, List<&2, Lean.UInt64>)>, fuel: Nat, frontier: List<&2, Lean.UInt64>, seen: List<&2, Lean.UInt64>) -> List<&2, Lean.UInt64>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.UInt64{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.String(graph: List<&2, L.Lean.Prod(String, List<&2, String>)>, fuel: Nat, frontier: List<&2, String>, seen: List<&2, String>) -> List<&2, String>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.String{}, graph, fuel, frontier, seen)

def LexLeanCollections.reachableFrom.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, graph: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>)>, fuel: Nat, frontier: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>, seen: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>:
  LexLeanCollections.reachableFrom.Key(LexLeanCollections.Key.Prod{ka, kb}, graph, fuel, frontier, seen)

def LexLeanCollections.graphReachable.Key(+k: LexLeanCollections.Key, +graph: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>)>, +start: LexLeanCollections.Key.carrier(k)) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  LexLeanCollections.reachableFrom.Key(k, graph, L.Lean.Nat.add(L.Lean.List.length(LexLeanCollections.Key.carrier(k), LexLeanCollections.graphNodes.Key(k, graph)), 1n), [start], [start])

def LexLeanCollections.graphReachable.Nat(graph: List<&2, L.Lean.Prod(Nat, List<&2, Nat>)>, start: Nat) -> List<&2, Nat>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.Nat{}, graph, start)

def LexLeanCollections.graphReachable.Int(graph: List<&2, L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>)>, start: L.Lean.Int) -> List<&2, L.Lean.Int>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.Int{}, graph, start)

def LexLeanCollections.graphReachable.Bool(graph: List<&2, L.Lean.Prod(Bool, List<&2, Bool>)>, start: Bool) -> List<&2, Bool>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.Bool{}, graph, start)

def LexLeanCollections.graphReachable.Int8(graph: List<&2, L.Lean.Prod(Lean.Int8, List<&2, Lean.Int8>)>, start: Lean.Int8) -> List<&2, Lean.Int8>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.Int8{}, graph, start)

def LexLeanCollections.graphReachable.Int16(graph: List<&2, L.Lean.Prod(Lean.Int16, List<&2, Lean.Int16>)>, start: Lean.Int16) -> List<&2, Lean.Int16>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.Int16{}, graph, start)

def LexLeanCollections.graphReachable.Int32(graph: List<&2, L.Lean.Prod(Lean.Int32, List<&2, Lean.Int32>)>, start: Lean.Int32) -> List<&2, Lean.Int32>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.Int32{}, graph, start)

def LexLeanCollections.graphReachable.Int64(graph: List<&2, L.Lean.Prod(Lean.Int64, List<&2, Lean.Int64>)>, start: Lean.Int64) -> List<&2, Lean.Int64>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.Int64{}, graph, start)

def LexLeanCollections.graphReachable.UInt8(graph: List<&2, L.Lean.Prod(Lean.UInt8, List<&2, Lean.UInt8>)>, start: Lean.UInt8) -> List<&2, Lean.UInt8>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.UInt8{}, graph, start)

def LexLeanCollections.graphReachable.UInt16(graph: List<&2, L.Lean.Prod(Lean.UInt16, List<&2, Lean.UInt16>)>, start: Lean.UInt16) -> List<&2, Lean.UInt16>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.UInt16{}, graph, start)

def LexLeanCollections.graphReachable.UInt32(graph: List<&2, L.Lean.Prod(U32, List<&2, U32>)>, start: U32) -> List<&2, U32>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.UInt32{}, graph, start)

def LexLeanCollections.graphReachable.UInt64(graph: List<&2, L.Lean.Prod(Lean.UInt64, List<&2, Lean.UInt64>)>, start: Lean.UInt64) -> List<&2, Lean.UInt64>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.UInt64{}, graph, start)

def LexLeanCollections.graphReachable.String(graph: List<&2, L.Lean.Prod(String, List<&2, String>)>, start: String) -> List<&2, String>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.String{}, graph, start)

def LexLeanCollections.graphReachable.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, graph: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>)>, start: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))) -> List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>:
  LexLeanCollections.graphReachable.Key(LexLeanCollections.Key.Prod{ka, kb}, graph, start)

# if remaining.isEmpty then some order.reverse else none
def LexLeanCollections.topo.done(-K: Data, +remaining: List<&2, K>, order: List<&2, K>) -> Maybe<&2, List<&2, K>>:
  Bool.pick(Maybe<&2, List<&2, K>>, List.is_empty(&2, K, remaining), Some{List.reverse(&2, K, order)}, None{})

# remaining.all (fun other => !containsElement node (graphSuccessors graph other))
def LexLeanCollections.topo.free(+k: LexLeanCollections.Key, +graph: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>)>, +node: LexLeanCollections.Key.carrier(k), others: List<&2, LexLeanCollections.Key.carrier(k)>) -> Bool:
  match others:
    case Nil{}:
      True{}
    case Con{other, rest}:
      L.Lean.Bool.and(L.Lean.Bool.not(LexLeanCollections.containsElement.Key(k, node, LexLeanCollections.graphSuccessors.Key(k, graph, other))), LexLeanCollections.topo.free(k, graph, node, rest))

# remaining.filter (fun node => remaining.all ...)
def LexLeanCollections.topo.ready(+k: LexLeanCollections.Key, +graph: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>)>, candidates: List<&2, LexLeanCollections.Key.carrier(k)>, +remaining: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  match candidates:
    case Nil{}:
      Nil{}
    case Con{+node, rest}:
      LexLeanCollections.filter.put(LexLeanCollections.Key.carrier(k), LexLeanCollections.topo.free(k, graph, node, remaining), node, LexLeanCollections.topo.ready(k, graph, rest, remaining))

def LexLeanCollections.topo.nextRemaining(+k: LexLeanCollections.Key, ready: List<&2, LexLeanCollections.Key.carrier(k)>, remaining: List<&2, LexLeanCollections.Key.carrier(k)>) -> List<&2, LexLeanCollections.Key.carrier(k)>:
  match ready:
    case Nil{}:
      remaining
    case Con{r, rest}:
      LexLeanCollections.removeElement.Key(k, r, remaining)

def LexLeanCollections.topo.nextOrder(-K: Data, ready: List<&2, K>, order: List<&2, K>) -> List<&2, K>:
  match ready:
    case Nil{}:
      order
    case Con{r, rest}:
      Con{r, order}

def LexLeanCollections.topological.Key(+k: LexLeanCollections.Key, +graph: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>)>, fuel: Nat, +remaining: List<&2, LexLeanCollections.Key.carrier(k)>, +order: List<&2, LexLeanCollections.Key.carrier(k)>) -> Maybe<&2, List<&2, LexLeanCollections.Key.carrier(k)>>:
  match fuel:
    case 0n:
      LexLeanCollections.topo.done(LexLeanCollections.Key.carrier(k), remaining, order)
    case 1n+f:
      +ready = LexLeanCollections.topo.ready(k, graph, remaining, remaining)
      Bool.pick(Maybe<&2, List<&2, LexLeanCollections.Key.carrier(k)>>, List.is_empty(&2, LexLeanCollections.Key.carrier(k), ready), LexLeanCollections.topo.done(LexLeanCollections.Key.carrier(k), remaining, order), LexLeanCollections.topological.Key(k, graph, f, LexLeanCollections.topo.nextRemaining(k, ready, remaining), LexLeanCollections.topo.nextOrder(LexLeanCollections.Key.carrier(k), ready, order)))

def LexLeanCollections.topological.Nat(graph: List<&2, L.Lean.Prod(Nat, List<&2, Nat>)>, fuel: Nat, remaining: List<&2, Nat>, order: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.Nat{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.Int(graph: List<&2, L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>)>, fuel: Nat, remaining: List<&2, L.Lean.Int>, order: List<&2, L.Lean.Int>) -> Maybe<&2, List<&2, L.Lean.Int>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.Int{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.Bool(graph: List<&2, L.Lean.Prod(Bool, List<&2, Bool>)>, fuel: Nat, remaining: List<&2, Bool>, order: List<&2, Bool>) -> Maybe<&2, List<&2, Bool>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.Bool{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.Int8(graph: List<&2, L.Lean.Prod(Lean.Int8, List<&2, Lean.Int8>)>, fuel: Nat, remaining: List<&2, Lean.Int8>, order: List<&2, Lean.Int8>) -> Maybe<&2, List<&2, Lean.Int8>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.Int8{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.Int16(graph: List<&2, L.Lean.Prod(Lean.Int16, List<&2, Lean.Int16>)>, fuel: Nat, remaining: List<&2, Lean.Int16>, order: List<&2, Lean.Int16>) -> Maybe<&2, List<&2, Lean.Int16>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.Int16{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.Int32(graph: List<&2, L.Lean.Prod(Lean.Int32, List<&2, Lean.Int32>)>, fuel: Nat, remaining: List<&2, Lean.Int32>, order: List<&2, Lean.Int32>) -> Maybe<&2, List<&2, Lean.Int32>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.Int32{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.Int64(graph: List<&2, L.Lean.Prod(Lean.Int64, List<&2, Lean.Int64>)>, fuel: Nat, remaining: List<&2, Lean.Int64>, order: List<&2, Lean.Int64>) -> Maybe<&2, List<&2, Lean.Int64>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.Int64{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.UInt8(graph: List<&2, L.Lean.Prod(Lean.UInt8, List<&2, Lean.UInt8>)>, fuel: Nat, remaining: List<&2, Lean.UInt8>, order: List<&2, Lean.UInt8>) -> Maybe<&2, List<&2, Lean.UInt8>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.UInt8{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.UInt16(graph: List<&2, L.Lean.Prod(Lean.UInt16, List<&2, Lean.UInt16>)>, fuel: Nat, remaining: List<&2, Lean.UInt16>, order: List<&2, Lean.UInt16>) -> Maybe<&2, List<&2, Lean.UInt16>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.UInt16{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.UInt32(graph: List<&2, L.Lean.Prod(U32, List<&2, U32>)>, fuel: Nat, remaining: List<&2, U32>, order: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.UInt32{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.UInt64(graph: List<&2, L.Lean.Prod(Lean.UInt64, List<&2, Lean.UInt64>)>, fuel: Nat, remaining: List<&2, Lean.UInt64>, order: List<&2, Lean.UInt64>) -> Maybe<&2, List<&2, Lean.UInt64>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.UInt64{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.String(graph: List<&2, L.Lean.Prod(String, List<&2, String>)>, fuel: Nat, remaining: List<&2, String>, order: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.String{}, graph, fuel, remaining, order)

def LexLeanCollections.topological.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, graph: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>)>, fuel: Nat, remaining: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>, order: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>) -> Maybe<&2, List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>>:
  LexLeanCollections.topological.Key(LexLeanCollections.Key.Prod{ka, kb}, graph, fuel, remaining, order)

def LexLeanCollections.graphTopological.Key(+k: LexLeanCollections.Key, +graph: List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(k), List<&2, LexLeanCollections.Key.carrier(k)>)>) -> Maybe<&2, List<&2, LexLeanCollections.Key.carrier(k)>>:
  +nodes = LexLeanCollections.graphNodes.Key(k, graph)
  LexLeanCollections.topological.Key(k, graph, L.Lean.Nat.add(L.Lean.List.length(LexLeanCollections.Key.carrier(k), nodes), 1n), nodes, Nil{})

def LexLeanCollections.graphTopological.Nat(graph: List<&2, L.Lean.Prod(Nat, List<&2, Nat>)>) -> Maybe<&2, List<&2, Nat>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.Nat{}, graph)

def LexLeanCollections.graphTopological.Int(graph: List<&2, L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>)>) -> Maybe<&2, List<&2, L.Lean.Int>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.Int{}, graph)

def LexLeanCollections.graphTopological.Bool(graph: List<&2, L.Lean.Prod(Bool, List<&2, Bool>)>) -> Maybe<&2, List<&2, Bool>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.Bool{}, graph)

def LexLeanCollections.graphTopological.Int8(graph: List<&2, L.Lean.Prod(Lean.Int8, List<&2, Lean.Int8>)>) -> Maybe<&2, List<&2, Lean.Int8>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.Int8{}, graph)

def LexLeanCollections.graphTopological.Int16(graph: List<&2, L.Lean.Prod(Lean.Int16, List<&2, Lean.Int16>)>) -> Maybe<&2, List<&2, Lean.Int16>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.Int16{}, graph)

def LexLeanCollections.graphTopological.Int32(graph: List<&2, L.Lean.Prod(Lean.Int32, List<&2, Lean.Int32>)>) -> Maybe<&2, List<&2, Lean.Int32>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.Int32{}, graph)

def LexLeanCollections.graphTopological.Int64(graph: List<&2, L.Lean.Prod(Lean.Int64, List<&2, Lean.Int64>)>) -> Maybe<&2, List<&2, Lean.Int64>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.Int64{}, graph)

def LexLeanCollections.graphTopological.UInt8(graph: List<&2, L.Lean.Prod(Lean.UInt8, List<&2, Lean.UInt8>)>) -> Maybe<&2, List<&2, Lean.UInt8>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.UInt8{}, graph)

def LexLeanCollections.graphTopological.UInt16(graph: List<&2, L.Lean.Prod(Lean.UInt16, List<&2, Lean.UInt16>)>) -> Maybe<&2, List<&2, Lean.UInt16>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.UInt16{}, graph)

def LexLeanCollections.graphTopological.UInt32(graph: List<&2, L.Lean.Prod(U32, List<&2, U32>)>) -> Maybe<&2, List<&2, U32>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.UInt32{}, graph)

def LexLeanCollections.graphTopological.UInt64(graph: List<&2, L.Lean.Prod(Lean.UInt64, List<&2, Lean.UInt64>)>) -> Maybe<&2, List<&2, Lean.UInt64>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.UInt64{}, graph)

def LexLeanCollections.graphTopological.String(graph: List<&2, L.Lean.Prod(String, List<&2, String>)>) -> Maybe<&2, List<&2, String>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.String{}, graph)

def LexLeanCollections.graphTopological.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, graph: List<&2, L.Lean.Prod(L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>)>) -> Maybe<&2, List<&2, L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))>>:
  LexLeanCollections.graphTopological.Key(LexLeanCollections.Key.Prod{ka, kb}, graph)

def LexLeanCollections.lessThan.Key(+k: LexLeanCollections.Key, left: LexLeanCollections.Key.carrier(k), right: LexLeanCollections.Key.carrier(k)) -> Bool:
  Cmp.is_lt(LexLeanCollections.Key.compare(k, left, right))

def LexLeanCollections.lessThan.Nat(left: Nat, right: Nat) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.Nat{}, left, right)

def LexLeanCollections.lessThan.Int(left: L.Lean.Int, right: L.Lean.Int) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.Int{}, left, right)

def LexLeanCollections.lessThan.Bool(left: Bool, right: Bool) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.Bool{}, left, right)

def LexLeanCollections.lessThan.Int8(left: Lean.Int8, right: Lean.Int8) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.Int8{}, left, right)

def LexLeanCollections.lessThan.Int16(left: Lean.Int16, right: Lean.Int16) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.Int16{}, left, right)

def LexLeanCollections.lessThan.Int32(left: Lean.Int32, right: Lean.Int32) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.Int32{}, left, right)

def LexLeanCollections.lessThan.Int64(left: Lean.Int64, right: Lean.Int64) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.Int64{}, left, right)

def LexLeanCollections.lessThan.UInt8(left: Lean.UInt8, right: Lean.UInt8) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.UInt8{}, left, right)

def LexLeanCollections.lessThan.UInt16(left: Lean.UInt16, right: Lean.UInt16) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.UInt16{}, left, right)

def LexLeanCollections.lessThan.UInt32(left: U32, right: U32) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.UInt32{}, left, right)

def LexLeanCollections.lessThan.UInt64(left: Lean.UInt64, right: Lean.UInt64) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.UInt64{}, left, right)

def LexLeanCollections.lessThan.String(left: String, right: String) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.String{}, left, right)

def LexLeanCollections.lessThan.Prod(ka: LexLeanCollections.Key, kb: LexLeanCollections.Key, left: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb)), right: L.Lean.Prod(LexLeanCollections.Key.carrier(ka), LexLeanCollections.Key.carrier(kb))) -> Bool:
  LexLeanCollections.lessThan.Key(LexLeanCollections.Key.Prod{ka, kb}, left, right)

# ---------------------------------------------------------------------------
# LexLeanModels. A Lean Prop is a Bend Type; these defs return Types, so their
# bodies are checked dead and may mention a function argument many times.
# ---------------------------------------------------------------------------

def LexLeanModels.Sound1(-A: Type, v: A -> Bool, p: A -> Type) -> Type:
  @a: A -> {v(a) == True{} : Bool} -> p(a)

def LexLeanModels.Sound2(-A: Type, -B: Type, v: A -> B -> Bool, p: A -> B -> Type) -> Type:
  @a: A -> @b: B -> {v(a, b) == True{} : Bool} -> p(a, b)

def LexLeanModels.Sound4(-A: Type, -B: Type, -C: Type, -D: Type, v: A -> B -> C -> D -> Bool, p: A -> B -> C -> D -> Type) -> Type:
  @a: A -> @b: B -> @c: C -> @d: D -> {v(a, b, c, d) == True{} : Bool} -> p(a, b, c, d)

def LexLeanModels.Complete1(-A: Type, v: A -> Bool, p: A -> Type) -> Type:
  @a: A -> p(a) -> {v(a) == True{} : Bool}

def LexLeanModels.Complete2(-A: Type, -B: Type, v: A -> B -> Bool, p: A -> B -> Type) -> Type:
  @a: A -> @b: B -> p(a, b) -> {v(a, b) == True{} : Bool}

def LexLeanModels.Complete4(-A: Type, -B: Type, -C: Type, -D: Type, v: A -> B -> C -> D -> Bool, p: A -> B -> C -> D -> Type) -> Type:
  @a: A -> @b: B -> @c: C -> @d: D -> p(a, b, c, d) -> {v(a, b, c, d) == True{} : Bool}

def LexLeanModels.Satisfies(-A: Type, -B: Type, p: A -> Type, q: A -> B -> Type, r: A -> B) -> Type:
  @a: A -> p(a) -> q(a, r(a))

def LexLeanModels.SatisfiesTotal(-A: Type, -B: Type, q: A -> B -> Type, r: A -> B) -> Type:
  @a: A -> q(a, r(a))

def LexLeanModels.SatisfiesStep(-S: Data, -A: Type, -B: Data, j: S -> Type, p: S -> A -> Type, q: S -> A -> S -> B -> Type, r: S -> A -> L.Lean.Prod(S, B)) -> Type:
  @s: S -> @a: A -> j(s) -> p(s, a) -> q(s, a, Lean.Prod.fst(S, B, r(s, a)), Lean.Prod.snd(S, B, r(s, a)))

def LexLeanModels.SatisfiesStepNoInvariant(-S: Data, -A: Type, -B: Data, p: S -> A -> Type, q: S -> A -> S -> B -> Type, r: S -> A -> L.Lean.Prod(S, B)) -> Type:
  @s: S -> @a: A -> p(s, a) -> q(s, a, Lean.Prod.fst(S, B, r(s, a)), Lean.Prod.snd(S, B, r(s, a)))

def LexLeanModels.SatisfiesStepNoPrecondition(-S: Data, -A: Type, -B: Data, j: S -> Type, q: S -> A -> S -> B -> Type, r: S -> A -> L.Lean.Prod(S, B)) -> Type:
  @s: S -> @a: A -> j(s) -> q(s, a, Lean.Prod.fst(S, B, r(s, a)), Lean.Prod.snd(S, B, r(s, a)))

def LexLeanModels.SatisfiesStepTotal(-S: Data, -A: Type, -B: Data, q: S -> A -> S -> B -> Type, r: S -> A -> L.Lean.Prod(S, B)) -> Type:
  @s: S -> @a: A -> q(s, a, Lean.Prod.fst(S, B, r(s, a)), Lean.Prod.snd(S, B, r(s, a)))

def LexLeanModels.Preserves(-S: Data, -A: Type, -B: Data, j: S -> Type, p: S -> A -> Type, r: S -> A -> L.Lean.Prod(S, B)) -> Type:
  @s: S -> @a: A -> j(s) -> p(s, a) -> j(Lean.Prod.fst(S, B, r(s, a)))

def LexLeanModels.PreservesTotal(-S: Data, -A: Type, -B: Data, j: S -> Type, r: S -> A -> L.Lean.Prod(S, B)) -> Type:
  @s: S -> @a: A -> j(s) -> j(Lean.Prod.fst(S, B, r(s, a)))

def LexLeanModels.Initial(-S: Type, j: S -> Type, i: S) -> Type:
  j(i)

def LexLeanModels.Equivalent(-A: Type, -B: Type, p: A -> Type, r: A -> B, f: A -> B) -> Type:
  @a: A -> p(a) -> {r(a) == f(a) : B}

def LexLeanModels.EquivalentTotal(-A: Type, -B: Type, r: A -> B, f: A -> B) -> Type:
  @a: A -> {r(a) == f(a) : B}

def LexLeanModels.EquivalentStep(-S: Data, -A: Type, -B: Data, j: S -> Type, p: S -> A -> Type, r: S -> A -> L.Lean.Prod(S, B), f: S -> A -> L.Lean.Prod(S, B)) -> Type:
  @s: S -> @a: A -> j(s) -> p(s, a) -> {r(s, a) == f(s, a) : L.Lean.Prod(S, B)}

def LexLeanModels.EquivalentStepNoInvariant(-S: Data, -A: Type, -B: Data, p: S -> A -> Type, r: S -> A -> L.Lean.Prod(S, B), f: S -> A -> L.Lean.Prod(S, B)) -> Type:
  @s: S -> @a: A -> p(s, a) -> {r(s, a) == f(s, a) : L.Lean.Prod(S, B)}

def LexLeanModels.EquivalentStepNoPrecondition(-S: Data, -A: Type, -B: Data, j: S -> Type, r: S -> A -> L.Lean.Prod(S, B), f: S -> A -> L.Lean.Prod(S, B)) -> Type:
  @s: S -> @a: A -> j(s) -> {r(s, a) == f(s, a) : L.Lean.Prod(S, B)}

def LexLeanModels.EquivalentStepTotal(-S: Data, -A: Type, -B: Data, r: S -> A -> L.Lean.Prod(S, B), f: S -> A -> L.Lean.Prod(S, B)) -> Type:
  @s: S -> @a: A -> {r(s, a) == f(s, a) : L.Lean.Prod(S, B)}

# d.foldl (fun c e => if cmp (r e.1) e.2 then c + 1 else c) c = n, unfolded
# along d: the fold's value is not computed by live code (r and cmp are
# closures, usable once), so the equation is a Type indexed by the accumulator.
def LexLeanModels.Agreement.count(-A: Data, -B: Data, -r: A -> B, -cmp: B -> B -> Bool, d: List<&2, L.Lean.Prod(A, B)>, -c: Nat, -n: Nat) -> Type:
  match d:
    case Nil{}:
      {c == n : Nat}
    case Con{+e, t}:
      LexLeanModels.Agreement.count(A, B, r, cmp, t, Bool.pick(Nat, cmp(r(Lean.Prod.fst(A, B, e)), Lean.Prod.snd(A, B, e)), L.Lean.Nat.add(c, 1n), c), n)

def LexLeanModels.Agreement(-A: Data, -B: Data, r: A -> B, cmp: B -> B -> Bool, d: List<&2, L.Lean.Prod(A, B)>, examples: Nat, agreements: Nat) -> Type:
  {L.Lean.List.length(L.Lean.Prod(A, B), d) == examples : Nat} & LexLeanModels.Agreement.count(A, B, r, cmp, d, 0n, agreements)

# if signed then -(2^(8w-1)) <= value && value < 2^(8w-1) else 0 <= value && value < 2^(8w)
def LexLeanModels.inRange(+width: Nat, signed: Bool, value: L.Lean.Int) -> Bool:
  match signed:
    case True{}:
      match value:
        case L.ofNat{n}:
          LexLeanRuntime.Nat.ltPow2(L.Lean.Nat.sub(L.Lean.Nat.mul(8n, width), 1n), n)
        case L.negSucc{m}:
          LexLeanRuntime.Nat.ltPow2(L.Lean.Nat.sub(L.Lean.Nat.mul(8n, width), 1n), m)
    case False{}:
      match value:
        case L.ofNat{n}:
          LexLeanRuntime.Nat.ltPow2(L.Lean.Nat.mul(8n, width), n)
        case L.negSucc{m}:
          False{}

# (List.range width).map (fun i => (n / 256 ^ i) % 256)
def LexLeanModels.encodeInt.bytes(width: Nat, +n: Nat) -> List<&2, Nat>:
  match width:
    case 0n:
      Nil{}
    case 1n+p:
      Con{L.Lean.Nat.mod(n, 256n), LexLeanModels.encodeInt.bytes(p, L.Lean.Nat.div(n, 256n))}

def LexLeanModels.encodeInt.complement(bs: List<&2, Nat>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, rest}:
      Con{L.Lean.Nat.sub(255n, b), LexLeanModels.encodeInt.complement(rest)}

def LexLeanModels.encodeInt.zeros(width: Nat) -> List<&2, Nat>:
  match width:
    case 0n:
      Nil{}
    case 1n+p:
      Con{0n, LexLeanModels.encodeInt.zeros(p)}

# unsigned := if value < 0 then value + 2^(8w) else value; the bytes of
# unsigned.toNat, little-endian. For value = -(m + 1) with m < 2^(8w) these are
# the complemented bytes of m; below -2^(8w), toNat clamps to 0.
def LexLeanModels.encodeInt(+width: Nat, value: L.Lean.Int) -> List<&2, Nat>:
  match value:
    case L.ofNat{n}:
      LexLeanModels.encodeInt.bytes(width, n)
    case L.negSucc{+m}:
      Bool.pick(List<&2, Nat>, LexLeanRuntime.Nat.ltPow2(L.Lean.Nat.mul(8n, width), m), LexLeanModels.encodeInt.complement(LexLeanModels.encodeInt.bytes(width, m)), LexLeanModels.encodeInt.zeros(width))

def LexLeanModels.natListBeq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{bh, bt}:
      False{}
    case Con{ah, at} Nil{}:
      False{}
    case Con{ah, at} Con{bh, bt}:
      L.Lean.Bool.and(L.Lean.Nat.beq(ah, bh), LexLeanModels.natListBeq(at, bt))

def LexLeanModels.byteNats(bs: List<&2, Lean.UInt8>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, rest}:
      Con{Lean.UInt8.toNat(b), LexLeanModels.byteNats(rest)}

def LexLeanModels.tensorMatches.allInRange(+width: Nat, +signed: Bool, values: List<&2, L.Lean.Int>) -> Bool:
  match values:
    case Nil{}:
      True{}
    case Con{v, rest}:
      L.Lean.Bool.and(LexLeanModels.inRange(width, signed, v), LexLeanModels.tensorMatches.allInRange(width, signed, rest))

def LexLeanModels.tensorMatches.flat(+width: Nat, values: List<&2, L.Lean.Int>) -> List<&2, Nat>:
  match values:
    case Nil{}:
      Nil{}
    case Con{v, rest}:
      L.Lean.List.append(Nat, LexLeanModels.encodeInt(width, v), LexLeanModels.tensorMatches.flat(width, rest))

# values.all (inRange width signed) && values.flatMap (encodeInt width) == bytes.data.toList.map UInt8.toNat
def LexLeanModels.tensorMatches(+width: Nat, signed: Bool, +values: List<&2, L.Lean.Int>, bytes: Lean.ByteArray) -> Bool:
  L.Lean.Bool.and(LexLeanModels.tensorMatches.allInRange(width, signed, values), LexLeanModels.natListBeq(LexLeanModels.tensorMatches.flat(width, values), LexLeanModels.byteNats(Lean.ByteArray.data(bytes))))

# The UTF-8 bytes of c.toNat, computed in U32 (every intermediate is below 2^32).
def LexLeanModels.utf8Char(c: Char) -> List<&2, Nat>:
  +n = Char.to_u32(c)
  Bool.pick(List<&2, Nat>, U32.is_lt(n, 128), [U32.to_nat(n)], Bool.pick(List<&2, Nat>, U32.is_lt(n, 2048), [U32.to_nat(U32.add(192, U32.div(n, 64))), U32.to_nat(U32.add(128, U32.mod(n, 64)))], Bool.pick(List<&2, Nat>, U32.is_lt(n, 65536), [U32.to_nat(U32.add(224, U32.div(n, 4096))), U32.to_nat(U32.add(128, U32.mod(U32.div(n, 64), 64))), U32.to_nat(U32.add(128, U32.mod(n, 64)))], [U32.to_nat(U32.add(240, U32.div(n, 262144))), U32.to_nat(U32.add(128, U32.mod(U32.div(n, 4096), 64))), U32.to_nat(U32.add(128, U32.mod(U32.div(n, 64), 64))), U32.to_nat(U32.add(128, U32.mod(n, 64)))])))

# c.toNat != 10 && c.toNat != 13
def LexLeanModels.linesMatch.ok(+v: U32) -> Bool:
  L.Lean.Bool.and(L.Lean.Bool.not(U32.is_eq(v, 10)), L.Lean.Bool.not(U32.is_eq(v, 13)))

def LexLeanModels.linesMatch.clean(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      L.Lean.Bool.and(LexLeanModels.linesMatch.ok(Char.to_u32(c)), LexLeanModels.linesMatch.clean(t))

def LexLeanModels.linesMatch.allClean(lines: List<&2, String>) -> Bool:
  match lines:
    case Nil{}:
      True{}
    case Con{l, rest}:
      L.Lean.Bool.and(LexLeanModels.linesMatch.clean(l), LexLeanModels.linesMatch.allClean(rest))

def LexLeanModels.linesMatch.line(s: String) -> List<&2, Nat>:
  match s:
    case SNil{}:
      [10n]
    case SCon{c, t}:
      L.Lean.List.append(Nat, LexLeanModels.utf8Char(c), LexLeanModels.linesMatch.line(t))

def LexLeanModels.linesMatch.all(lines: List<&2, String>) -> List<&2, Nat>:
  match lines:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      L.Lean.List.append(Nat, LexLeanModels.linesMatch.line(l), LexLeanModels.linesMatch.all(rest))

def LexLeanModels.linesMatch(+lines: List<&2, String>, bytes: Lean.ByteArray) -> Bool:
  L.Lean.Bool.and(LexLeanModels.linesMatch.allClean(lines), LexLeanModels.natListBeq(LexLeanModels.linesMatch.all(lines), LexLeanModels.byteNats(Lean.ByteArray.data(bytes))))

# ---------------------------------------------------------------------------
# LexLeanReasoning. Lean's `if g then a else b` on a Bool is Base's
# Bool.pick(T, g, a, b) (a when g is true); a lemma whose statement has an
# `if` applies where the backend lowers that `if` through Bool.pick.
# Lean `True` is Unit and `True.intro` is Unit{}.
# ---------------------------------------------------------------------------

# Star r a c: the reflexive-transitive closure of r, extended on the right.
type LexLeanReasoning.Star<-S: Type, -r: S -> S -> Type, -a: S, -c: S> is Type:
  LexLeanReasoning.Star.refl.mk{e: {a == c : S}}
  LexLeanReasoning.Star.tail.mk{b: S, h: LexLeanReasoning.Star<S, r, a, b>, s: r(b, c)}

def LexLeanReasoning.Star.refl(-S: Type, -r: S -> S -> Type, a: S) -> LexLeanReasoning.Star<S, r, a, a>:
  LexLeanReasoning.Star.refl.mk{{==}}

def LexLeanReasoning.Star.tail(-S: Type, -r: S -> S -> Type, -a: S, b: S, -c: S, h: LexLeanReasoning.Star<S, r, a, b>, s: r(b, c)) -> LexLeanReasoning.Star<S, r, a, c>:
  LexLeanReasoning.Star.tail.mk{b, h, s}

# All p xs: p holds of every element; Lean's inductive predicate, as the
# conjunction it unfolds to (All.nil is Unit{}, All.cons is a pair).
def LexLeanReasoning.All(-A: Data, p: A -> Type, xs: List<&2, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{h, t}:
      p(h) & LexLeanReasoning.All(A, p, t)

def LexLeanReasoning.All.nil(-A: Data, -p: A -> Type) -> LexLeanReasoning.All(A, p, Nil{}):
  Unit{}

def LexLeanReasoning.All.cons(-A: Data, -p: A -> Type, -a: A, -rest: List<&2, A>, h1: p(a), h2: LexLeanReasoning.All(A, p, rest)) -> LexLeanReasoning.All(A, p, Con{a, rest}):
  (h1, h2)

def LexLeanReasoning.Preserves(-S: Type, r: S -> S -> Type, j: S -> Type) -> Type:
  @s: S -> @t: S -> j(s) -> r(s, t) -> j(t)

def LexLeanReasoning.Sound(-A: Type, -B: Type, v: A -> B -> Bool, p: A -> B -> Type) -> Type:
  @a: A -> @b: B -> {v(a, b) == True{} : Bool} -> p(a, b)

def LexLeanReasoning.Complete(-A: Type, -B: Type, v: A -> B -> Bool, p: A -> B -> Type) -> Type:
  @a: A -> @b: B -> p(a, b) -> {v(a, b) == True{} : Bool}

def LexLeanReasoning.Reaches(-S: Data, -E: Data, r: S -> S -> Type, a: S, acc: Result<&2, &2, E, S>) -> Type:
  @s: S -> {acc == Done{s} : Result<&2, &2, E, S>} -> LexLeanReasoning.Star<S, r, a, s>

def LexLeanReasoning.Found(-N: Data, -R: Data, ok: N -> Type, accept: N -> Maybe<&2, R>, found: Maybe<&2, L.Lean.Prod(R, N)>) -> Type:
  match found:
    case None{}:
      Unit
    case Some{hit}:
      ok(Lean.Prod.snd(R, N, hit)) & {accept(Lean.Prod.snd(R, N, hit)) == Some{Lean.Prod.fst(R, N, hit)} : Maybe<&2, R>}

def LexLeanReasoning.SearchOk(-N: Data, -R: Data, ok: N -> Type, accept: N -> Maybe<&2, R>, frontier: List<&2, N>, found: Maybe<&2, L.Lean.Prod(R, N)>) -> Type:
  LexLeanReasoning.All(N, ok, frontier) & LexLeanReasoning.Found(N, R, ok, accept, found)

# Motives for refuting none = some v.
def LexLeanReasoning.someDisc(-S: Data, m: Maybe<&2, S>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def LexLeanReasoning.noneNeSome(-S: Data, -v: S, e: {None{} == Some{v} : Maybe<&2, S>}) -> Empty:
  %e : LexLeanReasoning.someDisc(S, _)
  Unit{}

def LexLeanReasoning.someValue(-S: Data, d: S, m: Maybe<&2, S>) -> S:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def LexLeanReasoning.doneValue(-E: Data, -S: Data, d: S, m: Result<&2, &2, E, S>) -> S:
  match m:
    case Fail{x}:
      d
    case Done{x}:
      x

# Some a = Some b gives a = b.
def LexLeanReasoning.someInj(-S: Data, +a: S, -b: S, e: {Some{a} == Some{b} : Maybe<&2, S>}) -> {a == b : S}:
  Equal.cong(Maybe<&2, S>, S, m => LexLeanReasoning.someValue(S, a, m), Some{a}, Some{b}, e)

def LexLeanReasoning.guarded.go(-S: Data, -r: S -> S -> Type, -s: S, -c: S, -t: S, h: r(s, c), ct: {c == t : S}) -> r(s, t):
  %ct : r(s, _)
  h

def LexLeanReasoning.guardedRank.go(-S: Data, -mu: S -> Nat, -s: S, -c: S, -t: S, h: L.Lean.Nat.lt(mu(c), mu(s)), ct: {c == t : S}) -> L.Lean.Nat.lt(mu(t), mu(s)):
  %ct : L.Lean.Nat.lt(mu(_), mu(s))
  h

def LexLeanReasoning.peakBound.go(b: Bool, -p: Nat, -len: Nat, -k: Nat, hp: L.Lean.Nat.le(p, k), hl: L.Lean.Nat.le(len, k)) -> L.Lean.Nat.le(Bool.pick(Nat, b, len, p), k):
  match b:
    case True{}:
      hl
    case False{}:
      hp

law LexLeanReasoning.reachesStart:
  for -S: Data
  for -E: Data
  for r: S -> S -> Type
  for +a: S
  LexLeanReasoning.Reaches(S, E, r, a, Done{a})

def LexLeanReasoning.reachesStart(S, E, r, a):
  s => e => LexLeanReasoning.Star.refl.mk{Equal.cong(Result<&2, &2, E, S>, S, m => LexLeanReasoning.doneValue(E, S, a, m), Done{a}, Done{s}, e)}

law LexLeanReasoning.guarded:
  for -S: Data
  for r: S -> S -> Type
  for s: S
  for g: Bool
  for +c: S
  for h: {g == True{} : Bool} -> r(s, c)
  for t: S
  {Bool.pick(Maybe<&2, S>, g, Some{c}, None{}) == Some{t} : Maybe<&2, S>} -> r(s, t)

def LexLeanReasoning.guarded(S, r, s, g, c, h, t):
  match g:
    case False{}:
      e => L.Lean.Empty.elim(r(s, t), LexLeanReasoning.noneNeSome(S, t, e))
    case True{}:
      e => LexLeanReasoning.guarded.go(S, r, s, c, t, h({==}), LexLeanReasoning.someInj(S, c, t, e))

law LexLeanReasoning.guardedRank:
  for -S: Data
  for mu: S -> Nat
  for s: S
  for g: Bool
  for +c: S
  for h: {g == True{} : Bool} -> L.Lean.Nat.lt(mu(c), mu(s))
  for t: S
  {Bool.pick(Maybe<&2, S>, g, Some{c}, None{}) == Some{t} : Maybe<&2, S>} -> L.Lean.Nat.lt(mu(t), mu(s))

def LexLeanReasoning.guardedRank(S, mu, s, g, c, h, t):
  match g:
    case False{}:
      e => L.Lean.Empty.elim(L.Lean.Nat.lt(mu(t), mu(s)), LexLeanReasoning.noneNeSome(S, t, e))
    case True{}:
      e => LexLeanReasoning.guardedRank.go(S, mu, s, c, t, h({==}), LexLeanReasoning.someInj(S, c, t, e))

law LexLeanReasoning.checked:
  for -R: Data
  for g: Bool
  for +a: R
  for b: R
  {Bool.pick(Maybe<&2, R>, g, Some{a}, None{}) == Some{b} : Maybe<&2, R>} -> {g == True{} : Bool} & {a == b : R}

def LexLeanReasoning.checked(R, g, a, b):
  match g:
    case False{}:
      e => L.Lean.Empty.elim({False{} == True{} : Bool} & {a == b : R}, LexLeanReasoning.noneNeSome(R, b, e))
    case True{}:
      e => ({==}, LexLeanReasoning.someInj(R, a, b, e))

law LexLeanReasoning.allAppend:
  for -A: Data
  for p: A -> Type
  for xs: List<&2, A>
  for ys: List<&2, A>
  for hx: LexLeanReasoning.All(A, p, xs)
  for hy: LexLeanReasoning.All(A, p, ys)
  LexLeanReasoning.All(A, p, LexLeanRuntime.append.List(A, xs, ys))

def LexLeanReasoning.allAppend(A, p, xs, ys, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{x, rest}:
      (hp, hr) = hx
      (hp, LexLeanReasoning.allAppend(A, p, rest, ys, hr, hy))

law LexLeanReasoning.allSingle:
  for -A: Data
  for p: A -> Type
  for a: A
  for h: p(a)
  LexLeanReasoning.All(A, p, Con{a, Nil{}})

def LexLeanReasoning.allSingle(A, p, a, h):
  (h, Unit{})

law LexLeanReasoning.allHead:
  for -A: Data
  for p: A -> Type
  for a: A
  for rest: List<&2, A>
  for h: LexLeanReasoning.All(A, p, Con{a, rest})
  p(a)

def LexLeanReasoning.allHead(A, p, a, rest, h):
  (hp, hr) = h
  hp

law LexLeanReasoning.allTail:
  for -A: Data
  for p: A -> Type
  for a: A
  for rest: List<&2, A>
  for h: LexLeanReasoning.All(A, p, Con{a, rest})
  LexLeanReasoning.All(A, p, rest)

def LexLeanReasoning.allTail(A, p, a, rest, h):
  (hp, hr) = h
  hr

law LexLeanReasoning.lengthSnoc:
  for -A: Data
  for xs: List<&2, A>
  for y: A
  {LexLeanRuntime.length.List(A, LexLeanRuntime.append.List(A, xs, Con{y, Nil{}})) == L.Lean.Nat.add(LexLeanRuntime.length.List(A, xs), 1n) : Nat}

def LexLeanReasoning.lengthSnoc(A, xs, y):
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      %LexLeanReasoning.lengthSnoc(A, rest, y) : {L.Lean.Nat.add(LexLeanRuntime.length.List(A, LexLeanRuntime.append.List(A, rest, Con{y, Nil{}})), 1n) == L.Lean.Nat.add(_, 1n) : Nat}
      {==}

law LexLeanReasoning.searchStart:
  for -N: Data
  for -R: Data
  for ok: N -> Type
  for accept: N -> Maybe<&2, R>
  for frontier: List<&2, N>
  for h: LexLeanReasoning.All(N, ok, frontier)
  LexLeanReasoning.SearchOk(N, R, ok, accept, frontier, None{})

def LexLeanReasoning.searchStart(N, R, ok, accept, frontier, h):
  (h, Unit{})

law LexLeanReasoning.peakBound:
  for p: Nat
  for len: Nat
  for k: Nat
  for hp: L.Lean.Nat.le(p, k)
  for hl: L.Lean.Nat.le(len, k)
  L.Lean.Nat.le(Bool.pick(Nat, L.Lean.Nat.blt(p, len), len, p), k)

def LexLeanReasoning.peakBound(p, len, k, hp, hl):
  LexLeanReasoning.peakBound.go(L.Lean.Nat.blt(p, len), p, len, k, hp, hl)

law LexLeanReasoning.noneSome:
  for -R: Data
  for -q: Type
  for v: R
  for h: {None{} == Some{v} : Maybe<&2, R>}
  q

def LexLeanReasoning.noneSome(R, q, v, h):
  L.Lean.Empty.elim(q, LexLeanReasoning.noneNeSome(R, v, h))

law LexLeanReasoning.zeroLe:
  for n: Nat
  L.Lean.Nat.le(0n, n)

def LexLeanReasoning.zeroLe(n):
  {==}

law LexLeanReasoning.bltSucc:
  for a: Nat
  for b: Nat
  for h: {L.Lean.Nat.blt(a, b) == True{} : Bool}
  L.Lean.Nat.le(L.Lean.Nat.add(a, 1n), b)

def LexLeanReasoning.bltSucc(a, b, h):
  h
