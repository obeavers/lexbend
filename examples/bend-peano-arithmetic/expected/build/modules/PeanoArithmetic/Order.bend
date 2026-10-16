import Base
import ../LexLeanPrelude.bend as L
import ./Addition.bend as PeanoArithmetic_Addition

def positive(+llv0: Nat) -> Type:
  L.Lean.Nat.lt(0n, llv0)

law successor_positive:
  for +llv0: Nat
  positive(L.Lean.Nat.succ(llv0))

def successor_positive(llv0):
  L.Lean.Nat.zero_lt_succ(llv0)

def zero_le.i0(+llv0: Nat) -> L.Lean.Nat.le(0n, llv0):
  match llv0:
    case 0n:
      L.Lean.Nat.le_refl(0n)
    case 1n++llh0:
      llh1 = zero_le.i0(llh0)
      L.Lean.Nat.le_trans(0n, llh0, L.Lean.Nat.succ(llh0), llh1, L.Lean.Nat.le_succ(llh0))

law zero_le:
  for +llv0: Nat
  L.Lean.Nat.le(0n, llv0)

def zero_le(llv0):
  zero_le.i0(llv0)

law le_add_right:
  for +llv0: Nat
  L.Lean.Nat.le(llv0, L.Lean.Nat.add(llv0, 0n))

def le_add_right(llv0):
  %Equal.sym(Nat, L.Lean.Nat.add(llv0, 0n), llv0, PeanoArithmetic_Addition.add_zero(llv0)) : L.Lean.Nat.le(llv0, _)
  L.Lean.Nat.le_refl(llv0)

def zero_or_successor.c0(+llv0: Nat) -> Either<&1, &1, {llv0 == 0n : Nat}, Sigma<&2, &2, Nat, llv1 => {llv0 == L.Lean.Nat.succ(llv1) : Nat}>>:
  match llv0:
    case 0n:
      Inl{{==}}
    case 1n++llh0:
      Inr{(llh0, {==})}

law zero_or_successor:
  for +llv0: Nat
  Either<&1, &1, {llv0 == 0n : Nat}, Sigma<&2, &2, Nat, llv1 => {llv0 == L.Lean.Nat.succ(llv1) : Nat}>>

def zero_or_successor(llv0):
  zero_or_successor.c0(llv0)

law successor_not_zero:
  for +llv0: Nat
  for +llh0: {L.Lean.Nat.succ(llv0) == 0n : Nat}
  Empty

def successor_not_zero(llv0, llh0):
  L.Lean.Nat.succ_ne_zero(llv0, llh0)
