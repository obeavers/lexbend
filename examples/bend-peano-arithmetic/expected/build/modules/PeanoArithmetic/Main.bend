import Base
import ../LexLeanPrelude.bend as L
import ./Addition.bend as PeanoArithmetic_Addition
import ./Divisibility.bend as PeanoArithmetic_Divisibility
import ./Doubling.bend as PeanoArithmetic_Doubling
import ./Order.bend as PeanoArithmetic_Order

law comm_under_hypothesis:
  for +llv0: Nat
  for +llv1: Nat
  for +llh0: {llv0 == llv1 : Nat}
  {L.Lean.Nat.add(llv0, llv1) == L.Lean.Nat.add(llv1, llv0) : Nat}

def comm_under_hypothesis(llv0, llv1, llh0):
  PeanoArithmetic_Addition.add_comm(llv0, llv1)

law comm_rewrite:
  for +llv0: Nat
  for +llv1: Nat
  for +llh0: {llv0 == llv1 : Nat}
  {L.Lean.Nat.add(llv0, llv0) == L.Lean.Nat.add(llv1, llv0) : Nat}

def comm_rewrite(llv0, llv1, llh0):
  %Equal.sym(Nat, llv0, llv1, llh0) : {L.Lean.Nat.add(_, _) == L.Lean.Nat.add(llv1, _) : Nat}
  {==}

law double_divides:
  for +llv0: Nat
  PeanoArithmetic_Divisibility.divides(2n, PeanoArithmetic_Doubling.double(llv0))

def double_divides(llv0):
  (llv0, L.Lean.Eq.symm(Nat, L.Lean.Nat.mul(2n, llv0), L.Lean.Nat.add(llv0, llv0), L.Lean.Nat.two_mul(llv0)))

def even_divides.c0(+llv0: Nat, +llh0: PeanoArithmetic_Doubling.even(llv0)) -> PeanoArithmetic_Divisibility.divides(2n, llv0):
  match llh0:
    case (+llh1, +llh2):
      (llh1, {(
        %Equal.sym(Nat, llv0, L.Lean.Nat.add(llh1, llh1), llh2) : {_ == L.Lean.Nat.mul(2n, llh1) : Nat}
        L.Lean.Eq.symm(Nat, L.Lean.Nat.mul(2n, llh1), L.Lean.Nat.add(llh1, llh1), L.Lean.Nat.two_mul(llh1))
      ) : {llv0 == L.Lean.Nat.mul(2n, llh1) : Nat}})

law even_divides:
  for +llv0: Nat
  for +llh0: PeanoArithmetic_Doubling.even(llv0)
  PeanoArithmetic_Divisibility.divides(2n, llv0)

def even_divides(llv0, llh0):
  even_divides.c0(llv0, llh0)

law even_or_not:
  for ll_excluded_middle: L.Lean.Assume.excluded_middle()
  for +llv0: Nat
  Either<&1, &1, PeanoArithmetic_Doubling.even(llv0), PeanoArithmetic_Doubling.even(llv0) -> Empty>

def even_or_not(ll_excluded_middle, llv0):
  ll_excluded_middle(PeanoArithmetic_Doubling.even(llv0))

def positive_or_zero.c0(+llv0: Nat) -> Either<&1, &1, PeanoArithmetic_Order.positive(llv0), {llv0 == 0n : Nat}>:
  match llv0:
    case 0n:
      Inr{{==}}
    case 1n++llh0:
      Inl{PeanoArithmetic_Order.successor_positive(llh0)}

law positive_or_zero:
  for +llv0: Nat
  Either<&1, &1, PeanoArithmetic_Order.positive(llv0), {llv0 == 0n : Nat}>

def positive_or_zero(llv0):
  positive_or_zero.c0(llv0)
