import Base
import ../LexLeanPrelude.bend as L
import ./Addition.bend as PeanoArithmetic_Addition

def count() -> Data:
  Nat

def double(+llv0: Nat) -> Nat:
  L.Lean.Nat.add(llv0, llv0)

def even(+llv0: Nat) -> Data:
  Sigma<&2, &2, Nat, llv1 => {llv0 == L.Lean.Nat.add(llv1, llv1) : Nat}>

law double_even:
  for +llv0: Nat
  even(double(llv0))

def double_even(llv0):
  (llv0, {==})

law sum_even:
  for +llv0: Nat
  even(L.Lean.Nat.add(llv0, llv0))

def sum_even(llv0):
  (llv0, {==})

law zero_even:
  even(0n)

def zero_even():
  (0n, {==})

def even_succ_succ.c0(+llv0: Nat, +llh0: even(llv0)) -> even(L.Lean.Nat.succ(L.Lean.Nat.succ(llv0))):
  match llh0:
    case (+llh1, +llh2):
      (L.Lean.Nat.succ(llh1), {(
        %Equal.sym(Nat, llv0, L.Lean.Nat.add(llh1, llh1), llh2) : {L.Lean.Nat.succ(L.Lean.Nat.succ(_)) == L.Lean.Nat.add(L.Lean.Nat.succ(llh1), L.Lean.Nat.succ(llh1)) : Nat}
        %PeanoArithmetic_Addition.succ_add(llh1, llh1) : {L.Lean.Nat.succ(_) == L.Lean.Nat.add(L.Lean.Nat.succ(llh1), L.Lean.Nat.succ(llh1)) : Nat}
        {==}
      ) : {L.Lean.Nat.succ(L.Lean.Nat.succ(llv0)) == L.Lean.Nat.add(L.Lean.Nat.succ(llh1), L.Lean.Nat.succ(llh1)) : Nat}})

law even_succ_succ:
  for +llv0: Nat
  for +llh0: even(llv0)
  even(L.Lean.Nat.succ(L.Lean.Nat.succ(llv0)))

def even_succ_succ(llv0, llh0):
  even_succ_succ.c0(llv0, llh0)

law rotate:
  for +llv0: Nat
  for +llv1: Nat
  {L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv1, L.Lean.Nat.add(llv0, llv1))) == L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv1, llv1))) : Nat}

def rotate(llv0, llv1):
  %Equal.sym(Nat, L.Lean.Nat.add(llv1, L.Lean.Nat.add(llv0, llv1)), L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv1, llv1)), PeanoArithmetic_Addition.add_left_comm(llv1, llv0, llv1)) : {L.Lean.Nat.add(llv0, _) == L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv1, llv1))) : Nat}
  {==}

law double_add:
  for +llv0: Nat
  for +llv1: Nat
  {double(L.Lean.Nat.add(llv0, llv1)) == L.Lean.Nat.add(double(llv0), double(llv1)) : Nat}

def double_add(llv0, llv1):
  Equal.trans(Nat, double(L.Lean.Nat.add(llv0, llv1)), L.Lean.Nat.add(L.Lean.Nat.add(llv0, llv1), L.Lean.Nat.add(llv0, llv1)), L.Lean.Nat.add(double(llv0), double(llv1)), L.Lean.rfl(Nat, double(L.Lean.Nat.add(llv0, llv1))), Equal.trans(Nat, L.Lean.Nat.add(L.Lean.Nat.add(llv0, llv1), L.Lean.Nat.add(llv0, llv1)), L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv1, L.Lean.Nat.add(llv0, llv1))), L.Lean.Nat.add(double(llv0), double(llv1)), L.Lean.Nat.add_assoc(llv0, llv1, L.Lean.Nat.add(llv0, llv1)), Equal.trans(Nat, L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv1, L.Lean.Nat.add(llv0, llv1))), L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv1, llv1))), L.Lean.Nat.add(double(llv0), double(llv1)), rotate(llv0, llv1), Equal.trans(Nat, L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv1, llv1))), L.Lean.Nat.add(L.Lean.Nat.add(llv0, llv0), L.Lean.Nat.add(llv1, llv1)), L.Lean.Nat.add(double(llv0), double(llv1)), L.Lean.Eq.symm(Nat, L.Lean.Nat.add(L.Lean.Nat.add(llv0, llv0), L.Lean.Nat.add(llv1, llv1)), L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv1, llv1))), L.Lean.Nat.add_assoc(llv0, llv0, L.Lean.Nat.add(llv1, llv1))), L.Lean.rfl(Nat, L.Lean.Nat.add(L.Lean.Nat.add(llv0, llv0), L.Lean.Nat.add(llv1, llv1)))))))
