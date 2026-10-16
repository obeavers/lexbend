import Base
import ../LexLeanPrelude.bend as L
import ./Addition.bend as PeanoArithmetic_Addition

def divides(+llv0: Nat, +llv1: Nat) -> Data:
  Sigma<&2, &2, Nat, llv2 => {llv1 == L.Lean.Nat.mul(llv0, llv2) : Nat}>

law divides_refl:
  for +llv0: Nat
  divides(llv0, llv0)

def divides_refl(llv0):
  (1n, L.Lean.Eq.symm(Nat, L.Lean.Nat.mul(llv0, 1n), llv0, L.Lean.Nat.mul_one(llv0)))

law one_divides:
  for +llv0: Nat
  divides(1n, llv0)

def one_divides(llv0):
  (llv0, L.Lean.Eq.symm(Nat, L.Lean.Nat.mul(1n, llv0), llv0, L.Lean.Nat.one_mul(llv0)))

def divides_trans.c2(+llv1: Nat, +llv2: Nat, +llh2: divides(llv1, llv2), +llv0: Nat, +llh3: Nat, +llh4: {llv1 == L.Lean.Nat.mul(llv0, llh3) : Nat}) -> divides(llv0, llv2):
  match llh2:
    case (+llh5, +llh6):
      (L.Lean.Nat.mul(llh3, llh5), {(
        %Equal.sym(Nat, llv2, L.Lean.Nat.mul(llv1, llh5), llh6) : {_ == L.Lean.Nat.mul(llv0, L.Lean.Nat.mul(llh3, llh5)) : Nat}
        %Equal.sym(Nat, llv1, L.Lean.Nat.mul(llv0, llh3), llh4) : {L.Lean.Nat.mul(_, llh5) == L.Lean.Nat.mul(llv0, L.Lean.Nat.mul(llh3, llh5)) : Nat}
        L.Lean.Nat.mul_assoc(llv0, llh3, llh5)
      ) : {llv2 == L.Lean.Nat.mul(llv0, L.Lean.Nat.mul(llh3, llh5)) : Nat}})

def divides_trans.c1(+llv0: Nat, +llv1: Nat, +llh1: divides(llv0, llv1), +llv2: Nat, +llh2: divides(llv1, llv2)) -> divides(llv0, llv2):
  match llh1:
    case (+llh3, +llh4):
      divides_trans.c2(llv1, llv2, llh2, llv0, llh3, llh4)

def divides_trans.c0(+llv0: Nat, +llv1: Nat, +llv2: Nat, +llh0: Sigma<&2, &2, divides(llv0, llv1), llx => divides(llv1, llv2)>) -> divides(llv0, llv2):
  match llh0:
    case (+llh1, +llh2):
      divides_trans.c1(llv0, llv1, llh1, llv2, llh2)

law divides_trans:
  for +llv0: Nat
  for +llv1: Nat
  for +llv2: Nat
  for +llh0: Sigma<&2, &2, divides(llv0, llv1), llx => divides(llv1, llv2)>
  divides(llv0, llv2)

def divides_trans(llv0, llv1, llv2, llh0):
  divides_trans.c0(llv0, llv1, llv2, llh0)
