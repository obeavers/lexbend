import Base
import ../LexLeanPrelude.bend as L

def and_comm.c0(-llv0: Type, -llv1: Type, llh0: Sigma<&1, &1, llv0, llx => llv1>) -> Sigma<&1, &1, llv1, llx => llv0>:
  match llh0:
    case (llh1, llh2):
      (llh2, llh1)

law and_comm:
  for -llv0: Type
  for -llv1: Type
  for llh0: Sigma<&1, &1, llv0, llx => llv1>
  Sigma<&1, &1, llv1, llx => llv0>

def and_comm(llv0, llv1, llh0):
  and_comm.c0(llv0, llv1, llh0)

def and_assoc.c1(-llv0: Type, -llv1: Type, llh1: Sigma<&1, &1, llv0, llx => llv1>, -llv2: Type, llh2: llv2) -> Sigma<&1, &1, llv0, llx => Sigma<&1, &1, llv1, llx => llv2>>:
  match llh1:
    case (llh3, llh4):
      (llh3, (llh4, llh2))

def and_assoc.c0(-llv0: Type, -llv1: Type, -llv2: Type, llh0: Sigma<&1, &1, Sigma<&1, &1, llv0, llx => llv1>, llx => llv2>) -> Sigma<&1, &1, llv0, llx => Sigma<&1, &1, llv1, llx => llv2>>:
  match llh0:
    case (llh1, llh2):
      and_assoc.c1(llv0, llv1, llh1, llv2, llh2)

def and_assoc.c3(-llv1: Type, -llv2: Type, llh7: Sigma<&1, &1, llv1, llx => llv2>, -llv0: Type, llh6: llv0) -> Sigma<&1, &1, Sigma<&1, &1, llv0, llx => llv1>, llx => llv2>:
  match llh7:
    case (llh8, llh9):
      ((llh6, llh8), llh9)

def and_assoc.c2(-llv0: Type, -llv1: Type, -llv2: Type, llh5: Sigma<&1, &1, llv0, llx => Sigma<&1, &1, llv1, llx => llv2>>) -> Sigma<&1, &1, Sigma<&1, &1, llv0, llx => llv1>, llx => llv2>:
  match llh5:
    case (llh6, llh7):
      and_assoc.c3(llv1, llv2, llh7, llv0, llh6)

law and_assoc:
  for -llv0: Type
  for -llv1: Type
  for -llv2: Type
  (Sigma<&1, &1, Sigma<&1, &1, llv0, llx => llv1>, llx => llv2> -> Sigma<&1, &1, llv0, llx => Sigma<&1, &1, llv1, llx => llv2>>) & (Sigma<&1, &1, llv0, llx => Sigma<&1, &1, llv1, llx => llv2>> -> Sigma<&1, &1, Sigma<&1, &1, llv0, llx => llv1>, llx => llv2>)

def and_assoc(llv0, llv1, llv2):
  ((llh0 => and_assoc.c0(llv0, llv1, llv2, llh0)), (llh5 => and_assoc.c2(llv0, llv1, llv2, llh5)))

def or_comm.c0(-llv0: Type, -llv1: Type, llh0: Either<&1, &1, llv0, llv1>) -> Either<&1, &1, llv1, llv0>:
  match llh0:
    case Inl{llh1}:
      Inr{llh1}
    case Inr{llh2}:
      Inl{llh2}

law or_comm:
  for -llv0: Type
  for -llv1: Type
  for llh0: Either<&1, &1, llv0, llv1>
  Either<&1, &1, llv1, llv0>

def or_comm(llv0, llv1, llh0):
  or_comm.c0(llv0, llv1, llh0)

def or_elim.c0(-llv0: Type, -llv1: Type, llh0: Either<&1, &1, llv0, llv1>, -llv2: Type, llh1: llv0 -> llv2, llh2: llv1 -> llv2) -> llv2:
  match llh0:
    case Inl{llh3}:
      llh1(llh3)
    case Inr{llh4}:
      llh2(llh4)

law or_elim:
  for -llv0: Type
  for -llv1: Type
  for -llv2: Type
  for llh0: Either<&1, &1, llv0, llv1>
  for llh1: llv0 -> llv2
  for llh2: llv1 -> llv2
  llv2

def or_elim(llv0, llv1, llv2, llh0, llh1, llh2):
  or_elim.c0(llv0, llv1, llh0, llv2, llh1, llh2)

law double_negation_intro:
  for -llv0: Type
  for llh0: llv0
  for llh1: llv0 -> Empty
  Empty

def double_negation_intro(llv0, llh0, llh1):
  llh1(llh0)

def explosion.c0(-llv0: Type, llh0: Sigma<&1, &1, llv0, llx => llv0 -> Empty>, -llv1: Type) -> llv1:
  match llh0:
    case (llh1, llh2):
      L.Lean.absurd(llv0, llv1, llh1, llh2)

law explosion:
  for -llv0: Type
  for -llv1: Type
  for llh0: Sigma<&1, &1, llv0, llx => llv0 -> Empty>
  llv1

def explosion(llv0, llv1, llh0):
  explosion.c0(llv0, llh0, llv1)

law iff_refl:
  for -llv0: Type
  (llv0 -> llv0) & (llv0 -> llv0)

def iff_refl(llv0):
  ((llh0 => llh0), (llh1 => llh1))

def iff_symm.c0(-llv0: Type, -llv1: Type, llh0: (llv0 -> llv1) & (llv1 -> llv0)) -> (llv1 -> llv0) & (llv0 -> llv1):
  match llh0:
    case (llh1, llh2):
      (llh2, llh1)

law iff_symm:
  for -llv0: Type
  for -llv1: Type
  for llh0: (llv0 -> llv1) & (llv1 -> llv0)
  (llv1 -> llv0) & (llv0 -> llv1)

def iff_symm(llv0, llv1, llh0):
  iff_symm.c0(llv0, llv1, llh0)

def double_negation_elim.c0(-llv0: Type, llc1: Either<&1, &1, llv0, llv0 -> Empty>, llh0: (llv0 -> Empty) -> Empty) -> llv0:
  match llc1:
    case Inl{llh1}:
      llh1
    case Inr{llh2}:
      L.Lean.absurd(llv0 -> Empty, llv0, llh2, llh0)

law double_negation_elim:
  for ll_excluded_middle: L.Lean.Assume.excluded_middle()
  for -llv0: Type
  for llh0: (llv0 -> Empty) -> Empty
  llv0

def double_negation_elim(ll_excluded_middle, llv0, llh0):
  double_negation_elim.c0(llv0, ll_excluded_middle(llv0), llh0)
