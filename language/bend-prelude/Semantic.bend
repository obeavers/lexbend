# LexLean semantic support: the forms language 2.2 lowers the language-1.2
# semantic surface through, over the Lean denotations of `LexLean.bend`.
# Nothing here is a Lean name; each def is the Bend reading of one fixed
# semantic construct, so a goal Lean closes by `rfl` or `decide` on a closed
# value closes here by `{==}`.

import Base
import ./LexLean.bend as L

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
