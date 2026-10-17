import Base
import ../LexLeanPrelude.bend as L

def doubledSuccessor(+n: Nat) -> Nat:
  +doubled = L.Lean.Nat.add(n, n)
  L.Lean.Nat.add(doubled, 1n)

law doubled_successor_two:
  {doubledSuccessor(2n) == 5n : Nat}

def doubled_successor_two():
  {==}

law let_statement_unfolds:
  {L.Lean.Nat.add(3n, 3n) == 6n : Nat}

def let_statement_unfolds():
  {==}
