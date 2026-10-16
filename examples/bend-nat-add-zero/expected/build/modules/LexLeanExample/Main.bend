import Base
import ../LexLeanPrelude.bend as L

law add_zero:
  for +llv0: Nat
  {L.Lean.Nat.add(llv0, 0n) == llv0 : Nat}

def add_zero(llv0):
  {==}
