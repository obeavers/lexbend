import Base
import ../LexLeanPrelude.bend as L

law add_zero:
  for +llv0: Nat
  {L.Lean.Nat.add(llv0, 0n) == llv0 : Nat}

def add_zero(llv0):
  {==}

law zero_add:
  for +llv0: Nat
  {L.Lean.Nat.add(0n, llv0) == llv0 : Nat}

def zero_add(llv0):
  L.Lean.Nat.zero_add(llv0)

law succ_add:
  for +llv0: Nat
  for +llv1: Nat
  {L.Lean.Nat.add(L.Lean.Nat.succ(llv0), llv1) == L.Lean.Nat.succ(L.Lean.Nat.add(llv0, llv1)) : Nat}

def succ_add(llv0, llv1):
  L.Lean.Nat.succ_add(llv0, llv1)

law both_identities:
  for +llv0: Nat
  Sigma<&2, &2, {L.Lean.Nat.add(llv0, 0n) == llv0 : Nat}, llx => {L.Lean.Nat.add(0n, llv0) == llv0 : Nat}>

def both_identities(llv0):
  ({==}, zero_add(llv0))

law add_comm:
  for +llv0: Nat
  for +llv1: Nat
  {L.Lean.Nat.add(llv0, llv1) == L.Lean.Nat.add(llv1, llv0) : Nat}

def add_comm(llv0, llv1):
  L.Lean.Nat.add_comm(llv0, llv1)

law add_comm_symm:
  for +llv0: Nat
  for +llv1: Nat
  {L.Lean.Nat.add(llv1, llv0) == L.Lean.Nat.add(llv0, llv1) : Nat}

def add_comm_symm(llv0, llv1):
  L.Lean.Eq.symm(Nat, L.Lean.Nat.add(llv0, llv1), L.Lean.Nat.add(llv1, llv0), add_comm(llv0, llv1))

law add_assoc:
  for +llv0: Nat
  for +llv1: Nat
  for +llv2: Nat
  {L.Lean.Nat.add(L.Lean.Nat.add(llv0, llv1), llv2) == L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv1, llv2)) : Nat}

def add_assoc(llv0, llv1, llv2):
  L.Lean.Nat.add_assoc(llv0, llv1, llv2)

law add_left_comm:
  for +llv0: Nat
  for +llv1: Nat
  for +llv2: Nat
  {L.Lean.Nat.add(llv0, L.Lean.Nat.add(llv1, llv2)) == L.Lean.Nat.add(llv1, L.Lean.Nat.add(llv0, llv2)) : Nat}

def add_left_comm(llv0, llv1, llv2):
  %add_assoc(llv0, llv1, llv2) : {_ == L.Lean.Nat.add(llv1, L.Lean.Nat.add(llv0, llv2)) : Nat}
  %Equal.sym(Nat, L.Lean.Nat.add(llv0, llv1), L.Lean.Nat.add(llv1, llv0), add_comm(llv0, llv1)) : {L.Lean.Nat.add(_, llv2) == L.Lean.Nat.add(llv1, L.Lean.Nat.add(llv0, llv2)) : Nat}
  %Equal.sym(Nat, L.Lean.Nat.add(L.Lean.Nat.add(llv1, llv0), llv2), L.Lean.Nat.add(llv1, L.Lean.Nat.add(llv0, llv2)), add_assoc(llv1, llv0, llv2)) : {_ == L.Lean.Nat.add(llv1, L.Lean.Nat.add(llv0, llv2)) : Nat}
  {==}
