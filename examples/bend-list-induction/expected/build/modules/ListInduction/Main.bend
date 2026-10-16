import Base
import ../LexLeanPrelude.bend as L

law nil_append:
  for -llv0: Data
  for +llv1: List<&2, llv0>
  {L.Lean.List.append(llv0, L.Lean.List.nil(llv0), llv1) == llv1 : List<&2, llv0>}

def nil_append(llv0, llv1):
  {==}

law cons_append:
  for -llv0: Data
  for +llv1: llv0
  for +llv2: List<&2, llv0>
  for +llv3: List<&2, llv0>
  {L.Lean.List.append(llv0, L.Lean.List.cons(llv0, llv1, llv2), llv3) == L.Lean.List.cons(llv0, llv1, L.Lean.List.append(llv0, llv2, llv3)) : List<&2, llv0>}

def cons_append(llv0, llv1, llv2, llv3):
  {==}

law length_singleton:
  for -llv0: Data
  for +llv1: llv0
  {L.Lean.List.length(llv0, L.Lean.List.cons(llv0, llv1, L.Lean.List.nil(llv0))) == 1n : Nat}

def length_singleton(llv0, llv1):
  {==}

law length_cons:
  for -llv0: Data
  for +llv1: llv0
  for +llv2: List<&2, llv0>
  {L.Lean.List.length(llv0, L.Lean.List.cons(llv0, llv1, llv2)) == L.Lean.Nat.succ(L.Lean.List.length(llv0, llv2)) : Nat}

def length_cons(llv0, llv1, llv2):
  {==}

def append_nil.i0(-llv0: Data, +llv1: List<&2, llv0>) -> {L.Lean.List.append(llv0, llv1, L.Lean.List.nil(llv0)) == llv1 : List<&2, llv0>}:
  match llv1:
    case Nil{}:
      {==}
    case Con{+llh0, +llh1}:
      llh2 = append_nil.i0(llv0, llh1)
      %Equal.sym(List<&2, llv0>, L.Lean.List.append(llv0, L.Lean.List.cons(llv0, llh0, llh1), L.Lean.List.nil(llv0)), L.Lean.List.cons(llv0, llh0, L.Lean.List.append(llv0, llh1, L.Lean.List.nil(llv0))), cons_append(llv0, llh0, llh1, L.Lean.List.nil(llv0))) : {_ == L.Lean.List.cons(llv0, llh0, llh1) : List<&2, llv0>}
      %Equal.sym(List<&2, llv0>, L.Lean.List.append(llv0, llh1, L.Lean.List.nil(llv0)), llh1, llh2) : {L.Lean.List.cons(llv0, llh0, _) == L.Lean.List.cons(llv0, llh0, llh1) : List<&2, llv0>}
      {==}

law append_nil:
  for -llv0: Data
  for +llv1: List<&2, llv0>
  {L.Lean.List.append(llv0, llv1, L.Lean.List.nil(llv0)) == llv1 : List<&2, llv0>}

def append_nil(llv0, llv1):
  append_nil.i0(llv0, llv1)

law succ_add_doc:
  for +llv0: Nat
  for +llv1: Nat
  {L.Lean.Nat.add(L.Lean.Nat.succ(llv0), llv1) == L.Lean.Nat.succ(L.Lean.Nat.add(llv0, llv1)) : Nat}

def succ_add_doc(llv0, llv1):
  L.Lean.Nat.succ_add(llv0, llv1)

law length_append:
  for -llv0: Data
  for +llv1: List<&2, llv0>
  for +llv2: List<&2, llv0>
  {L.Lean.List.length(llv0, L.Lean.List.append(llv0, llv1, llv2)) == L.Lean.Nat.add(L.Lean.List.length(llv0, llv1), L.Lean.List.length(llv0, llv2)) : Nat}

def length_append(llv0, llv1, llv2):
  L.Lean.List.length_append(llv0, llv1, llv2)
