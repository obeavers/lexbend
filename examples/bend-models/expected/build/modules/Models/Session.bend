import Base
import ../LexLeanPrelude.bend as L
import ../LexLeanSemantic.bend as S
import ../LexLeanRuntime.bend as R
import ../LexLeanLinArith.bend as LA

type ll.Window is Data:
  ll.Window.mk{used: Nat, items: Nat}

def ll.Window.used(ll_record: ll.Window) -> Nat:
  match ll_record:
    case ll.Window.mk{ll_f0, ll_f1}:
      ll_f0

def ll.Window.items(ll_record: ll.Window) -> Nat:
  match ll_record:
    case ll.Window.mk{ll_f0, ll_f1}:
      ll_f1

def Affordable(+window: ll.Window, +cost: Nat) -> Data:
  S.Sem.le(cost, 16n)

def affordableCheck(+window: ll.Window, +cost: Nat) -> Bool:
  L.Lean.Nat.ble(cost, 16n)

law affordable_check_sound:
  for +window: ll.Window
  for +cost: Nat
  for +ll_h0: {affordableCheck(window, cost) == True{} : Bool}
  Affordable(window, cost)

def affordable_check_sound(window, cost, ll_h0):
  LA.sound(Con{cost, Nil{}}, LA.FLe{LA.TVar{0n}, LA.TLit{16n}}, Con{LA.FIs{LA.BLe{LA.TVar{0n}, LA.TLit{16n}}, True{}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

def Bounded(+window: ll.Window) -> Data:
  S.Sem.le(ll.Window.used(window), 64n)

def boundedCheck(+window: ll.Window) -> Bool:
  L.Lean.Nat.ble(ll.Window.used(window), 64n)

law bounded_check_sound:
  for +window: ll.Window
  for +ll_h0: {boundedCheck(window) == True{} : Bool}
  Bounded(window)

def bounded_check_sound(window, ll_h0):
  LA.sound(Con{ll.Window.used(window), Nil{}}, LA.FLe{LA.TVar{0n}, LA.TLit{64n}}, Con{LA.FIs{LA.BLe{LA.TVar{0n}, LA.TLit{64n}}, True{}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

def Conserves(+window: ll.Window, +cost: Nat, +updated: ll.Window, +overflow: Nat) -> Data:
  {L.Lean.Nat.add(ll.Window.used(updated), overflow) == L.Lean.Nat.add(ll.Window.used(window), cost) : Nat}

law SessionContract.invariant_sound:
  R.LexLeanModels.Sound1(ll.Window, (+ll_x1 => boundedCheck(ll_x1)), (+ll_x2 => Bounded(ll_x2)))

def SessionContract.invariant_sound():
  ll_a3 => ll_a4 => bounded_check_sound(ll_a3, ll_a4)

law SessionContract.precondition_sound:
  R.LexLeanModels.Sound2(ll.Window, Nat, (+ll_x5 => +ll_x6 => affordableCheck(ll_x5, ll_x6)), (+ll_x7 => +ll_x8 => Affordable(ll_x7, ll_x8)))

def SessionContract.precondition_sound():
  ll_a9 => ll_a10 => ll_a11 => affordable_check_sound(ll_a9, ll_a10, ll_a11)

def SessionStep.initial() -> ll.Window:
  ll.Window.mk{0n, 0n}

def SessionStep(+window: ll.Window, +cost: Nat) -> L.Lean.Prod(ll.Window, Nat):
  +total = L.Lean.Nat.add(ll.Window.used(window), cost)
  (ll.Window.mk{L.Lean.Nat.sub(total, L.Lean.Nat.sub(total, 64n)), L.Lean.Nat.add(ll.Window.items(window), 1n)}, L.Lean.Nat.sub(total, 64n))

law session_initial:
  Bounded(SessionStep.initial())

def session_initial():
  {==}

law session_preserves:
  for +window: ll.Window
  for +cost: Nat
  for +ll_h0: Bounded(window)
  for +ll_h1: Affordable(window, cost)
  Bounded(S.Sem.fst(ll.Window, Nat, SessionStep(window, cost)))

def session_preserves(window, cost, ll_h0, ll_h1):
  LA.sound(Con{L.Lean.Nat.sub(L.Lean.Nat.add(ll.Window.used(window), cost), L.Lean.Nat.sub(L.Lean.Nat.add(ll.Window.used(window), cost), 64n)), Con{ll.Window.used(window), Con{cost, Con{L.Lean.Nat.sub(L.Lean.Nat.add(ll.Window.used(window), cost), 64n), Nil{}}}}}, LA.FLe{LA.TVar{0n}, LA.TLit{64n}}, Con{LA.FSub{LA.TVar{3n}, LA.TAdd{LA.TVar{1n}, LA.TVar{2n}}, LA.TLit{64n}}, Con{LA.FSub{LA.TVar{0n}, LA.TAdd{LA.TVar{1n}, LA.TVar{2n}}, LA.TVar{3n}}, Nil{}}}, 19n, LA.Fork{LA.Fork{LA.Leaf{Con{0n, Con{1n, Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}, LA.Leaf{Con{0n, Con{1n, Con{0n, Con{0n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}}, LA.Fork{LA.Leaf{Con{0n, Con{1n, Con{0n, Con{1n, Con{0n, Con{1n, Con{1n, Nil{}}}}}}}}}, LA.Leaf{Con{0n, Con{1n, Con{0n, Con{0n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}}}, {==}, ({==}, ({==}, Unit{})))

law session_conserves:
  for +window: ll.Window
  for +cost: Nat
  for +ll_h0: Bounded(window)
  for +ll_h1: Affordable(window, cost)
  Conserves(window, cost, S.Sem.fst(ll.Window, Nat, SessionStep(window, cost)), S.Sem.snd(ll.Window, Nat, SessionStep(window, cost)))

def session_conserves(window, cost, ll_h0, ll_h1):
  LA.sound(Con{L.Lean.Nat.sub(L.Lean.Nat.add(ll.Window.used(window), cost), L.Lean.Nat.sub(L.Lean.Nat.add(ll.Window.used(window), cost), 64n)), Con{ll.Window.used(window), Con{cost, Con{L.Lean.Nat.sub(L.Lean.Nat.add(ll.Window.used(window), cost), 64n), Nil{}}}}}, LA.FEq{LA.TAdd{LA.TVar{0n}, LA.TVar{3n}}, LA.TAdd{LA.TVar{1n}, LA.TVar{2n}}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{1n}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{2n}}, Con{LA.FSub{LA.TVar{3n}, LA.TAdd{LA.TVar{1n}, LA.TVar{2n}}, LA.TLit{64n}}, Con{LA.FSub{LA.TVar{0n}, LA.TAdd{LA.TVar{1n}, LA.TVar{2n}}, LA.TVar{3n}}, Nil{}}}}}, 25n, LA.Fork{LA.Skip{LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{0n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}, LA.Leaf{Con{1n, Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}}, LA.Fork{LA.Fork{LA.Leaf{Con{0n, Con{1n, Con{0n, Con{0n, Con{0n, Con{0n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{1n, Con{0n, Con{1n, Nil{}}}}}}}}, LA.Fork{LA.Leaf{Con{0n, Con{1n, Con{0n, Con{0n, Con{0n, Con{0n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{1n, Con{0n, Con{1n, Con{0n, Con{1n, Con{1n, Nil{}}}}}}}}}}}}}, {==}, ({==}, ({==}, ({==}, ({==}, Unit{})))))

law SessionEvidence.session_initial:
  R.LexLeanModels.Initial(ll.Window, (+ll_x12 => Bounded(ll_x12)), SessionStep.initial())

def SessionEvidence.session_initial():
  session_initial()

law SessionEvidence.session_preserves:
  R.LexLeanModels.Preserves(ll.Window, Nat, Nat, (+ll_x13 => Bounded(ll_x13)), (+ll_x14 => +ll_x15 => Affordable(ll_x14, ll_x15)), (+ll_x16 => +ll_x17 => SessionStep(ll_x16, ll_x17)))

def SessionEvidence.session_preserves():
  ll_a18 => ll_a19 => ll_a20 => ll_a21 => session_preserves(ll_a18, ll_a19, ll_a20, ll_a21)

law SessionEvidence.session_conserves:
  R.LexLeanModels.SatisfiesStep(ll.Window, Nat, Nat, (+ll_x22 => Bounded(ll_x22)), (+ll_x23 => +ll_x24 => Affordable(ll_x23, ll_x24)), (+ll_x25 => +ll_x26 => +ll_x27 => +ll_x28 => Conserves(ll_x25, ll_x26, ll_x27, ll_x28)), (+ll_x29 => +ll_x30 => SessionStep(ll_x29, ll_x30)))

def SessionEvidence.session_conserves():
  ll_a31 => ll_a32 => ll_a33 => ll_a34 => session_conserves(ll_a31, ll_a32, ll_a33, ll_a34)

def SessionModel.initial() -> ll.Window:
  SessionStep.initial()

def SessionModel(+__state: ll.Window, +__input: Nat) -> L.Lean.Prod(ll.Window, Nat):
  SessionStep(__state, __input)
