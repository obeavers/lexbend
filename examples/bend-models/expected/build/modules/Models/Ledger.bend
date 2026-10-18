import Base
import ../LexLeanPrelude.bend as L
import ../LexLeanSemantic.bend as S
import ../LexLeanRuntime.bend as R
import ../LexLeanLinArith.bend as LA

def Capped(+s: Nat) -> Data:
  S.Sem.le(s, 100n)

def cappedCheck(+s: Nat) -> Bool:
  L.Lean.Nat.ble(s, 100n)

law capped_check_sound:
  for +s: Nat
  for +ll_h0: {cappedCheck(s) == True{} : Bool}
  Capped(s)

def capped_check_sound(s, ll_h0):
  LA.sound(Con{s, Nil{}}, LA.FLe{LA.TVar{0n}, LA.TLit{100n}}, Con{LA.FIs{LA.BLe{LA.TVar{0n}, LA.TLit{100n}}, True{}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

law capped_check_complete:
  for +s: Nat
  for +ll_h0: Capped(s)
  {cappedCheck(s) == True{} : Bool}

def capped_check_complete(s, ll_h0):
  LA.sound(Con{s, Nil{}}, LA.FIs{LA.BLe{LA.TVar{0n}, LA.TLit{100n}}, True{}}, Con{LA.FLe{LA.TVar{0n}, LA.TLit{100n}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

def Small(+s: Nat, +x: Nat) -> Data:
  S.Sem.le(x, 10n)

def smallCheck(+s: Nat, +x: Nat) -> Bool:
  L.Lean.Nat.ble(x, 10n)

law small_check_sound:
  for +s: Nat
  for +x: Nat
  for +ll_h0: {smallCheck(s, x) == True{} : Bool}
  Small(s, x)

def small_check_sound(s, x, ll_h0):
  LA.sound(Con{x, Nil{}}, LA.FLe{LA.TVar{0n}, LA.TLit{10n}}, Con{LA.FIs{LA.BLe{LA.TVar{0n}, LA.TLit{10n}}, True{}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

def Grows(+s: Nat, +x: Nat, +t: Nat, +y: Nat) -> Data:
  S.Sem.le(s, t)

def growsCheck(+s: Nat, +x: Nat, +t: Nat, +y: Nat) -> Bool:
  L.Lean.Nat.ble(s, t)

law grows_check_sound:
  for +s: Nat
  for +x: Nat
  for +t: Nat
  for +y: Nat
  for +ll_h0: {growsCheck(s, x, t, y) == True{} : Bool}
  Grows(s, x, t, y)

def grows_check_sound(s, x, t, y, ll_h0):
  LA.sound(Con{s, Con{t, Nil{}}}, LA.FLe{LA.TVar{0n}, LA.TVar{1n}}, Con{LA.FIs{LA.BLe{LA.TVar{0n}, LA.TVar{1n}}, True{}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

law grows_check_complete:
  for +s: Nat
  for +x: Nat
  for +t: Nat
  for +y: Nat
  for +ll_h0: Grows(s, x, t, y)
  {growsCheck(s, x, t, y) == True{} : Bool}

def grows_check_complete(s, x, t, y, ll_h0):
  LA.sound(Con{s, Con{t, Nil{}}}, LA.FIs{LA.BLe{LA.TVar{0n}, LA.TVar{1n}}, True{}}, Con{LA.FLe{LA.TVar{0n}, LA.TVar{1n}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

law LedgerContract.invariant_sound:
  R.LexLeanModels.Sound1(Nat, (+ll_x1 => cappedCheck(ll_x1)), (+ll_x2 => Capped(ll_x2)))

def LedgerContract.invariant_sound():
  ll_a3 => ll_a4 => capped_check_sound(ll_a3, ll_a4)

law LedgerContract.invariant_complete:
  R.LexLeanModels.Complete1(Nat, (+ll_x5 => cappedCheck(ll_x5)), (+ll_x6 => Capped(ll_x6)))

def LedgerContract.invariant_complete():
  ll_a7 => ll_a8 => capped_check_complete(ll_a7, ll_a8)

law LedgerContract.postcondition_sound:
  R.LexLeanModels.Sound4(Nat, Nat, Nat, Nat, (+ll_x9 => +ll_x10 => +ll_x11 => +ll_x12 => growsCheck(ll_x9, ll_x10, ll_x11, ll_x12)), (+ll_x13 => +ll_x14 => +ll_x15 => +ll_x16 => Grows(ll_x13, ll_x14, ll_x15, ll_x16)))

def LedgerContract.postcondition_sound():
  ll_a17 => ll_a18 => ll_a19 => ll_a20 => ll_a21 => grows_check_sound(ll_a17, ll_a18, ll_a19, ll_a20, ll_a21)

law LedgerContract.postcondition_complete:
  R.LexLeanModels.Complete4(Nat, Nat, Nat, Nat, (+ll_x22 => +ll_x23 => +ll_x24 => +ll_x25 => growsCheck(ll_x22, ll_x23, ll_x24, ll_x25)), (+ll_x26 => +ll_x27 => +ll_x28 => +ll_x29 => Grows(ll_x26, ll_x27, ll_x28, ll_x29)))

def LedgerContract.postcondition_complete():
  ll_a30 => ll_a31 => ll_a32 => ll_a33 => ll_a34 => grows_check_complete(ll_a30, ll_a31, ll_a32, ll_a33, ll_a34)

law LedgerContract.precondition_sound:
  R.LexLeanModels.Sound2(Nat, Nat, (+ll_x35 => +ll_x36 => smallCheck(ll_x35, ll_x36)), (+ll_x37 => +ll_x38 => Small(ll_x37, ll_x38)))

def LedgerContract.precondition_sound():
  ll_a39 => ll_a40 => ll_a41 => small_check_sound(ll_a39, ll_a40, ll_a41)

def Spill.initial() -> Nat:
  0n

def Spill(+s: Nat, +x: Nat) -> L.Lean.Prod(Nat, Nat):
  (L.Lean.Nat.add(s, x), x)

def spillRef(+s: Nat, +x: Nat) -> L.Lean.Prod(Nat, Nat):
  (L.Lean.Nat.add(s, x), x)

law spill_grows:
  for +s: Nat
  for +x: Nat
  for +ll_h0: Capped(s)
  for +ll_h1: Small(s, x)
  Grows(s, x, S.Sem.fst(Nat, Nat, Spill(s, x)), S.Sem.snd(Nat, Nat, Spill(s, x)))

def spill_grows(s, x, ll_h0, ll_h1):
  LA.sound(Con{s, Con{x, Nil{}}}, LA.FLe{LA.TVar{0n}, LA.TAdd{LA.TVar{0n}, LA.TVar{1n}}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{1n}}, Nil{}}, 5n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, ({==}, Unit{}))

law spill_reference:
  for +s: Nat
  for +x: Nat
  for +ll_h0: Capped(s)
  for +ll_h1: Small(s, x)
  {Spill(s, x) == spillRef(s, x) : L.Lean.Prod(Nat, Nat)}

def spill_reference(s, x, ll_h0, ll_h1):
  {==}

law SpillEvidence.spill_grows:
  R.LexLeanModels.SatisfiesStep(Nat, Nat, Nat, (+ll_x42 => Capped(ll_x42)), (+ll_x43 => +ll_x44 => Small(ll_x43, ll_x44)), (+ll_x45 => +ll_x46 => +ll_x47 => +ll_x48 => Grows(ll_x45, ll_x46, ll_x47, ll_x48)), (+ll_x49 => +ll_x50 => Spill(ll_x49, ll_x50)))

def SpillEvidence.spill_grows():
  ll_a51 => ll_a52 => ll_a53 => ll_a54 => spill_grows(ll_a51, ll_a52, ll_a53, ll_a54)

def SpillModel.initial() -> Nat:
  Spill.initial()

def SpillModel(+__state: Nat, +__input: Nat) -> L.Lean.Prod(Nat, Nat):
  Spill(__state, __input)

law SpillReference.spill_reference:
  R.LexLeanModels.EquivalentStep(Nat, Nat, Nat, (+ll_x55 => Capped(ll_x55)), (+ll_x56 => +ll_x57 => Small(ll_x56, ll_x57)), (+ll_x58 => +ll_x59 => Spill(ll_x58, ll_x59)), (+ll_x60 => +ll_x61 => spillRef(ll_x60, ll_x61)))

def SpillReference.spill_reference():
  ll_a62 => ll_a63 => ll_a64 => ll_a65 => spill_reference(ll_a62, ll_a63, ll_a64, ll_a65)

def SpillRawModel.initial() -> Nat:
  Spill.initial()

def SpillRawModel(+__state: Nat, +__input: Nat) -> L.Lean.Prod(Nat, Nat):
  Spill(__state, __input)

law TallyContract.postcondition_sound:
  R.LexLeanModels.Sound4(Nat, Nat, Nat, Nat, (+ll_x66 => +ll_x67 => +ll_x68 => +ll_x69 => growsCheck(ll_x66, ll_x67, ll_x68, ll_x69)), (+ll_x70 => +ll_x71 => +ll_x72 => +ll_x73 => Grows(ll_x70, ll_x71, ll_x72, ll_x73)))

def TallyContract.postcondition_sound():
  ll_a74 => ll_a75 => ll_a76 => ll_a77 => ll_a78 => grows_check_sound(ll_a74, ll_a75, ll_a76, ll_a77, ll_a78)

law TallyContract.precondition_sound:
  R.LexLeanModels.Sound2(Nat, Nat, (+ll_x79 => +ll_x80 => smallCheck(ll_x79, ll_x80)), (+ll_x81 => +ll_x82 => Small(ll_x81, ll_x82)))

def TallyContract.precondition_sound():
  ll_a83 => ll_a84 => ll_a85 => small_check_sound(ll_a83, ll_a84, ll_a85)

def Tally.initial() -> Nat:
  0n

def Tally(+s: Nat, +x: Nat) -> L.Lean.Prod(Nat, Nat):
  (L.Lean.Nat.add(s, x), s)

def tallyRef(+s: Nat, +x: Nat) -> L.Lean.Prod(Nat, Nat):
  (L.Lean.Nat.add(s, x), s)

law tally_grows:
  for +s: Nat
  for +x: Nat
  for +ll_h0: Small(s, x)
  Grows(s, x, S.Sem.fst(Nat, Nat, Tally(s, x)), S.Sem.snd(Nat, Nat, Tally(s, x)))

def tally_grows(s, x, ll_h0):
  LA.sound(Con{s, Con{x, Nil{}}}, LA.FLe{LA.TVar{0n}, LA.TAdd{LA.TVar{0n}, LA.TVar{1n}}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{1n}}, Nil{}}, 5n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, ({==}, Unit{}))

law tally_reference:
  for +s: Nat
  for +x: Nat
  for +ll_h0: Small(s, x)
  {Tally(s, x) == tallyRef(s, x) : L.Lean.Prod(Nat, Nat)}

def tally_reference(s, x, ll_h0):
  {==}

law TallyEvidence.tally_reference:
  R.LexLeanModels.EquivalentStepNoInvariant(Nat, Nat, Nat, (+ll_x86 => +ll_x87 => Small(ll_x86, ll_x87)), (+ll_x88 => +ll_x89 => Tally(ll_x88, ll_x89)), (+ll_x90 => +ll_x91 => tallyRef(ll_x90, ll_x91)))

def TallyEvidence.tally_reference():
  ll_a92 => ll_a93 => ll_a94 => tally_reference(ll_a92, ll_a93, ll_a94)

law TallyEvidence.tally_grows:
  R.LexLeanModels.SatisfiesStepNoInvariant(Nat, Nat, Nat, (+ll_x95 => +ll_x96 => Small(ll_x95, ll_x96)), (+ll_x97 => +ll_x98 => +ll_x99 => +ll_x100 => Grows(ll_x97, ll_x98, ll_x99, ll_x100)), (+ll_x101 => +ll_x102 => Tally(ll_x101, ll_x102)))

def TallyEvidence.tally_grows():
  ll_a103 => ll_a104 => ll_a105 => tally_grows(ll_a103, ll_a104, ll_a105)

def TallyModel.initial() -> Nat:
  Tally.initial()

def TallyModel(+__state: Nat, +__input: Nat) -> L.Lean.Prod(Nat, Nat):
  Tally(__state, __input)

law CapContract.invariant_sound:
  R.LexLeanModels.Sound1(Nat, (+ll_x106 => cappedCheck(ll_x106)), (+ll_x107 => Capped(ll_x107)))

def CapContract.invariant_sound():
  ll_a108 => ll_a109 => capped_check_sound(ll_a108, ll_a109)

law CapContract.invariant_complete:
  R.LexLeanModels.Complete1(Nat, (+ll_x110 => cappedCheck(ll_x110)), (+ll_x111 => Capped(ll_x111)))

def CapContract.invariant_complete():
  ll_a112 => ll_a113 => capped_check_complete(ll_a112, ll_a113)

law CapContract.postcondition_sound:
  R.LexLeanModels.Sound4(Nat, Nat, Nat, Nat, (+ll_x114 => +ll_x115 => +ll_x116 => +ll_x117 => growsCheck(ll_x114, ll_x115, ll_x116, ll_x117)), (+ll_x118 => +ll_x119 => +ll_x120 => +ll_x121 => Grows(ll_x118, ll_x119, ll_x120, ll_x121)))

def CapContract.postcondition_sound():
  ll_a122 => ll_a123 => ll_a124 => ll_a125 => ll_a126 => grows_check_sound(ll_a122, ll_a123, ll_a124, ll_a125, ll_a126)

def Clamp.initial() -> Nat:
  0n

def Clamp(+s: Nat, +x: Nat) -> L.Lean.Prod(Nat, Nat):
  +total = L.Lean.Nat.add(s, x)
  (L.Lean.Nat.sub(total, L.Lean.Nat.sub(total, 100n)), L.Lean.Nat.sub(total, L.Lean.Nat.sub(total, 100n)))

def clampRef(+s: Nat, +x: Nat) -> L.Lean.Prod(Nat, Nat):
  +total = L.Lean.Nat.add(s, x)
  (L.Lean.Nat.sub(total, L.Lean.Nat.sub(total, 100n)), L.Lean.Nat.sub(total, L.Lean.Nat.sub(total, 100n)))

law clamp_initial:
  Capped(Clamp.initial())

def clamp_initial():
  {==}

law clamp_preserves:
  for +s: Nat
  for +x: Nat
  for +ll_h0: Capped(s)
  Capped(S.Sem.fst(Nat, Nat, Clamp(s, x)))

def clamp_preserves(s, x, ll_h0):
  LA.sound(Con{L.Lean.Nat.sub(L.Lean.Nat.add(s, x), L.Lean.Nat.sub(L.Lean.Nat.add(s, x), 100n)), Con{s, Con{x, Con{L.Lean.Nat.sub(L.Lean.Nat.add(s, x), 100n), Nil{}}}}}, LA.FLe{LA.TVar{0n}, LA.TLit{100n}}, Con{LA.FSub{LA.TVar{3n}, LA.TAdd{LA.TVar{1n}, LA.TVar{2n}}, LA.TLit{100n}}, Con{LA.FSub{LA.TVar{0n}, LA.TAdd{LA.TVar{1n}, LA.TVar{2n}}, LA.TVar{3n}}, Nil{}}}, 19n, LA.Fork{LA.Fork{LA.Leaf{Con{0n, Con{1n, Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}, LA.Leaf{Con{0n, Con{1n, Con{0n, Con{0n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}}, LA.Fork{LA.Leaf{Con{0n, Con{1n, Con{0n, Con{1n, Con{0n, Con{1n, Con{1n, Nil{}}}}}}}}}, LA.Leaf{Con{0n, Con{1n, Con{0n, Con{0n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}}}, {==}, ({==}, ({==}, Unit{})))

law clamp_grows:
  for +s: Nat
  for +x: Nat
  for +ll_h0: Capped(s)
  Grows(s, x, S.Sem.fst(Nat, Nat, Clamp(s, x)), S.Sem.snd(Nat, Nat, Clamp(s, x)))

def clamp_grows(s, x, ll_h0):
  LA.sound(Con{s, Con{L.Lean.Nat.sub(L.Lean.Nat.add(s, x), L.Lean.Nat.sub(L.Lean.Nat.add(s, x), 100n)), Con{x, Con{L.Lean.Nat.sub(L.Lean.Nat.add(s, x), 100n), Nil{}}}}}, LA.FLe{LA.TVar{0n}, LA.TVar{1n}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{0n}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{2n}}, Con{LA.FLe{LA.TVar{0n}, LA.TLit{100n}}, Con{LA.FSub{LA.TVar{3n}, LA.TAdd{LA.TVar{0n}, LA.TVar{2n}}, LA.TLit{100n}}, Con{LA.FSub{LA.TVar{1n}, LA.TAdd{LA.TVar{0n}, LA.TVar{2n}}, LA.TVar{3n}}, Nil{}}}}}}, 25n, LA.Fork{LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{0n, Con{0n, Con{1n, Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{1n, Con{0n, Con{1n, Nil{}}}}}}}}, LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{0n, Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Con{0n, Con{1n, Nil{}}}}}}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{1n, Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Con{1n, Nil{}}}}}}}}}}}}}, {==}, ({==}, ({==}, (ll_h0, ({==}, ({==}, Unit{}))))))

law clamp_reference:
  for +s: Nat
  for +x: Nat
  for +ll_h0: Capped(s)
  {Clamp(s, x) == clampRef(s, x) : L.Lean.Prod(Nat, Nat)}

def clamp_reference(s, x, ll_h0):
  {==}

law ClampEvidence.clamp_reference:
  R.LexLeanModels.EquivalentStepNoPrecondition(Nat, Nat, Nat, (+ll_x127 => Capped(ll_x127)), (+ll_x128 => +ll_x129 => Clamp(ll_x128, ll_x129)), (+ll_x130 => +ll_x131 => clampRef(ll_x130, ll_x131)))

def ClampEvidence.clamp_reference():
  ll_a132 => ll_a133 => ll_a134 => clamp_reference(ll_a132, ll_a133, ll_a134)

law ClampEvidence.clamp_initial:
  R.LexLeanModels.Initial(Nat, (+ll_x135 => Capped(ll_x135)), Clamp.initial())

def ClampEvidence.clamp_initial():
  clamp_initial()

law ClampEvidence.clamp_preserves:
  R.LexLeanModels.PreservesTotal(Nat, Nat, Nat, (+ll_x136 => Capped(ll_x136)), (+ll_x137 => +ll_x138 => Clamp(ll_x137, ll_x138)))

def ClampEvidence.clamp_preserves():
  ll_a139 => ll_a140 => ll_a141 => clamp_preserves(ll_a139, ll_a140, ll_a141)

law ClampEvidence.clamp_grows:
  R.LexLeanModels.SatisfiesStepNoPrecondition(Nat, Nat, Nat, (+ll_x142 => Capped(ll_x142)), (+ll_x143 => +ll_x144 => +ll_x145 => +ll_x146 => Grows(ll_x143, ll_x144, ll_x145, ll_x146)), (+ll_x147 => +ll_x148 => Clamp(ll_x147, ll_x148)))

def ClampEvidence.clamp_grows():
  ll_a149 => ll_a150 => ll_a151 => clamp_grows(ll_a149, ll_a150, ll_a151)

def ClampModel.initial() -> Nat:
  Clamp.initial()

def ClampModel(+__state: Nat, +__input: Nat) -> L.Lean.Prod(Nat, Nat):
  Clamp(__state, __input)

law FreeContract.postcondition_sound:
  R.LexLeanModels.Sound4(Nat, Nat, Nat, Nat, (+ll_x152 => +ll_x153 => +ll_x154 => +ll_x155 => growsCheck(ll_x152, ll_x153, ll_x154, ll_x155)), (+ll_x156 => +ll_x157 => +ll_x158 => +ll_x159 => Grows(ll_x156, ll_x157, ll_x158, ll_x159)))

def FreeContract.postcondition_sound():
  ll_a160 => ll_a161 => ll_a162 => ll_a163 => ll_a164 => grows_check_sound(ll_a160, ll_a161, ll_a162, ll_a163, ll_a164)

law tally_free_grows:
  for +s: Nat
  for +x: Nat
  Grows(s, x, S.Sem.fst(Nat, Nat, Tally(s, x)), S.Sem.snd(Nat, Nat, Tally(s, x)))

def tally_free_grows(s, x):
  LA.sound(Con{s, Con{x, Nil{}}}, LA.FLe{LA.TVar{0n}, LA.TAdd{LA.TVar{0n}, LA.TVar{1n}}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{1n}}, Nil{}}, 5n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, ({==}, Unit{}))

law tally_free_reference:
  for +s: Nat
  for +x: Nat
  {Tally(s, x) == tallyRef(s, x) : L.Lean.Prod(Nat, Nat)}

def tally_free_reference(s, x):
  {==}

law FreeEvidence.tally_free_reference:
  R.LexLeanModels.EquivalentStepTotal(Nat, Nat, Nat, (+ll_x165 => +ll_x166 => Tally(ll_x165, ll_x166)), (+ll_x167 => +ll_x168 => tallyRef(ll_x167, ll_x168)))

def FreeEvidence.tally_free_reference():
  ll_a169 => ll_a170 => tally_free_reference(ll_a169, ll_a170)

law FreeEvidence.tally_free_grows:
  R.LexLeanModels.SatisfiesStepTotal(Nat, Nat, Nat, (+ll_x171 => +ll_x172 => +ll_x173 => +ll_x174 => Grows(ll_x171, ll_x172, ll_x173, ll_x174)), (+ll_x175 => +ll_x176 => Tally(ll_x175, ll_x176)))

def FreeEvidence.tally_free_grows():
  ll_a177 => ll_a178 => tally_free_grows(ll_a177, ll_a178)

def FreeModel.initial() -> Nat:
  Tally.initial()

def FreeModel(+__state: Nat, +__input: Nat) -> L.Lean.Prod(Nat, Nat):
  Tally(__state, __input)

def Within(+x: Nat) -> Data:
  S.Sem.le(x, 10n)

def withinCheck(+x: Nat) -> Bool:
  L.Lean.Nat.ble(x, 10n)

law within_check_sound:
  for +x: Nat
  for +ll_h0: {withinCheck(x) == True{} : Bool}
  Within(x)

def within_check_sound(x, ll_h0):
  LA.sound(Con{x, Nil{}}, LA.FLe{LA.TVar{0n}, LA.TLit{10n}}, Con{LA.FIs{LA.BLe{LA.TVar{0n}, LA.TLit{10n}}, True{}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

law within_check_complete:
  for +x: Nat
  for +ll_h0: Within(x)
  {withinCheck(x) == True{} : Bool}

def within_check_complete(x, ll_h0):
  LA.sound(Con{x, Nil{}}, LA.FIs{LA.BLe{LA.TVar{0n}, LA.TLit{10n}}, True{}}, Con{LA.FLe{LA.TVar{0n}, LA.TLit{10n}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

def Below(+x: Nat, +y: Nat) -> Data:
  S.Sem.le(y, x)

def belowCheck(+x: Nat, +y: Nat) -> Bool:
  L.Lean.Nat.ble(y, x)

law below_check_sound:
  for +x: Nat
  for +y: Nat
  for +ll_h0: {belowCheck(x, y) == True{} : Bool}
  Below(x, y)

def below_check_sound(x, y, ll_h0):
  LA.sound(Con{y, Con{x, Nil{}}}, LA.FLe{LA.TVar{0n}, LA.TVar{1n}}, Con{LA.FIs{LA.BLe{LA.TVar{0n}, LA.TVar{1n}}, True{}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

law GuessContract.postcondition_sound:
  R.LexLeanModels.Sound2(Nat, Nat, (+ll_x179 => +ll_x180 => belowCheck(ll_x179, ll_x180)), (+ll_x181 => +ll_x182 => Below(ll_x181, ll_x182)))

def GuessContract.postcondition_sound():
  ll_a183 => ll_a184 => ll_a185 => below_check_sound(ll_a183, ll_a184, ll_a185)

law GuessContract.precondition_sound:
  R.LexLeanModels.Sound1(Nat, (+ll_x186 => withinCheck(ll_x186)), (+ll_x187 => Within(ll_x187)))

def GuessContract.precondition_sound():
  ll_a188 => ll_a189 => within_check_sound(ll_a188, ll_a189)

law GuessContract.precondition_complete:
  R.LexLeanModels.Complete1(Nat, (+ll_x190 => withinCheck(ll_x190)), (+ll_x191 => Within(ll_x191)))

def GuessContract.precondition_complete():
  ll_a192 => ll_a193 => within_check_complete(ll_a192, ll_a193)

def Guess(+x: Nat) -> Nat:
  L.Lean.Nat.sub(x, 1n)

def guessRef(+x: Nat) -> Nat:
  L.Lean.Nat.sub(x, 1n)

law guess_reference:
  for +x: Nat
  for +ll_h0: Within(x)
  {Guess(x) == guessRef(x) : Nat}

def guess_reference(x, ll_h0):
  {==}

def guessSamples() -> List<&2, L.Lean.Prod(Nat, Nat)>:
  Con{(0n, 0n), Con{(1n, 0n), Con{(2n, 1n), Con{(5n, 4n), Con{(9n, 9n), Nil{}}}}}}

def sameNat(+expected: Nat, +observed: Nat) -> Bool:
  L.Lean.Nat.beq(expected, observed)

law same_nat_sound:
  for +expected: Nat
  for +observed: Nat
  for +ll_h0: {sameNat(expected, observed) == True{} : Bool}
  {expected == observed : Nat}

def same_nat_sound(expected, observed, ll_h0):
  LA.sound(Con{expected, Con{observed, Nil{}}}, LA.FEq{LA.TVar{0n}, LA.TVar{1n}}, Con{LA.FIs{LA.BEq{LA.TVar{0n}, LA.TVar{1n}}, True{}}, Nil{}}, 9n, LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{1n, Nil{}}}}}, LA.Leaf{Con{0n, Con{1n, Con{1n, Nil{}}}}}}, {==}, (ll_h0, Unit{}))

def ll_code194(+ll_e: Unit, +count: Nat, +example: L.Lean.Prod(Nat, Nat)) -> Nat:
  S.Sem.ite(Nat, sameNat(Guess(S.Sem.fst(Nat, Nat, example)), S.Sem.snd(Nat, Nat, example)), L.Lean.Nat.add(count, 1n), count)

law guess_agreement:
  L.Lean.Prod({R.LexLeanRuntime.length.List(L.Lean.Prod(Nat, Nat), guessSamples()) == 5n : Nat}, {S.Sem.listFold(~L.Lean.Prod(Nat, Nat), ~Nat, ~Unit, ~ll_code194, Unit{}, guessSamples(), 0n) == 4n : Nat})

def guess_agreement():
  ({==}, {==})

law GuessSample.guess_agreement:
  R.LexLeanModels.Agreement(Nat, Nat, (+ll_x195 => Guess(ll_x195)), (+ll_x196 => +ll_x197 => sameNat(ll_x196, ll_x197)), guessSamples(), 5n, 4n)

def GuessSample.guess_agreement():
  ({==}, {==})

def GuessModel(+__input: Nat) -> Nat:
  Guess(__input)

law GuessEquivalence.guess_reference:
  R.LexLeanModels.Equivalent(Nat, Nat, (+ll_x198 => Within(ll_x198)), (+ll_x199 => Guess(ll_x199)), (+ll_x200 => guessRef(ll_x200)))

def GuessEquivalence.guess_reference():
  ll_a201 => ll_a202 => guess_reference(ll_a201, ll_a202)

def GuessExactModel(+__input: Nat) -> Nat:
  Guess(__input)

def Overshoot(+x: Nat) -> Nat:
  L.Lean.Nat.add(x, 1n)

def OvershootModel(+__input: Nat) -> Nat:
  Overshoot(__input)

def violationCode(+violation: S.Sem.ContractViolation) -> Nat:
  match violation:
    case S.Sem.ContractViolation.precondition{}:
      1n
    case S.Sem.ContractViolation.input_invariant{}:
      2n
    case S.Sem.ContractViolation.postcondition{}:
      3n
    case S.Sem.ContractViolation.output_invariant{}:
      4n
