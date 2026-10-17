import Base
import ../LexLeanPrelude.bend as L
import ../LexLeanSemantic.bend as S
import ../LexLeanRuntime.bend as R
import ../LexLeanLinArith.bend as LA
import ./Ledger.bend as Models_Ledger

law flow_capped_sound:
  for +s: Nat
  for +ll_h0: {Models_Ledger.cappedCheck(s) == True{} : Bool}
  Models_Ledger.Capped(s)

def flow_capped_sound(s, ll_h0):
  Models_Ledger.capped_check_sound(s, ll_h0)

law FlowContract.invariant_sound:
  R.LexLeanModels.Sound1(Nat, (+ll_x1 => Models_Ledger.cappedCheck(ll_x1)), (+ll_x2 => Models_Ledger.Capped(ll_x2)))

def FlowContract.invariant_sound():
  ll_a3 => ll_a4 => flow_capped_sound(ll_a3, ll_a4)

def ClampGuess.initial() -> Nat:
  0n

def ClampGuess(+s: Nat, +x: Nat) -> L.Lean.Prod(Nat, Result<&2, &2, S.Sem.ContractViolation, Nat>):
  +__step1 = Models_Ledger.ClampModel(s, x)
  +__stage1 = S.Sem.snd(Nat, Nat, __step1)
  +__state1 = S.Sem.fst(Nat, Nat, __step1)
  S.Sem.ite(L.Lean.Prod(Nat, Result<&2, &2, S.Sem.ContractViolation, Nat>), Models_Ledger.withinCheck(__stage1), (
    +__stage2 = Models_Ledger.GuessModel(__stage1)
    S.Sem.ite(L.Lean.Prod(Nat, Result<&2, &2, S.Sem.ContractViolation, Nat>), Models_Ledger.belowCheck(__stage1, __stage2), (__state1, Done{__stage2}), (s, Fail{S.Sem.ContractViolation.postcondition{}}))
  ), (s, Fail{S.Sem.ContractViolation.precondition{}}))

law flow_entry:
  for +s: Nat
  for +x: Nat
  for +ll_h0: Models_Ledger.Capped(s)
  Models_Ledger.Capped(s)

def flow_entry(s, x, ll_h0):
  ll_h0

def FlowModel.initial() -> Nat:
  ClampGuess.initial()

def FlowModel(+__state: Nat, +__input: Nat) -> L.Lean.Prod(Nat, Result<&2, &2, S.Sem.ContractViolation, Nat>):
  ClampGuess(__state, __input)

law pair_within_sound:
  for +x: Nat
  for +ll_h0: {Models_Ledger.withinCheck(x) == True{} : Bool}
  Models_Ledger.Within(x)

def pair_within_sound(x, ll_h0):
  Models_Ledger.within_check_sound(x, ll_h0)

law PairGuessContract.precondition_sound:
  R.LexLeanModels.Sound1(Nat, (+ll_x5 => Models_Ledger.withinCheck(ll_x5)), (+ll_x6 => Models_Ledger.Within(ll_x6)))

def PairGuessContract.precondition_sound():
  ll_a7 => ll_a8 => pair_within_sound(ll_a7, ll_a8)

def GuessTwice(+x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>:
  +__left = Models_Ledger.GuessModel(x)
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>, Models_Ledger.belowCheck(x, __left), (
    +__right = Models_Ledger.GuessExactModel(x)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>, Models_Ledger.belowCheck(x, __right), Done{(__left, __right)}, Fail{S.Sem.ContractViolation.postcondition{}})
  ), Fail{S.Sem.ContractViolation.postcondition{}})

law pair_entry_left:
  for +x: Nat
  for +ll_h0: Models_Ledger.Within(x)
  Models_Ledger.Within(x)

def pair_entry_left(x, ll_h0):
  ll_h0

law pair_entry_right:
  for +x: Nat
  for +ll_h0: Models_Ledger.Within(x)
  Models_Ledger.Within(x)

def pair_entry_right(x, ll_h0):
  ll_h0

def PairGuessModel(+__input: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>:
  GuessTwice(__input)

def GuessOvershoot(+x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>:
  +__left = Models_Ledger.GuessModel(x)
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>, Models_Ledger.belowCheck(x, __left), (
    +__right = Models_Ledger.OvershootModel(x)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>, Models_Ledger.belowCheck(x, __right), Done{(__left, __right)}, Fail{S.Sem.ContractViolation.postcondition{}})
  ), Fail{S.Sem.ContractViolation.postcondition{}})

def OvershootPairModel(+__input: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>:
  GuessOvershoot(__input)

def Few(+xs: List<&2, Nat>) -> Data:
  S.Sem.le(R.LexLeanRuntime.length.List(Nat, xs), 100n)

def fewCheck(+xs: List<&2, Nat>) -> Bool:
  L.Lean.Nat.ble(R.LexLeanRuntime.length.List(Nat, xs), 100n)

law few_check_sound:
  for +xs: List<&2, Nat>
  for +ll_h0: {fewCheck(xs) == True{} : Bool}
  Few(xs)

def few_check_sound(xs, ll_h0):
  LA.sound(Con{R.LexLeanRuntime.length.List(Nat, xs), Nil{}}, LA.FLe{LA.TVar{0n}, LA.TLit{100n}}, Con{LA.FIs{LA.BLe{LA.TVar{0n}, LA.TLit{100n}}, True{}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

law SpillStreamContract.precondition_sound:
  R.LexLeanModels.Sound1(List<&2, Nat>, (+ll_x9 => fewCheck(ll_x9)), (+ll_x10 => Few(ll_x10)))

def SpillStreamContract.precondition_sound():
  ll_a11 => ll_a12 => few_check_sound(ll_a11, ll_a12)

def ll_match13(+ll_v14: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, List<&2, Nat>)>, +__acc: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, List<&2, Nat>)>, +__item: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, List<&2, Nat>)>:
  match ll_v14:
    case Fail{__violation}:
      __acc
    case Done{__state}:
      S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, List<&2, Nat>)>, Models_Ledger.cappedCheck(S.Sem.fst(Nat, List<&2, Nat>, __state)), S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, List<&2, Nat>)>, Models_Ledger.smallCheck(S.Sem.fst(Nat, List<&2, Nat>, __state), __item), (
        +__step = Models_Ledger.SpillModel(S.Sem.fst(Nat, List<&2, Nat>, __state), __item)
        S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, List<&2, Nat>)>, Models_Ledger.cappedCheck(S.Sem.fst(Nat, Nat, __step)), Done{(S.Sem.fst(Nat, Nat, __step), R.LexLeanRuntime.append.List(Nat, S.Sem.snd(Nat, List<&2, Nat>, __state), Con{S.Sem.snd(Nat, Nat, __step), Nil{}}))}, Fail{S.Sem.ContractViolation.output_invariant{}})
      ), Fail{S.Sem.ContractViolation.precondition{}}), Fail{S.Sem.ContractViolation.input_invariant{}})

def ll_match15(+ll_v16: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, List<&2, Nat>)>) -> Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>:
  match ll_v16:
    case Fail{__violation}:
      Fail{__violation}
    case Done{__state}:
      Done{S.Sem.snd(Nat, List<&2, Nat>, __state)}

def SpillStream(+xs: List<&2, Nat>) -> Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>:
  +__scanned = S.Sem.listFold(~Nat, ~Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, List<&2, Nat>)>, ~Unit, ~(+ll_e => +__acc => +__item => ll_match13(__acc, __acc, __item)), Unit{}, xs, Done{(Models_Ledger.SpillModel.initial(), Nil{})})
  ll_match15(__scanned)

def SpillStreamModel(+__input: List<&2, Nat>) -> Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>:
  SpillStream(__input)

def TwinCapped(+s: L.Lean.Prod(Nat, Nat)) -> Data:
  Models_Ledger.Capped(S.Sem.fst(Nat, Nat, s))

def twinCappedCheck(+s: L.Lean.Prod(Nat, Nat)) -> Bool:
  Models_Ledger.cappedCheck(S.Sem.fst(Nat, Nat, s))

law twin_capped_check_sound:
  for +s: L.Lean.Prod(Nat, Nat)
  for +ll_h0: {twinCappedCheck(s) == True{} : Bool}
  TwinCapped(s)

def twin_capped_check_sound(s, ll_h0):
  LA.sound(Con{S.Sem.fst(Nat, Nat, s), Nil{}}, LA.FLe{LA.TVar{0n}, LA.TLit{100n}}, Con{LA.FIs{LA.BLe{LA.TVar{0n}, LA.TLit{100n}}, True{}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

def TwinSmall(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> Data:
  S.Sem.le(x, 10n)

def twinSmallCheck(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> Bool:
  L.Lean.Nat.ble(x, 10n)

law twin_small_check_sound:
  for +s: L.Lean.Prod(Nat, Nat)
  for +x: Nat
  for +ll_h0: {twinSmallCheck(s, x) == True{} : Bool}
  TwinSmall(s, x)

def twin_small_check_sound(s, x, ll_h0):
  LA.sound(Con{x, Nil{}}, LA.FLe{LA.TVar{0n}, LA.TLit{10n}}, Con{LA.FIs{LA.BLe{LA.TVar{0n}, LA.TLit{10n}}, True{}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

law TwinContract.invariant_sound:
  R.LexLeanModels.Sound1(L.Lean.Prod(Nat, Nat), (+ll_x17 => twinCappedCheck(ll_x17)), (+ll_x18 => TwinCapped(ll_x18)))

def TwinContract.invariant_sound():
  ll_a19 => ll_a20 => twin_capped_check_sound(ll_a19, ll_a20)

law TwinContract.precondition_sound:
  R.LexLeanModels.Sound2(L.Lean.Prod(Nat, Nat), Nat, (+ll_x21 => +ll_x22 => twinSmallCheck(ll_x21, ll_x22)), (+ll_x23 => +ll_x24 => TwinSmall(ll_x23, ll_x24)))

def TwinContract.precondition_sound():
  ll_a25 => ll_a26 => ll_a27 => twin_small_check_sound(ll_a25, ll_a26, ll_a27)

def ClampTally.initial() -> L.Lean.Prod(Nat, Nat):
  (0n, 0n)

def ClampTally(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat)):
  +__left_step = Models_Ledger.ClampModel(S.Sem.fst(Nat, Nat, s), x)
  +__left = S.Sem.snd(Nat, Nat, __left_step)
  +__left_state = S.Sem.fst(Nat, Nat, __left_step)
  +__right_step = Models_Ledger.TallyModel(S.Sem.snd(Nat, Nat, s), x)
  +__right = S.Sem.snd(Nat, Nat, __right_step)
  +__right_state = S.Sem.fst(Nat, Nat, __right_step)
  ((__left_state, __right_state), (__left, __right))

law twin_entry_left:
  for +s: L.Lean.Prod(Nat, Nat)
  for +x: Nat
  for +ll_h0: TwinCapped(s)
  for +ll_h1: TwinSmall(s, x)
  Models_Ledger.Capped(S.Sem.fst(Nat, Nat, s))

def twin_entry_left(s, x, ll_h0, ll_h1):
  ll_h0

law twin_entry_right:
  for +s: L.Lean.Prod(Nat, Nat)
  for +x: Nat
  for +ll_h0: TwinCapped(s)
  for +ll_h1: TwinSmall(s, x)
  Models_Ledger.Small(S.Sem.snd(Nat, Nat, s), x)

def twin_entry_right(s, x, ll_h0, ll_h1):
  ll_h1

def TwinModel.initial() -> L.Lean.Prod(Nat, Nat):
  ClampTally.initial()

def TwinModel(+__state: L.Lean.Prod(Nat, Nat), +__input: Nat) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat)):
  ClampTally(__state, __input)

def BothCapped(+s: L.Lean.Prod(Nat, Nat)) -> Data:
  L.Lean.Prod(Models_Ledger.Capped(S.Sem.fst(Nat, Nat, s)), Models_Ledger.Capped(S.Sem.snd(Nat, Nat, s)))

def bothCappedCheck(+s: L.Lean.Prod(Nat, Nat)) -> Bool:
  L.Lean.Nat.ble(L.Lean.Nat.add(L.Lean.Nat.sub(S.Sem.fst(Nat, Nat, s), 100n), L.Lean.Nat.sub(S.Sem.snd(Nat, Nat, s), 100n)), 0n)

law both_capped_check_sound:
  for +s: L.Lean.Prod(Nat, Nat)
  for +ll_h0: {bothCappedCheck(s) == True{} : Bool}
  BothCapped(s)

def both_capped_check_sound(s, ll_h0):
  (LA.sound(Con{S.Sem.fst(Nat, Nat, s), Con{L.Lean.Nat.sub(S.Sem.fst(Nat, Nat, s), 100n), Con{L.Lean.Nat.sub(S.Sem.snd(Nat, Nat, s), 100n), Con{S.Sem.snd(Nat, Nat, s), Nil{}}}}}, LA.FLe{LA.TVar{0n}, LA.TLit{100n}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{2n}}, Con{LA.FIs{LA.BLe{LA.TAdd{LA.TVar{1n}, LA.TVar{2n}}, LA.TLit{0n}}, True{}}, Con{LA.FSub{LA.TVar{1n}, LA.TVar{0n}, LA.TLit{100n}}, Nil{}}}}, 17n, LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{0n, Con{1n, Con{1n, Con{1n, Nil{}}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}, {==}, ({==}, (ll_h0, ({==}, Unit{})))), LA.sound(Con{S.Sem.snd(Nat, Nat, s), Con{L.Lean.Nat.sub(S.Sem.fst(Nat, Nat, s), 100n), Con{S.Sem.fst(Nat, Nat, s), Con{L.Lean.Nat.sub(S.Sem.snd(Nat, Nat, s), 100n), Nil{}}}}}, LA.FLe{LA.TVar{0n}, LA.TLit{100n}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{1n}}, Con{LA.FIs{LA.BLe{LA.TAdd{LA.TVar{1n}, LA.TVar{3n}}, LA.TLit{0n}}, True{}}, Con{LA.FSub{LA.TVar{3n}, LA.TVar{0n}, LA.TLit{100n}}, Nil{}}}}, 17n, LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{0n, Con{1n, Con{1n, Con{1n, Nil{}}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}, {==}, ({==}, (ll_h0, ({==}, Unit{})))))

law PairClampContract.invariant_sound:
  R.LexLeanModels.Sound1(L.Lean.Prod(Nat, Nat), (+ll_x28 => bothCappedCheck(ll_x28)), (+ll_x29 => BothCapped(ll_x29)))

def PairClampContract.invariant_sound():
  ll_a30 => ll_a31 => both_capped_check_sound(ll_a30, ll_a31)

def ClampBoth.initial() -> L.Lean.Prod(Nat, Nat):
  (0n, 0n)

def ClampBoth(+s: L.Lean.Prod(Nat, Nat), +x: L.Lean.Prod(Nat, Nat)) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat)):
  +__left_step = Models_Ledger.ClampModel(S.Sem.fst(Nat, Nat, s), S.Sem.fst(Nat, Nat, x))
  +__left = S.Sem.snd(Nat, Nat, __left_step)
  +__left_state = S.Sem.fst(Nat, Nat, __left_step)
  +__right_step = Models_Ledger.ClampModel(S.Sem.snd(Nat, Nat, s), S.Sem.snd(Nat, Nat, x))
  +__right = S.Sem.snd(Nat, Nat, __right_step)
  +__right_state = S.Sem.fst(Nat, Nat, __right_step)
  ((__left_state, __right_state), (__left, __right))

law both_entry_left:
  for +s: L.Lean.Prod(Nat, Nat)
  for +x: L.Lean.Prod(Nat, Nat)
  for +ll_h0: BothCapped(s)
  Models_Ledger.Capped(S.Sem.fst(Nat, Nat, s))

def both_entry_left(s, x, ll_h0):
  LA.sound(Con{S.Sem.fst(Nat, Nat, s), Con{S.Sem.snd(Nat, Nat, s), Nil{}}}, LA.FLe{LA.TVar{0n}, LA.TLit{100n}}, Con{LA.FAnd{LA.FLe{LA.TVar{0n}, LA.TLit{100n}}, LA.FLe{LA.TVar{1n}, LA.TLit{100n}}}, Nil{}}, 9n, LA.Leaf{Con{0n, Con{1n, Con{1n, Nil{}}}}}, {==}, ((S.Sem.fst(S.Sem.le(S.Sem.fst(Nat, Nat, s), 100n), S.Sem.le(S.Sem.snd(Nat, Nat, s), 100n), ll_h0), S.Sem.snd(S.Sem.le(S.Sem.fst(Nat, Nat, s), 100n), S.Sem.le(S.Sem.snd(Nat, Nat, s), 100n), ll_h0)), Unit{}))

law both_entry_right:
  for +s: L.Lean.Prod(Nat, Nat)
  for +x: L.Lean.Prod(Nat, Nat)
  for +ll_h0: BothCapped(s)
  Models_Ledger.Capped(S.Sem.snd(Nat, Nat, s))

def both_entry_right(s, x, ll_h0):
  LA.sound(Con{S.Sem.snd(Nat, Nat, s), Con{S.Sem.fst(Nat, Nat, s), Nil{}}}, LA.FLe{LA.TVar{0n}, LA.TLit{100n}}, Con{LA.FAnd{LA.FLe{LA.TVar{1n}, LA.TLit{100n}}, LA.FLe{LA.TVar{0n}, LA.TLit{100n}}}, Nil{}}, 9n, LA.Leaf{Con{1n, Con{0n, Con{1n, Nil{}}}}}, {==}, ((S.Sem.fst(S.Sem.le(S.Sem.fst(Nat, Nat, s), 100n), S.Sem.le(S.Sem.snd(Nat, Nat, s), 100n), ll_h0), S.Sem.snd(S.Sem.le(S.Sem.fst(Nat, Nat, s), 100n), S.Sem.le(S.Sem.snd(Nat, Nat, s), 100n), ll_h0)), Unit{}))

def PairClampModel.initial() -> L.Lean.Prod(Nat, Nat):
  ClampBoth.initial()

def PairClampModel(+__state: L.Lean.Prod(Nat, Nat), +__input: L.Lean.Prod(Nat, Nat)) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat)):
  ClampBoth(__state, __input)

law BranchContract.invariant_sound:
  R.LexLeanModels.Sound1(L.Lean.Prod(Nat, Nat), (+ll_x32 => twinCappedCheck(ll_x32)), (+ll_x33 => TwinCapped(ll_x33)))

def BranchContract.invariant_sound():
  ll_a34 => ll_a35 => twin_capped_check_sound(ll_a34, ll_a35)

law BranchContract.precondition_sound:
  R.LexLeanModels.Sound2(L.Lean.Prod(Nat, Nat), Nat, (+ll_x36 => +ll_x37 => twinSmallCheck(ll_x36, ll_x37)), (+ll_x38 => +ll_x39 => TwinSmall(ll_x38, ll_x39)))

def BranchContract.precondition_sound():
  ll_a40 => ll_a41 => ll_a42 => twin_small_check_sound(ll_a40, ll_a41, ll_a42)

def ClampOrTally.initial() -> L.Lean.Prod(Nat, Nat):
  (0n, 0n)

def ClampOrTally(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), Nat):
  S.Sem.ite(L.Lean.Prod(L.Lean.Prod(Nat, Nat), Nat), L.Lean.Nat.ble(x, 5n), (
    +__then_step = Models_Ledger.ClampModel(S.Sem.fst(Nat, Nat, s), x)
    (
      +__then = S.Sem.snd(Nat, Nat, __then_step)
      (
        +__then_state = S.Sem.fst(Nat, Nat, __then_step)
        ((__then_state, S.Sem.snd(Nat, Nat, s)), __then)
      )
    )
  ), (
    +__else_step = Models_Ledger.TallyModel(S.Sem.snd(Nat, Nat, s), x)
    (
      +__else = S.Sem.snd(Nat, Nat, __else_step)
      (
        +__else_state = S.Sem.fst(Nat, Nat, __else_step)
        ((S.Sem.fst(Nat, Nat, s), __else_state), __else)
      )
    )
  ))

law branch_entry_then:
  for +s: L.Lean.Prod(Nat, Nat)
  for +x: Nat
  for +ll_h0: TwinCapped(s)
  for +ll_h1: TwinSmall(s, x)
  for +ll_h2: {L.Lean.Nat.ble(x, 5n) == True{} : Bool}
  Models_Ledger.Capped(S.Sem.fst(Nat, Nat, s))

def branch_entry_then(s, x, ll_h0, ll_h1, ll_h2):
  ll_h0

law branch_entry_else:
  for +s: L.Lean.Prod(Nat, Nat)
  for +x: Nat
  for +ll_h0: TwinCapped(s)
  for +ll_h1: TwinSmall(s, x)
  for +ll_h2: {L.Lean.Nat.ble(x, 5n) == False{} : Bool}
  Models_Ledger.Small(S.Sem.snd(Nat, Nat, s), x)

def branch_entry_else(s, x, ll_h0, ll_h1, ll_h2):
  ll_h1

def BranchModel.initial() -> L.Lean.Prod(Nat, Nat):
  ClampOrTally.initial()

def BranchModel(+__state: L.Lean.Prod(Nat, Nat), +__input: Nat) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), Nat):
  ClampOrTally(__state, __input)

law ChainContract.invariant_sound:
  R.LexLeanModels.Sound1(L.Lean.Prod(Nat, Nat), (+ll_x43 => twinCappedCheck(ll_x43)), (+ll_x44 => TwinCapped(ll_x44)))

def ChainContract.invariant_sound():
  ll_a45 => ll_a46 => twin_capped_check_sound(ll_a45, ll_a46)

law ChainContract.precondition_sound:
  R.LexLeanModels.Sound2(L.Lean.Prod(Nat, Nat), Nat, (+ll_x47 => +ll_x48 => twinSmallCheck(ll_x47, ll_x48)), (+ll_x49 => +ll_x50 => TwinSmall(ll_x49, ll_x50)))

def ChainContract.precondition_sound():
  ll_a51 => ll_a52 => ll_a53 => twin_small_check_sound(ll_a51, ll_a52, ll_a53)

law spill_tally:
  for +s: L.Lean.Prod(Nat, Nat)
  for +x: Nat
  for +ll_h0: Models_Ledger.Capped(S.Sem.fst(Nat, Nat, s))
  for +ll_h1: Models_Ledger.Small(S.Sem.fst(Nat, Nat, s), x)
  Models_Ledger.Small(S.Sem.snd(Nat, Nat, s), S.Sem.snd(Nat, Nat, Models_Ledger.SpillModel(S.Sem.fst(Nat, Nat, s), x)))

def spill_tally(s, x, ll_h0, ll_h1):
  ll_h1

def SpillTally.initial() -> L.Lean.Prod(Nat, Nat):
  (0n, 0n)

def SpillTally(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>):
  +__step1 = Models_Ledger.SpillModel(S.Sem.fst(Nat, Nat, s), x)
  +__stage1 = S.Sem.snd(Nat, Nat, __step1)
  +__state1 = S.Sem.fst(Nat, Nat, __step1)
  S.Sem.ite(L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>), Models_Ledger.cappedCheck(__state1), (
    +__step2 = Models_Ledger.TallyModel(S.Sem.snd(Nat, Nat, s), __stage1)
    (
      +__stage2 = S.Sem.snd(Nat, Nat, __step2)
      (
        +__state2 = S.Sem.fst(Nat, Nat, __step2)
        ((__state1, __state2), Done{__stage2})
      )
    )
  ), (s, Fail{S.Sem.ContractViolation.output_invariant{}}))

law chain_entry_invariant:
  for +s: L.Lean.Prod(Nat, Nat)
  for +x: Nat
  for +ll_h0: TwinCapped(s)
  for +ll_h1: TwinSmall(s, x)
  Models_Ledger.Capped(S.Sem.fst(Nat, Nat, s))

def chain_entry_invariant(s, x, ll_h0, ll_h1):
  ll_h0

law chain_entry_precondition:
  for +s: L.Lean.Prod(Nat, Nat)
  for +x: Nat
  for +ll_h0: TwinCapped(s)
  for +ll_h1: TwinSmall(s, x)
  Models_Ledger.Small(S.Sem.fst(Nat, Nat, s), x)

def chain_entry_precondition(s, x, ll_h0, ll_h1):
  ll_h1

def ChainModel.initial() -> L.Lean.Prod(Nat, Nat):
  SpillTally.initial()

def ChainModel(+__state: L.Lean.Prod(Nat, Nat), +__input: Nat) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>):
  SpillTally(__state, __input)

law RawChainContract.invariant_sound:
  R.LexLeanModels.Sound1(L.Lean.Prod(Nat, Nat), (+ll_x54 => twinCappedCheck(ll_x54)), (+ll_x55 => TwinCapped(ll_x55)))

def RawChainContract.invariant_sound():
  ll_a56 => ll_a57 => twin_capped_check_sound(ll_a56, ll_a57)

def TallySpillRaw.initial() -> L.Lean.Prod(Nat, Nat):
  (0n, 0n)

def TallySpillRaw(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>):
  +__step1 = Models_Ledger.FreeModel(S.Sem.fst(Nat, Nat, s), x)
  +__stage1 = S.Sem.snd(Nat, Nat, __step1)
  +__state1 = S.Sem.fst(Nat, Nat, __step1)
  S.Sem.ite(L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>), Models_Ledger.cappedCheck(S.Sem.snd(Nat, Nat, s)), S.Sem.ite(L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>), Models_Ledger.smallCheck(S.Sem.snd(Nat, Nat, s), __stage1), (
    +__step2 = Models_Ledger.SpillRawModel(S.Sem.snd(Nat, Nat, s), __stage1)
    (
      +__stage2 = S.Sem.snd(Nat, Nat, __step2)
      (
        +__state2 = S.Sem.fst(Nat, Nat, __step2)
        S.Sem.ite(L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>), Models_Ledger.cappedCheck(__state2), S.Sem.ite(L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>), Models_Ledger.growsCheck(S.Sem.snd(Nat, Nat, s), __stage1, __state2, __stage2), ((__state1, __state2), Done{__stage2}), (s, Fail{S.Sem.ContractViolation.postcondition{}})), (s, Fail{S.Sem.ContractViolation.output_invariant{}}))
      )
    )
  ), (s, Fail{S.Sem.ContractViolation.precondition{}})), (s, Fail{S.Sem.ContractViolation.input_invariant{}}))

def RawChainModel.initial() -> L.Lean.Prod(Nat, Nat):
  TallySpillRaw.initial()

def RawChainModel(+__state: L.Lean.Prod(Nat, Nat), +__input: Nat) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>):
  TallySpillRaw(__state, __input)

def Drain.initial() -> Nat:
  0n

def Drain(+s: Nat, +x: Nat) -> L.Lean.Prod(Nat, Nat):
  (L.Lean.Nat.sub(s, x), x)

def DrainModel.initial() -> Nat:
  Drain.initial()

def DrainModel(+__state: Nat, +__input: Nat) -> L.Lean.Prod(Nat, Nat):
  Drain(__state, __input)

def TallyDrain.initial() -> L.Lean.Prod(Nat, Nat):
  (0n, 0n)

def TallyDrain(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>):
  +__step1 = Models_Ledger.FreeModel(S.Sem.fst(Nat, Nat, s), x)
  +__stage1 = S.Sem.snd(Nat, Nat, __step1)
  +__state1 = S.Sem.fst(Nat, Nat, __step1)
  +__step2 = DrainModel(S.Sem.snd(Nat, Nat, s), __stage1)
  +__stage2 = S.Sem.snd(Nat, Nat, __step2)
  +__state2 = S.Sem.fst(Nat, Nat, __step2)
  S.Sem.ite(L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>), Models_Ledger.growsCheck(S.Sem.snd(Nat, Nat, s), __stage1, __state2, __stage2), ((__state1, __state2), Done{__stage2}), (s, Fail{S.Sem.ContractViolation.postcondition{}}))

def DrainChainModel.initial() -> L.Lean.Prod(Nat, Nat):
  TallyDrain.initial()

def DrainChainModel(+__state: L.Lean.Prod(Nat, Nat), +__input: Nat) -> L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>):
  TallyDrain(__state, __input)
