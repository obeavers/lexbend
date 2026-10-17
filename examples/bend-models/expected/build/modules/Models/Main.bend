import Base
import ../LexLeanPrelude.bend as L
import ../LexLeanSemantic.bend as S
import ../LexLeanRuntime.bend as R
import ./Flows.bend as Models_Flows
import ./Glyphs.bend as Models_Glyphs
import ./Ledger.bend as Models_Ledger
import ./Pipeline.bend as Models_Pipeline
import ./Recognizer.bend as Models_Recognizer
import ./Session.bend as Models_Session
import ./Triage.bend as Models_Triage

def classify(+glyph: Models_Glyphs.Glyph) -> Nat:
  Models_Recognizer.DigitModel(glyph)

def classifyChecked(+glyph: Models_Glyphs.Glyph) -> Result<&2, &2, S.Sem.ContractViolation, Nat>:
  +__checked1_input = glyph
  +__checked1_output = Models_Recognizer.RawDigitModel(__checked1_input)
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, Nat>, Models_Recognizer.recognizesCheck(__checked1_input, __checked1_output), Done{__checked1_output}, Fail{S.Sem.ContractViolation.postcondition{}})

def respond(+presentation: Models_Triage.Presentation) -> Result<&2, &2, S.Sem.ContractViolation, Nat>:
  +__checked1_input = presentation
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, Nat>, Models_Triage.symptomaticCheck(__checked1_input), (
    +__checked1_output = Models_Pipeline.PipelineModel(__checked1_input)
    Done{__checked1_output}
  ), Fail{S.Sem.ContractViolation.precondition{}})

def admitCosts(+costs: List<&2, Nat>) -> Result<&2, &2, S.Sem.ContractViolation, Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>>:
  +__checked1_input = costs
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>>, Models_Pipeline.shortStreamCheck(__checked1_input), (
    +__checked1_output = Models_Pipeline.StreamModel(__checked1_input)
    Done{__checked1_output}
  ), Fail{S.Sem.ContractViolation.precondition{}})

def step(+window: Models_Session.ll.Window, +cost: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, Nat)>:
  +__checked1_state = window
  +__checked1_input = cost
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, Nat)>, Models_Session.boundedCheck(__checked1_state), S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, Nat)>, Models_Session.affordableCheck(__checked1_state, __checked1_input), (
    +__checked1_step = Models_Session.SessionModel(__checked1_state, __checked1_input)
    Done{__checked1_step}
  ), Fail{S.Sem.ContractViolation.precondition{}}), Fail{S.Sem.ContractViolation.input_invariant{}})

law classify_eight:
  {classify(Models_Glyphs.Glyph.g8{}) == 8n : Nat}

def classify_eight():
  {==}

def admission(+outcome: Result<&2, &2, S.Sem.ContractViolation, Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>>) -> Nat:
  match outcome:
    case Fail{violation}:
      0n
    case Done{scanned}:
      match scanned:
        case Fail{violation}:
          1n
        case Done{overflows}:
          2n

law admit_rejects_costly:
  {admission(admitCosts(Con{3n, Con{40n, Nil{}}})) == 1n : Nat}

def admit_rejects_costly():
  {==}

law admit_accepts_cheap:
  {admission(admitCosts(Con{3n, Con{16n, Con{9n, Nil{}}}})) == 2n : Nat}

def admit_accepts_cheap():
  {==}

def ledgerPost(+s: Nat, +x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>:
  +__checked1_state = s
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>, Models_Ledger.cappedCheck(__checked1_state), S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>, Models_Ledger.smallCheck(__checked1_state, __checked1_input), (
    +__checked1_step = Models_Ledger.SpillModel(__checked1_state, __checked1_input)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>, Models_Ledger.cappedCheck(S.Sem.fst(Nat, Nat, __checked1_step)), Done{__checked1_step}, Fail{S.Sem.ContractViolation.output_invariant{}})
  ), Fail{S.Sem.ContractViolation.precondition{}}), Fail{S.Sem.ContractViolation.input_invariant{}})

def ledgerFull(+s: Nat, +x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>:
  +__checked1_state = s
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>, Models_Ledger.cappedCheck(__checked1_state), S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>, Models_Ledger.smallCheck(__checked1_state, __checked1_input), (
    +__checked1_step = Models_Ledger.SpillRawModel(__checked1_state, __checked1_input)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>, Models_Ledger.cappedCheck(S.Sem.fst(Nat, Nat, __checked1_step)), S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>, Models_Ledger.growsCheck(__checked1_state, __checked1_input, S.Sem.fst(Nat, Nat, __checked1_step), S.Sem.snd(Nat, Nat, __checked1_step)), Done{__checked1_step}, Fail{S.Sem.ContractViolation.postcondition{}}), Fail{S.Sem.ContractViolation.output_invariant{}})
  ), Fail{S.Sem.ContractViolation.precondition{}}), Fail{S.Sem.ContractViolation.input_invariant{}})

def guessChecked(+x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, Nat>:
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, Nat>, Models_Ledger.withinCheck(__checked1_input), (
    +__checked1_output = Models_Ledger.GuessModel(__checked1_input)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, Nat>, Models_Ledger.belowCheck(__checked1_input, __checked1_output), Done{__checked1_output}, Fail{S.Sem.ContractViolation.postcondition{}})
  ), Fail{S.Sem.ContractViolation.precondition{}})

def overshootChecked(+x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, Nat>:
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, Nat>, Models_Ledger.withinCheck(__checked1_input), (
    +__checked1_output = Models_Ledger.OvershootModel(__checked1_input)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, Nat>, Models_Ledger.belowCheck(__checked1_input, __checked1_output), Done{__checked1_output}, Fail{S.Sem.ContractViolation.postcondition{}})
  ), Fail{S.Sem.ContractViolation.precondition{}})

def flowStep(+s: Nat, +x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Result<&2, &2, S.Sem.ContractViolation, Nat>)>:
  +__checked1_state = s
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Result<&2, &2, S.Sem.ContractViolation, Nat>)>, Models_Ledger.cappedCheck(__checked1_state), (
    +__checked1_step = Models_Flows.FlowModel(__checked1_state, __checked1_input)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Result<&2, &2, S.Sem.ContractViolation, Nat>)>, Models_Ledger.cappedCheck(S.Sem.fst(Nat, Result<&2, &2, S.Sem.ContractViolation, Nat>, __checked1_step)), Done{__checked1_step}, Fail{S.Sem.ContractViolation.output_invariant{}})
  ), Fail{S.Sem.ContractViolation.input_invariant{}})

def guessTwice(+x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>>:
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>>, Models_Ledger.withinCheck(__checked1_input), (
    +__checked1_output = Models_Flows.PairGuessModel(__checked1_input)
    Done{__checked1_output}
  ), Fail{S.Sem.ContractViolation.precondition{}})

def guessOvershoot(+x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>>:
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>>, Models_Ledger.withinCheck(__checked1_input), (
    +__checked1_output = Models_Flows.OvershootPairModel(__checked1_input)
    Done{__checked1_output}
  ), Fail{S.Sem.ContractViolation.precondition{}})

def twinStep(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat))>:
  +__checked1_state = s
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat))>, Models_Flows.twinCappedCheck(__checked1_state), S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat))>, Models_Flows.twinSmallCheck(__checked1_state, __checked1_input), (
    +__checked1_step = Models_Flows.TwinModel(__checked1_state, __checked1_input)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat))>, Models_Flows.twinCappedCheck(S.Sem.fst(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat), __checked1_step)), Done{__checked1_step}, Fail{S.Sem.ContractViolation.output_invariant{}})
  ), Fail{S.Sem.ContractViolation.precondition{}}), Fail{S.Sem.ContractViolation.input_invariant{}})

def pairClamp(+s: L.Lean.Prod(Nat, Nat), +x: L.Lean.Prod(Nat, Nat)) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat))>:
  +__checked1_state = s
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat))>, Models_Flows.bothCappedCheck(__checked1_state), (
    +__checked1_step = Models_Flows.PairClampModel(__checked1_state, __checked1_input)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat))>, Models_Flows.bothCappedCheck(S.Sem.fst(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat), __checked1_step)), Done{__checked1_step}, Fail{S.Sem.ContractViolation.output_invariant{}})
  ), Fail{S.Sem.ContractViolation.input_invariant{}})

def branchStep(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Nat)>:
  +__checked1_state = s
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Nat)>, Models_Flows.twinCappedCheck(__checked1_state), S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Nat)>, Models_Flows.twinSmallCheck(__checked1_state, __checked1_input), (
    +__checked1_step = Models_Flows.BranchModel(__checked1_state, __checked1_input)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Nat)>, Models_Flows.twinCappedCheck(S.Sem.fst(L.Lean.Prod(Nat, Nat), Nat, __checked1_step)), Done{__checked1_step}, Fail{S.Sem.ContractViolation.output_invariant{}})
  ), Fail{S.Sem.ContractViolation.precondition{}}), Fail{S.Sem.ContractViolation.input_invariant{}})

def chainStep(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>)>:
  +__checked1_state = s
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>)>, Models_Flows.twinCappedCheck(__checked1_state), S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>)>, Models_Flows.twinSmallCheck(__checked1_state, __checked1_input), (
    +__checked1_step = Models_Flows.ChainModel(__checked1_state, __checked1_input)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>)>, Models_Flows.twinCappedCheck(S.Sem.fst(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>, __checked1_step)), Done{__checked1_step}, Fail{S.Sem.ContractViolation.output_invariant{}})
  ), Fail{S.Sem.ContractViolation.precondition{}}), Fail{S.Sem.ContractViolation.input_invariant{}})

def rawChainStep(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>)>:
  +__checked1_state = s
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>)>, Models_Flows.twinCappedCheck(__checked1_state), (
    +__checked1_step = Models_Flows.RawChainModel(__checked1_state, __checked1_input)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>)>, Models_Flows.twinCappedCheck(S.Sem.fst(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>, __checked1_step)), Done{__checked1_step}, Fail{S.Sem.ContractViolation.output_invariant{}})
  ), Fail{S.Sem.ContractViolation.input_invariant{}})

def drainChainStep(+s: L.Lean.Prod(Nat, Nat), +x: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>)>:
  +__checked1_state = s
  +__checked1_input = x
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>)>, Models_Flows.twinCappedCheck(__checked1_state), (
    +__checked1_step = Models_Flows.DrainChainModel(__checked1_state, __checked1_input)
    S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>)>, Models_Flows.twinCappedCheck(S.Sem.fst(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>, __checked1_step)), Done{__checked1_step}, Fail{S.Sem.ContractViolation.output_invariant{}})
  ), Fail{S.Sem.ContractViolation.input_invariant{}})

def spillStream(+xs: List<&2, Nat>) -> Result<&2, &2, S.Sem.ContractViolation, Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>>:
  +__checked1_input = xs
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>>, Models_Flows.fewCheck(__checked1_input), (
    +__checked1_output = Models_Flows.SpillStreamModel(__checked1_input)
    Done{__checked1_output}
  ), Fail{S.Sem.ContractViolation.precondition{}})

def stepCode(+outcome: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>) -> Nat:
  match outcome:
    case Fail{violation}:
      Models_Ledger.violationCode(violation)
    case Done{pair}:
      L.Lean.Nat.add(100n, S.Sem.fst(Nat, Nat, pair))

def valueCode(+outcome: Result<&2, &2, S.Sem.ContractViolation, Nat>) -> Nat:
  match outcome:
    case Fail{violation}:
      Models_Ledger.violationCode(violation)
    case Done{value}:
      L.Lean.Nat.add(100n, value)

def flowCode(+outcome: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Result<&2, &2, S.Sem.ContractViolation, Nat>)>) -> Nat:
  match outcome:
    case Fail{violation}:
      Models_Ledger.violationCode(violation)
    case Done{pair}:
      L.Lean.Nat.add(1000n, L.Lean.Nat.add(L.Lean.Nat.mul(S.Sem.fst(Nat, Result<&2, &2, S.Sem.ContractViolation, Nat>, pair), 1000n), valueCode(S.Sem.snd(Nat, Result<&2, &2, S.Sem.ContractViolation, Nat>, pair))))

def quadCode(+outcome: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat))>) -> Nat:
  match outcome:
    case Fail{violation}:
      Models_Ledger.violationCode(violation)
    case Done{p}:
      L.Lean.Nat.add(L.Lean.Nat.mul(S.Sem.fst(Nat, Nat, S.Sem.fst(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat), p)), 1000000000n), L.Lean.Nat.add(L.Lean.Nat.mul(S.Sem.snd(Nat, Nat, S.Sem.fst(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat), p)), 1000000n), L.Lean.Nat.add(L.Lean.Nat.mul(S.Sem.fst(Nat, Nat, S.Sem.snd(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat), p)), 1000n), S.Sem.snd(Nat, Nat, S.Sem.snd(L.Lean.Prod(Nat, Nat), L.Lean.Prod(Nat, Nat), p)))))

def branchCode(+outcome: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Nat)>) -> Nat:
  match outcome:
    case Fail{violation}:
      Models_Ledger.violationCode(violation)
    case Done{p}:
      L.Lean.Nat.add(L.Lean.Nat.mul(S.Sem.fst(Nat, Nat, S.Sem.fst(L.Lean.Prod(Nat, Nat), Nat, p)), 1000000n), L.Lean.Nat.add(L.Lean.Nat.mul(S.Sem.snd(Nat, Nat, S.Sem.fst(L.Lean.Prod(Nat, Nat), Nat, p)), 1000n), S.Sem.snd(L.Lean.Prod(Nat, Nat), Nat, p)))

def chainCode(+outcome: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>)>) -> Nat:
  match outcome:
    case Fail{violation}:
      Models_Ledger.violationCode(violation)
    case Done{p}:
      L.Lean.Nat.add(L.Lean.Nat.mul(S.Sem.fst(Nat, Nat, S.Sem.fst(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>, p)), 1000000n), L.Lean.Nat.add(L.Lean.Nat.mul(S.Sem.snd(Nat, Nat, S.Sem.fst(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>, p)), 1000n), valueCode(S.Sem.snd(L.Lean.Prod(Nat, Nat), Result<&2, &2, S.Sem.ContractViolation, Nat>, p))))

def twiceCode(+outcome: Result<&2, &2, S.Sem.ContractViolation, Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Nat, Nat)>>) -> Nat:
  match outcome:
    case Fail{violation}:
      Models_Ledger.violationCode(violation)
    case Done{inner}:
      match inner:
        case Fail{violation}:
          L.Lean.Nat.add(10n, Models_Ledger.violationCode(violation))
        case Done{values}:
          L.Lean.Nat.add(100n, L.Lean.Nat.add(L.Lean.Nat.mul(S.Sem.fst(Nat, Nat, values), 10n), S.Sem.snd(Nat, Nat, values)))

def streamCode(+outcome: Result<&2, &2, S.Sem.ContractViolation, Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>>) -> Nat:
  match outcome:
    case Fail{violation}:
      Models_Ledger.violationCode(violation)
    case Done{inner}:
      match inner:
        case Fail{violation}:
          L.Lean.Nat.add(10n, Models_Ledger.violationCode(violation))
        case Done{values}:
          L.Lean.Nat.add(100n, R.LexLeanRuntime.length.List(Nat, values))

law ledger_accepts:
  {stepCode(ledgerPost(5n, 3n)) == 108n : Nat}

def ledger_accepts():
  {==}

law ledger_refuses_input:
  {stepCode(ledgerPost(200n, 1n)) == 2n : Nat}

def ledger_refuses_input():
  {==}

law ledger_refuses_precondition:
  {stepCode(ledgerPost(5n, 20n)) == 1n : Nat}

def ledger_refuses_precondition():
  {==}

law ledger_refuses_output:
  {stepCode(ledgerPost(95n, 9n)) == 4n : Nat}

def ledger_refuses_output():
  {==}

law ledger_full_accepts:
  {stepCode(ledgerFull(5n, 3n)) == 108n : Nat}

def ledger_full_accepts():
  {==}

law ledger_full_refuses_output:
  {stepCode(ledgerFull(95n, 9n)) == 4n : Nat}

def ledger_full_refuses_output():
  {==}

law guess_accepts:
  {valueCode(guessChecked(5n)) == 104n : Nat}

def guess_accepts():
  {==}

law guess_refuses_precondition:
  {valueCode(guessChecked(20n)) == 1n : Nat}

def guess_refuses_precondition():
  {==}

law overshoot_refuses_postcondition:
  {valueCode(overshootChecked(3n)) == 3n : Nat}

def overshoot_refuses_postcondition():
  {==}

law flow_accepts:
  {flowCode(flowStep(5n, 3n)) == 9107n : Nat}

def flow_accepts():
  {==}

law flow_refuses_junction:
  {flowCode(flowStep(5n, 30n)) == 6001n : Nat}

def flow_refuses_junction():
  {==}

law flow_refuses_input:
  {flowCode(flowStep(200n, 1n)) == 2n : Nat}

def flow_refuses_input():
  {==}

law twice_accepts:
  {twiceCode(guessTwice(4n)) == 133n : Nat}

def twice_accepts():
  {==}

law twice_refuses:
  {twiceCode(guessTwice(40n)) == 1n : Nat}

def twice_refuses():
  {==}

law overshoot_pair_refuses_postcondition:
  {twiceCode(guessOvershoot(4n)) == 13n : Nat}

def overshoot_pair_refuses_postcondition():
  {==}

law twin_refuses_precondition:
  {quadCode(twinStep((5n, 7n), 30n)) == 1n : Nat}

def twin_refuses_precondition():
  {==}

law twin_refuses_input:
  {quadCode(twinStep((200n, 7n), 3n)) == 2n : Nat}

def twin_refuses_input():
  {==}

law pair_clamp_refuses_input:
  {quadCode(pairClamp((5n, 200n), (1n, 1n))) == 2n : Nat}

def pair_clamp_refuses_input():
  {==}

law branch_refuses_precondition:
  {branchCode(branchStep((5n, 7n), 20n)) == 1n : Nat}

def branch_refuses_precondition():
  {==}

law chain_refuses_precondition:
  {chainCode(chainStep((5n, 7n), 30n)) == 1n : Nat}

def chain_refuses_precondition():
  {==}

law stream_accepts:
  {streamCode(spillStream(Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Nil{}}}}}}}}}}})) == 110n : Nat}

def stream_accepts():
  {==}

law stream_refuses_output:
  {streamCode(spillStream(Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Con{10n, Nil{}}}}}}}}}}}})) == 14n : Nat}

def stream_refuses_output():
  {==}
