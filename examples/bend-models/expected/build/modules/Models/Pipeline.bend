import Base
import ../LexLeanPrelude.bend as L
import ../LexLeanSemantic.bend as S
import ../LexLeanRuntime.bend as R
import ../LexLeanLinArith.bend as LA
import ./Glyphs.bend as Models_Glyphs
import ./Policy.bend as Models_Policy
import ./Recognizer.bend as Models_Recognizer
import ./Session.bend as Models_Session
import ./Triage.bend as Models_Triage

def Responds(+presentation: Models_Triage.Presentation, +action: Nat) -> Data:
  S.Sem.le(1n, action)

law symptomatic_sound:
  for +presentation: Models_Triage.Presentation
  for +ll_h0: {Models_Triage.symptomaticCheck(presentation) == True{} : Bool}
  Models_Triage.Symptomatic(presentation)

def symptomatic_sound(presentation, ll_h0):
  Models_Triage.symptomatic_check_sound(presentation, ll_h0)

law PipelineContract.precondition_sound:
  R.LexLeanModels.Sound1(Models_Triage.Presentation, (+ll_x1 => Models_Triage.symptomaticCheck(ll_x1)), (+ll_x2 => Models_Triage.Symptomatic(ll_x2)))

def PipelineContract.precondition_sound():
  ll_a3 => ll_a4 => symptomatic_sound(ll_a3, ll_a4)

law triage_actionable:
  for +presentation: Models_Triage.Presentation
  for +ll_h0: Models_Triage.Symptomatic(presentation)
  Models_Policy.Actionable(Models_Triage.TriageModel(presentation))

def triage_actionable(presentation, ll_h0):
  match presentation:
    case Models_Triage.Presentation.p0{}:
      S.Sem.false_ne_true(Models_Policy.Actionable(Models_Triage.TriageModel(Models_Triage.Presentation.p0{})), ll_h0)
    case Models_Triage.Presentation.p1{}:
      {==}
    case Models_Triage.Presentation.p2{}:
      {==}
    case Models_Triage.Presentation.p3{}:
      {==}
    case Models_Triage.Presentation.p4{}:
      {==}
    case Models_Triage.Presentation.p5{}:
      {==}
    case Models_Triage.Presentation.p6{}:
      {==}
    case Models_Triage.Presentation.p7{}:
      {==}

def TriagePipeline(+presentation: Models_Triage.Presentation) -> Nat:
  +__stage1 = Models_Triage.TriageModel(presentation)
  +__stage2 = Models_Policy.PolicyModel(__stage1)
  __stage2

law pipeline_entry:
  for +presentation: Models_Triage.Presentation
  for +ll_h0: Models_Triage.Symptomatic(presentation)
  Models_Triage.Symptomatic(presentation)

def pipeline_entry(presentation, ll_h0):
  ll_h0

law pipeline_responds:
  for +presentation: Models_Triage.Presentation
  for +ll_h0: Models_Triage.Symptomatic(presentation)
  Responds(presentation, TriagePipeline(presentation))

def pipeline_responds(presentation, ll_h0):
  match presentation:
    case Models_Triage.Presentation.p0{}:
      S.Sem.false_ne_true(Responds(Models_Triage.Presentation.p0{}, TriagePipeline(Models_Triage.Presentation.p0{})), ll_h0)
    case Models_Triage.Presentation.p1{}:
      {==}
    case Models_Triage.Presentation.p2{}:
      {==}
    case Models_Triage.Presentation.p3{}:
      {==}
    case Models_Triage.Presentation.p4{}:
      {==}
    case Models_Triage.Presentation.p5{}:
      {==}
    case Models_Triage.Presentation.p6{}:
      {==}
    case Models_Triage.Presentation.p7{}:
      {==}

law PipelineEvidence.pipeline_responds:
  R.LexLeanModels.Satisfies(Models_Triage.Presentation, Nat, (+ll_x5 => Models_Triage.Symptomatic(ll_x5)), (+ll_x6 => +ll_x7 => Responds(ll_x6, ll_x7)), (+ll_x8 => TriagePipeline(ll_x8)))

def PipelineEvidence.pipeline_responds():
  ll_a9 => ll_a10 => pipeline_responds(ll_a9, ll_a10)

def PipelineModel(+__input: Models_Triage.Presentation) -> Nat:
  TriagePipeline(__input)

def resultCode(+outcome: Result<&2, &2, S.Sem.ContractViolation, Nat>) -> Nat:
  match outcome:
    case Fail{violation}:
      0n
    case Done{action}:
      action

def Answered(+presentation: Models_Triage.Presentation, +outcome: Result<&2, &2, S.Sem.ContractViolation, Nat>) -> Data:
  S.Sem.le(resultCode(outcome), 2n)

def CheckedPipeline(+presentation: Models_Triage.Presentation) -> Result<&2, &2, S.Sem.ContractViolation, Nat>:
  +__stage1 = Models_Triage.TriageModel(presentation)
  S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, Nat>, Models_Policy.actionableCheck(__stage1), (
    +__stage2 = Models_Policy.PolicyModel(__stage1)
    Done{__stage2}
  ), Fail{S.Sem.ContractViolation.precondition{}})

law checked_answers:
  for +presentation: Models_Triage.Presentation
  for +ll_h0: Models_Triage.Symptomatic(presentation)
  Answered(presentation, CheckedPipeline(presentation))

def checked_answers(presentation, ll_h0):
  match presentation:
    case Models_Triage.Presentation.p0{}:
      S.Sem.false_ne_true(Answered(Models_Triage.Presentation.p0{}, CheckedPipeline(Models_Triage.Presentation.p0{})), ll_h0)
    case Models_Triage.Presentation.p1{}:
      {==}
    case Models_Triage.Presentation.p2{}:
      {==}
    case Models_Triage.Presentation.p3{}:
      {==}
    case Models_Triage.Presentation.p4{}:
      {==}
    case Models_Triage.Presentation.p5{}:
      {==}
    case Models_Triage.Presentation.p6{}:
      {==}
    case Models_Triage.Presentation.p7{}:
      {==}

law CheckedEvidence.checked_answers:
  R.LexLeanModels.Satisfies(Models_Triage.Presentation, Result<&2, &2, S.Sem.ContractViolation, Nat>, (+ll_x11 => Models_Triage.Symptomatic(ll_x11)), (+ll_x12 => +ll_x13 => Answered(ll_x12, ll_x13)), (+ll_x14 => CheckedPipeline(ll_x14)))

def CheckedEvidence.checked_answers():
  ll_a15 => ll_a16 => checked_answers(ll_a15, ll_a16)

def CheckedModel(+__input: Models_Triage.Presentation) -> Result<&2, &2, S.Sem.ContractViolation, Nat>:
  CheckedPipeline(__input)

def Lit(+glyph: Models_Glyphs.Glyph, +segments: Nat) -> Data:
  S.Sem.le(segments, 7n)

def SegmentCounter(+glyph: Models_Glyphs.Glyph) -> Nat:
  Models_Glyphs.segmentCount(glyph)

law segments_lit:
  for +glyph: Models_Glyphs.Glyph
  Lit(glyph, SegmentCounter(glyph))

def segments_lit(glyph):
  match glyph:
    case Models_Glyphs.Glyph.g0{}:
      {==}
    case Models_Glyphs.Glyph.g1{}:
      {==}
    case Models_Glyphs.Glyph.g2{}:
      {==}
    case Models_Glyphs.Glyph.g3{}:
      {==}
    case Models_Glyphs.Glyph.g4{}:
      {==}
    case Models_Glyphs.Glyph.g5{}:
      {==}
    case Models_Glyphs.Glyph.g6{}:
      {==}
    case Models_Glyphs.Glyph.g7{}:
      {==}
    case Models_Glyphs.Glyph.g8{}:
      {==}
    case Models_Glyphs.Glyph.g9{}:
      {==}

law SegmentEvidence.segments_lit:
  R.LexLeanModels.SatisfiesTotal(Models_Glyphs.Glyph, Nat, (+ll_x17 => +ll_x18 => Lit(ll_x17, ll_x18)), (+ll_x19 => SegmentCounter(ll_x19)))

def SegmentEvidence.segments_lit():
  ll_a20 => segments_lit(ll_a20)

def SegmentModel(+__input: Models_Glyphs.Glyph) -> Nat:
  SegmentCounter(__input)

def Reported(+glyph: Models_Glyphs.Glyph, +report: L.Lean.Prod(Nat, Nat)) -> Data:
  L.Lean.Prod(Models_Recognizer.Recognizes(glyph, S.Sem.fst(Nat, Nat, report)), S.Sem.le(S.Sem.snd(Nat, Nat, report), 7n))

def GlyphReport(+glyph: Models_Glyphs.Glyph) -> L.Lean.Prod(Nat, Nat):
  (Models_Recognizer.DigitModel(glyph), SegmentModel(glyph))

law report_correct:
  for +glyph: Models_Glyphs.Glyph
  Reported(glyph, GlyphReport(glyph))

def report_correct(glyph):
  match glyph:
    case Models_Glyphs.Glyph.g0{}:
      ({==}, {==})
    case Models_Glyphs.Glyph.g1{}:
      ({==}, {==})
    case Models_Glyphs.Glyph.g2{}:
      ({==}, {==})
    case Models_Glyphs.Glyph.g3{}:
      ({==}, {==})
    case Models_Glyphs.Glyph.g4{}:
      ({==}, {==})
    case Models_Glyphs.Glyph.g5{}:
      ({==}, {==})
    case Models_Glyphs.Glyph.g6{}:
      ({==}, {==})
    case Models_Glyphs.Glyph.g7{}:
      ({==}, {==})
    case Models_Glyphs.Glyph.g8{}:
      ({==}, {==})
    case Models_Glyphs.Glyph.g9{}:
      ({==}, {==})

law ReportEvidence.report_correct:
  R.LexLeanModels.SatisfiesTotal(Models_Glyphs.Glyph, L.Lean.Prod(Nat, Nat), (+ll_x21 => +ll_x22 => Reported(ll_x21, ll_x22)), (+ll_x23 => GlyphReport(ll_x23)))

def ReportEvidence.report_correct():
  ll_a24 => report_correct(ll_a24)

def ReportModel(+__input: Models_Glyphs.Glyph) -> L.Lean.Prod(Nat, Nat):
  GlyphReport(__input)

def PairLit(+glyphs: L.Lean.Prod(Models_Glyphs.Glyph, Models_Glyphs.Glyph), +counts: L.Lean.Prod(Nat, Nat)) -> Data:
  L.Lean.Prod(Lit(S.Sem.fst(Models_Glyphs.Glyph, Models_Glyphs.Glyph, glyphs), S.Sem.fst(Nat, Nat, counts)), Lit(S.Sem.snd(Models_Glyphs.Glyph, Models_Glyphs.Glyph, glyphs), S.Sem.snd(Nat, Nat, counts)))

def GlyphPair(+glyphs: L.Lean.Prod(Models_Glyphs.Glyph, Models_Glyphs.Glyph)) -> L.Lean.Prod(Nat, Nat):
  (SegmentModel(S.Sem.fst(Models_Glyphs.Glyph, Models_Glyphs.Glyph, glyphs)), SegmentModel(S.Sem.snd(Models_Glyphs.Glyph, Models_Glyphs.Glyph, glyphs)))

law pair_correct:
  for +glyphs: L.Lean.Prod(Models_Glyphs.Glyph, Models_Glyphs.Glyph)
  PairLit(glyphs, GlyphPair(glyphs))

def pair_correct(glyphs):
  ((
    segments_lit(S.Sem.fst(Models_Glyphs.Glyph, Models_Glyphs.Glyph, glyphs))
  ), (
    segments_lit(S.Sem.snd(Models_Glyphs.Glyph, Models_Glyphs.Glyph, glyphs))
  ))

law PairEvidence.pair_correct:
  R.LexLeanModels.SatisfiesTotal(L.Lean.Prod(Models_Glyphs.Glyph, Models_Glyphs.Glyph), L.Lean.Prod(Nat, Nat), (+ll_x25 => +ll_x26 => PairLit(ll_x25, ll_x26)), (+ll_x27 => GlyphPair(ll_x27)))

def PairEvidence.pair_correct():
  ll_a28 => pair_correct(ll_a28)

def PairModel(+__input: L.Lean.Prod(Models_Glyphs.Glyph, Models_Glyphs.Glyph)) -> L.Lean.Prod(Nat, Nat):
  GlyphPair(__input)

def Bounded9(+glyph: Models_Glyphs.Glyph, +value: Nat) -> Data:
  S.Sem.le(value, 9n)

def GlyphRoute(+glyph: Models_Glyphs.Glyph) -> Nat:
  S.Sem.ite(Nat, Models_Glyphs.isEight(glyph), SegmentModel(glyph), Models_Recognizer.DigitModel(glyph))

law route_bounded:
  for +glyph: Models_Glyphs.Glyph
  Bounded9(glyph, GlyphRoute(glyph))

def route_bounded(glyph):
  match glyph:
    case Models_Glyphs.Glyph.g0{}:
      {==}
    case Models_Glyphs.Glyph.g1{}:
      {==}
    case Models_Glyphs.Glyph.g2{}:
      {==}
    case Models_Glyphs.Glyph.g3{}:
      {==}
    case Models_Glyphs.Glyph.g4{}:
      {==}
    case Models_Glyphs.Glyph.g5{}:
      {==}
    case Models_Glyphs.Glyph.g6{}:
      {==}
    case Models_Glyphs.Glyph.g7{}:
      {==}
    case Models_Glyphs.Glyph.g8{}:
      {==}
    case Models_Glyphs.Glyph.g9{}:
      {==}

law RouteEvidence.route_bounded:
  R.LexLeanModels.SatisfiesTotal(Models_Glyphs.Glyph, Nat, (+ll_x29 => +ll_x30 => Bounded9(ll_x29, ll_x30)), (+ll_x31 => GlyphRoute(ll_x31)))

def RouteEvidence.route_bounded():
  ll_a32 => route_bounded(ll_a32)

def RouteModel(+__input: Models_Glyphs.Glyph) -> Nat:
  GlyphRoute(__input)

def ShortStream(+costs: List<&2, Nat>) -> Data:
  S.Sem.le(R.LexLeanRuntime.length.List(Nat, costs), 1000n)

def shortStreamCheck(+costs: List<&2, Nat>) -> Bool:
  L.Lean.Nat.blt(R.LexLeanRuntime.length.List(Nat, costs), 1001n)

law short_stream_check_sound:
  for +costs: List<&2, Nat>
  for +ll_h0: {shortStreamCheck(costs) == True{} : Bool}
  ShortStream(costs)

def short_stream_check_sound(costs, ll_h0):
  LA.sound(Con{R.LexLeanRuntime.length.List(Nat, costs), Nil{}}, LA.FLe{LA.TVar{0n}, LA.TLit{1000n}}, Con{LA.FIs{LA.BLt{LA.TVar{0n}, LA.TLit{1001n}}, True{}}, Nil{}}, 7n, LA.Leaf{Con{1n, Con{1n, Nil{}}}}, {==}, (ll_h0, Unit{}))

law StreamContract.precondition_sound:
  R.LexLeanModels.Sound1(List<&2, Nat>, (+ll_x33 => shortStreamCheck(ll_x33)), (+ll_x34 => ShortStream(ll_x34)))

def StreamContract.precondition_sound():
  ll_a35 => ll_a36 => short_stream_check_sound(ll_a35, ll_a36)

def ll_match37(+ll_v38: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, List<&2, Nat>)>, +__acc: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, List<&2, Nat>)>, +__item: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, List<&2, Nat>)>:
  match ll_v38:
    case Fail{__violation}:
      __acc
    case Done{__state}:
      S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, List<&2, Nat>)>, Models_Session.boundedCheck(S.Sem.fst(Models_Session.ll.Window, List<&2, Nat>, __state)), S.Sem.ite(Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, List<&2, Nat>)>, Models_Session.affordableCheck(S.Sem.fst(Models_Session.ll.Window, List<&2, Nat>, __state), __item), (
        +__step = Models_Session.SessionModel(S.Sem.fst(Models_Session.ll.Window, List<&2, Nat>, __state), __item)
        Done{(S.Sem.fst(Models_Session.ll.Window, Nat, __step), R.LexLeanRuntime.append.List(Nat, S.Sem.snd(Models_Session.ll.Window, List<&2, Nat>, __state), Con{S.Sem.snd(Models_Session.ll.Window, Nat, __step), Nil{}}))}
      ), Fail{S.Sem.ContractViolation.precondition{}}), Fail{S.Sem.ContractViolation.input_invariant{}})

def ll_code39(+ll_e: Unit, +__acc: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, List<&2, Nat>)>, +__item: Nat) -> Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, List<&2, Nat>)>:
  ll_match37(__acc, __acc, __item)

def ll_match40(+ll_v41: Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, List<&2, Nat>)>) -> Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>:
  match ll_v41:
    case Fail{__violation}:
      Fail{__violation}
    case Done{__state}:
      Done{S.Sem.snd(Models_Session.ll.Window, List<&2, Nat>, __state)}

def SessionStream(+costs: List<&2, Nat>) -> Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>:
  +__scanned = S.Sem.listFold(~Nat, ~Result<&2, &2, S.Sem.ContractViolation, L.Lean.Prod(Models_Session.ll.Window, List<&2, Nat>)>, ~Unit, ~ll_code39, Unit{}, costs, Done{(Models_Session.SessionModel.initial(), Nil{})})
  ll_match40(__scanned)

def StreamModel(+__input: List<&2, Nat>) -> Result<&2, &2, S.Sem.ContractViolation, List<&2, Nat>>:
  SessionStream(__input)
