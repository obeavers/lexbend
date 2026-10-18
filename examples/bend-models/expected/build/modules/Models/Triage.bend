import Base
import ../LexLeanPrelude.bend as L
import ../LexLeanSemantic.bend as S
import ../LexLeanRuntime.bend as R

type Presentation is Data:
  Presentation.p0{}
  Presentation.p1{}
  Presentation.p2{}
  Presentation.p3{}
  Presentation.p4{}
  Presentation.p5{}
  Presentation.p6{}
  Presentation.p7{}

type Level is Data:
  Level.routine{}
  Level.urgent{}
  Level.emergency{}

def features(+presentation: Presentation) -> List<&2, L.Lean.Int>:
  match presentation:
    case Presentation.p0{}:
      Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}
    case Presentation.p1{}:
      Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}
    case Presentation.p2{}:
      Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Nil{}}}}
    case Presentation.p3{}:
      Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Nil{}}}}
    case Presentation.p4{}:
      Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{1n}, Nil{}}}}
    case Presentation.p5{}:
      Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{1n}, Nil{}}}}
    case Presentation.p6{}:
      Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Nil{}}}}
    case Presentation.p7{}:
      Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Nil{}}}}

def hasSymptom(+presentation: Presentation) -> Bool:
  match presentation:
    case Presentation.p0{}:
      False{}
    case Presentation.p1{}:
      True{}
    case Presentation.p2{}:
      True{}
    case Presentation.p3{}:
      True{}
    case Presentation.p4{}:
      True{}
    case Presentation.p5{}:
      True{}
    case Presentation.p6{}:
      True{}
    case Presentation.p7{}:
      True{}

def isBreathless(+presentation: Presentation) -> Bool:
  match presentation:
    case Presentation.p0{}:
      False{}
    case Presentation.p1{}:
      False{}
    case Presentation.p2{}:
      False{}
    case Presentation.p3{}:
      False{}
    case Presentation.p4{}:
      True{}
    case Presentation.p5{}:
      True{}
    case Presentation.p6{}:
      True{}
    case Presentation.p7{}:
      True{}

def isEmergency(+level: Level) -> Bool:
  match level:
    case Level.routine{}:
      False{}
    case Level.urgent{}:
      False{}
    case Level.emergency{}:
      True{}

def isRoutine(+level: Level) -> Bool:
  match level:
    case Level.routine{}:
      True{}
    case Level.urgent{}:
      False{}
    case Level.emergency{}:
      False{}

def Symptomatic(+presentation: Presentation) -> Data:
  {hasSymptom(presentation) == True{} : Bool}

def symptomaticCheck(+presentation: Presentation) -> Bool:
  hasSymptom(presentation)

law symptomatic_check_sound:
  for +presentation: Presentation
  for +ll_h0: {symptomaticCheck(presentation) == True{} : Bool}
  Symptomatic(presentation)

def symptomatic_check_sound(presentation, ll_h0):
  match presentation:
    case Presentation.p0{}:
      S.Sem.false_ne_true(Symptomatic(Presentation.p0{}), ll_h0)
    case Presentation.p1{}:
      {==}
    case Presentation.p2{}:
      {==}
    case Presentation.p3{}:
      {==}
    case Presentation.p4{}:
      {==}
    case Presentation.p5{}:
      {==}
    case Presentation.p6{}:
      {==}
    case Presentation.p7{}:
      {==}

def Safe(+presentation: Presentation, +level: Level) -> Type:
  {isBreathless(presentation) == True{} : Bool} -> {isEmergency(level) == True{} : Bool}

def triageWeights.bytes() -> R.Lean.ByteArray:
  R.Lean.ByteArray.mk{Con{R.Lean.UInt8.lit(254), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(254), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(252), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(1), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(5), Con{R.Lean.UInt8.lit(0), Nil{}}}}}}}}}}}}}}}}}}}}

def triageWeights() -> List<&2, List<&2, L.Lean.Int>>:
  Con{Con{L.negSucc{1n}, Con{L.negSucc{1n}, Con{L.negSucc{3n}, Nil{}}}}, Con{Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Nil{}}}}, Con{Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.ofNat{5n}, Nil{}}}}, Nil{}}}}

law triageWeights.decoded:
  {L.Lean.Bool.and(R.LexLeanModels.tensorMatches(2n, True{}, S.Sem.flatten(L.Lean.Int, triageWeights()), triageWeights.bytes()), L.Lean.Bool.and(L.Lean.Nat.beq(L.Lean.List.length(List<&2, L.Lean.Int>, triageWeights()), 3n), L.Lean.Bool.and(L.Lean.Nat.beq(L.Lean.List.length(List<&2, L.Lean.Int>, triageWeights()), 3n), S.Sem.lengthsAre(L.Lean.Int, triageWeights(), 3n)))) == True{} : Bool}

def triageWeights.decoded():
  {==}

def triageBias.bytes() -> R.Lean.ByteArray:
  R.Lean.ByteArray.mk{Con{R.Lean.UInt8.lit(1), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Nil{}}}}}}}}

def triageBias() -> List<&2, L.Lean.Int>:
  Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.negSucc{0n}, Nil{}}}}

law triageBias.decoded:
  {L.Lean.Bool.and(R.LexLeanModels.tensorMatches(2n, True{}, triageBias(), triageBias.bytes()), L.Lean.Nat.beq(L.Lean.List.length(L.Lean.Int, triageBias()), 3n)) == True{} : Bool}

def triageBias.decoded():
  {==}

law TriageContract.precondition_sound:
  R.LexLeanModels.Sound1(Presentation, (+ll_x1 => symptomaticCheck(ll_x1)), (+ll_x2 => Symptomatic(ll_x2)))

def TriageContract.precondition_sound():
  ll_a3 => ll_a4 => symptomatic_check_sound(ll_a3, ll_a4)

law triage_width:
  for +presentation: Presentation
  {R.LexLeanRuntime.length.List(L.Lean.Int, features(presentation)) == 3n : Nat}

def triage_width(presentation):
  match presentation:
    case Presentation.p0{}:
      {==}
    case Presentation.p1{}:
      {==}
    case Presentation.p2{}:
      {==}
    case Presentation.p3{}:
      {==}
    case Presentation.p4{}:
      {==}
    case Presentation.p5{}:
      {==}
    case Presentation.p6{}:
      {==}
    case Presentation.p7{}:
      {==}

def TriageScore.features(+presentation: Presentation) -> List<&2, L.Lean.Int>:
  features(presentation)

def ll_match7(+ll_v8: List<&2, L.Lean.Int>, +__sum: L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>), +__weight: L.Lean.Int) -> L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>):
  match ll_v8:
    case Nil{}:
      __sum
    case Con{__value, __rest}:
      (L.Lean.Int.sub(S.Sem.fst(L.Lean.Int, List<&2, L.Lean.Int>, __sum), L.Lean.Int.neg(L.Lean.Int.mul(__weight, __value))), __rest)

def ll_code9(+ll_e: Unit, +__sum: L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>), +__weight: L.Lean.Int) -> L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>):
  ll_match7(S.Sem.snd(L.Lean.Int, List<&2, L.Lean.Int>, __sum), __sum, __weight)

def ll_match5(+ll_v6: List<&2, L.Lean.Int>, +__acc: L.Lean.Prod(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>), +__row: List<&2, L.Lean.Int>, +__values: List<&2, L.Lean.Int>) -> L.Lean.Prod(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>):
  match ll_v6:
    case Nil{}:
      __acc
    case Con{__bias, __biases}:
      (R.LexLeanRuntime.append.List(L.Lean.Int, S.Sem.fst(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>, __acc), Con{L.Lean.Int.sub(__bias, L.Lean.Int.neg(S.Sem.fst(L.Lean.Int, List<&2, L.Lean.Int>, S.Sem.listFold(~L.Lean.Int, ~L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>), ~Unit, ~ll_code9, Unit{}, __row, (L.ofNat{0n}, __values))))), Nil{}}), __biases)

def ll_code10(+ll_e: List<&2, L.Lean.Int>, +__acc: L.Lean.Prod(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>), +__row: List<&2, L.Lean.Int>) -> L.Lean.Prod(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>):
  +__values = ll_e
  ll_match5(S.Sem.snd(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>, __acc), __acc, __row, __values)

def TriageScore.scores(+presentation: Presentation) -> List<&2, L.Lean.Int>:
  +__values = TriageScore.features(presentation)
  S.Sem.fst(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>, S.Sem.listFold(~List<&2, L.Lean.Int>, ~L.Lean.Prod(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>), ~List<&2, L.Lean.Int>, ~ll_code10, __values, triageWeights(), (Nil{}, triageBias())))

def ll_match11(+ll_v12: Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>) -> Level:
  match ll_v12:
    case None{}:
      Level.routine{}
    case Some{__winner}:
      S.Sem.fst(Level, L.Lean.Int, __winner)

def ll_match15(+ll_v16: Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>, +__label: Level, +__score: L.Lean.Int) -> Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>:
  match ll_v16:
    case None{}:
      Some{(__label, __score)}
    case Some{__leader}:
      S.Sem.ite(Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>, R.LexLeanCollections.lessThan.Int(S.Sem.snd(Level, L.Lean.Int, __leader), __score), Some{(__label, __score)}, Some{__leader})

def ll_match13(+ll_v14: List<&2, Level>, +__best: L.Lean.Prod(Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>, List<&2, Level>), +__score: L.Lean.Int) -> L.Lean.Prod(Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>, List<&2, Level>):
  match ll_v14:
    case Nil{}:
      __best
    case Con{__label, __labels}:
      (ll_match15(S.Sem.fst(Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>, List<&2, Level>, __best), __label, __score), __labels)

def ll_code17(+ll_e: Unit, +__best: L.Lean.Prod(Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>, List<&2, Level>), +__score: L.Lean.Int) -> L.Lean.Prod(Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>, List<&2, Level>):
  ll_match13(S.Sem.snd(Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>, List<&2, Level>, __best), __best, __score)

def TriageScore(+presentation: Presentation) -> Level:
  ll_match11(S.Sem.fst(Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>, List<&2, Level>, S.Sem.listFold(~L.Lean.Int, ~L.Lean.Prod(Maybe<&2, L.Lean.Prod(Level, L.Lean.Int)>, List<&2, Level>), ~Unit, ~ll_code17, Unit{}, TriageScore.scores(presentation), (None{}, Con{Level.routine{}, Con{Level.urgent{}, Con{Level.emergency{}, Nil{}}}}))))

law triage_safe:
  for +presentation: Presentation
  for +ll_h0: Symptomatic(presentation)
  Safe(presentation, TriageScore(presentation))

def triage_safe(presentation, ll_h0):
  match presentation:
    case Presentation.p0{}:
      S.Sem.false_ne_true(Safe(Presentation.p0{}, TriageScore(Presentation.p0{})), ll_h0)
    case Presentation.p1{}:
      ll_h18 => S.Sem.false_ne_true({isEmergency(TriageScore(Presentation.p1{})) == True{} : Bool}, ll_h18)
    case Presentation.p2{}:
      ll_h19 => S.Sem.false_ne_true({isEmergency(TriageScore(Presentation.p2{})) == True{} : Bool}, ll_h19)
    case Presentation.p3{}:
      ll_h20 => S.Sem.false_ne_true({isEmergency(TriageScore(Presentation.p3{})) == True{} : Bool}, ll_h20)
    case Presentation.p4{}:
      ll_h21 => {==}
    case Presentation.p5{}:
      ll_h22 => {==}
    case Presentation.p6{}:
      ll_h23 => {==}
    case Presentation.p7{}:
      ll_h24 => {==}

law TriageEvidence.triage_safe:
  R.LexLeanModels.Satisfies(Presentation, Level, (+ll_x25 => Symptomatic(ll_x25)), (+ll_x26 => +ll_x27 => Safe(ll_x26, ll_x27)), (+ll_x28 => TriageScore(ll_x28)))

def TriageEvidence.triage_safe():
  ll_a29 => ll_a30 => triage_safe(ll_a29, ll_a30)

def TriageModel(+__input: Presentation) -> Level:
  TriageScore(__input)
