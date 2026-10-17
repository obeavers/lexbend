import Base
import ../LexLeanPrelude.bend as L
import ../LexLeanSemantic.bend as S
import ../LexLeanRuntime.bend as R
import ./Triage.bend as Models_Triage

def isUrgent(+level: Models_Triage.Level) -> Bool:
  match level:
    case Models_Triage.Level.routine{}:
      False{}
    case Models_Triage.Level.urgent{}:
      True{}
    case Models_Triage.Level.emergency{}:
      False{}

def Actionable(+level: Models_Triage.Level) -> Data:
  {Models_Triage.isRoutine(level) == False{} : Bool}

def actionableCheck(+level: Models_Triage.Level) -> Bool:
  L.Lean.Bool.not(Models_Triage.isRoutine(level))

law actionable_check_sound:
  for +level: Models_Triage.Level
  for +ll_h0: {actionableCheck(level) == True{} : Bool}
  Actionable(level)

def actionable_check_sound(level, ll_h0):
  match level:
    case Models_Triage.Level.routine{}:
      S.Sem.false_ne_true(Actionable(Models_Triage.Level.routine{}), ll_h0)
    case Models_Triage.Level.urgent{}:
      {==}
    case Models_Triage.Level.emergency{}:
      {==}

law actionable_check_complete:
  for +level: Models_Triage.Level
  for +ll_h0: Actionable(level)
  {actionableCheck(level) == True{} : Bool}

def actionable_check_complete(level, ll_h0):
  match level:
    case Models_Triage.Level.routine{}:
      S.Sem.false_ne_true({actionableCheck(Models_Triage.Level.routine{}) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, ll_h0))
    case Models_Triage.Level.urgent{}:
      {==}
    case Models_Triage.Level.emergency{}:
      {==}

def Escalates(+level: Models_Triage.Level, +action: Nat) -> Data:
  S.Sem.le(1n, action)

law PolicyContract.precondition_sound:
  R.LexLeanModels.Sound1(Models_Triage.Level, (+ll_x1 => actionableCheck(ll_x1)), (+ll_x2 => Actionable(ll_x2)))

def PolicyContract.precondition_sound():
  ll_a3 => ll_a4 => actionable_check_sound(ll_a3, ll_a4)

law PolicyContract.precondition_complete:
  R.LexLeanModels.Complete1(Models_Triage.Level, (+ll_x5 => actionableCheck(ll_x5)), (+ll_x6 => Actionable(ll_x6)))

def PolicyContract.precondition_complete():
  ll_a7 => ll_a8 => actionable_check_complete(ll_a7, ll_a8)

def PolicyRules.selected(+level: Models_Triage.Level) -> Nat:
  S.Sem.ite(Nat, Models_Triage.isEmergency(level), 0n, S.Sem.ite(Nat, isUrgent(level), 1n, 2n))

def PolicyRules(+level: Models_Triage.Level) -> Nat:
  S.Sem.ite(Nat, Models_Triage.isEmergency(level), 2n, S.Sem.ite(Nat, isUrgent(level), 1n, 0n))

law policy_escalates:
  for +level: Models_Triage.Level
  for +ll_h0: Actionable(level)
  Escalates(level, PolicyRules(level))

def policy_escalates(level, ll_h0):
  match level:
    case Models_Triage.Level.routine{}:
      S.Sem.false_ne_true(Escalates(Models_Triage.Level.routine{}, PolicyRules(Models_Triage.Level.routine{})), Equal.sym(Bool, True{}, False{}, ll_h0))
    case Models_Triage.Level.urgent{}:
      {==}
    case Models_Triage.Level.emergency{}:
      {==}

law emergency_dispatches:
  {PolicyRules.selected(Models_Triage.Level.emergency{}) == 0n : Nat}

def emergency_dispatches():
  {==}

law PolicyEvidence.policy_escalates:
  R.LexLeanModels.Satisfies(Models_Triage.Level, Nat, (+ll_x9 => Actionable(ll_x9)), (+ll_x10 => +ll_x11 => Escalates(ll_x10, ll_x11)), (+ll_x12 => PolicyRules(ll_x12)))

def PolicyEvidence.policy_escalates():
  ll_a13 => ll_a14 => policy_escalates(ll_a13, ll_a14)

def PolicyModel(+__input: Models_Triage.Level) -> Nat:
  PolicyRules(__input)
