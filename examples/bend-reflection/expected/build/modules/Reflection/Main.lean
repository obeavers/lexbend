module
public import Init
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
set_option linter.constructorNameAsVariable false
namespace Reflection.Main

public structure Pair where
  left : Nat
  right : Nat

@[expose] public def validatePair (pair : Pair) : Bool := ((Nat.beq ((pair).left) (0)) && (Nat.beq ((pair).right) (1)))

@[expose, reducible] public def PairValid (pair : Pair) : Prop := (((pair).left = 0) /\ ((pair).right = 1))

public theorem pair_reflects (pair : Pair) : ((validatePair (pair) = true) <-> PairValid (pair)) := by
  have llAndBridge : ∀ left right : Bool, ((left && right) = true) ↔ left = true ∧ right = true := by
    intro left right
    cases left <;> cases right <;> decide
  have llBeqRefl : ∀ value : Nat, Nat.beq value value = true := by
    intro value
    induction value with
    | zero => rfl
    | succ value ih => exact ih
  have llBeqBridge : ∀ left right : Nat, Nat.beq left right = true ↔ left = right := by
    intro left right
    constructor
    · exact Nat.eq_of_beq_eq_true
    · intro h
      cases h
      exact llBeqRefl left
  change (((Nat.beq ((pair).left) (0) && Nat.beq ((pair).right) (1))) = true) ↔ (((pair).left = 0) /\ ((pair).right = 1))
  exact Iff.trans (llAndBridge _ _) (and_congr (llBeqBridge _ _) (llBeqBridge _ _))

@[expose] public def countsFrom : (start : Nat) -> (values : List (Nat)) -> Bool
  | _start, List.nil => true
  | start, List.cons head tail => ((Nat.beq (start) (head)) && countsFrom ((start + 1)) (tail))

@[expose] public def CountsFrom : (start : Nat) -> (values : List (Nat)) -> Prop
  | _start, List.nil => (0 = 0)
  | start, List.cons head tail => ((start = head) /\ CountsFrom ((start + 1)) (tail))

public theorem counts_reflects (start : Nat) (values : List (Nat)) : ((countsFrom (start) (values) = true) <-> CountsFrom (start) (values)) := by
  have llAndBridge : ∀ left right : Bool, ((left && right) = true) ↔ left = true ∧ right = true := by
    intro left right
    cases left <;> cases right <;> decide
  have llBeqRefl : ∀ value : Nat, Nat.beq value value = true := by
    intro value
    induction value with
    | zero => rfl
    | succ value ih => exact ih
  induction values generalizing start with
  | nil => constructor <;> intro _ <;> rfl
  | cons llValue llRest llIH =>
    constructor
    · intro h
      have hpair := (llAndBridge _ _).mp h
      exact And.intro (Nat.eq_of_beq_eq_true hpair.left) ((llIH (start + 1)).mp hpair.right)
    · intro h
      have hleft : Nat.beq start llValue = true := h.left ▸ llBeqRefl start
      have hright : countsFrom (start + 1) llRest = true := (llIH (start + 1)).mpr h.right
      exact (llAndBridge _ _).mpr (And.intro hleft hright)

@[expose] public def allBelow : (bound : Nat) -> (values : List (Nat)) -> Bool
  | _bound, List.nil => true
  | bound, List.cons head tail => ((Nat.blt (head) (bound)) && allBelow (bound) (tail))

@[expose] public def AllBelow : (bound : Nat) -> (values : List (Nat)) -> Prop
  | _bound, List.nil => (0 = 0)
  | bound, List.cons head tail => ((head < bound) /\ AllBelow (bound) (tail))

public theorem below_reflects (bound : Nat) (values : List (Nat)) : ((allBelow (bound) (values) = true) <-> AllBelow (bound) (values)) := by
  have llAndBridge : ∀ left right : Bool, ((left && right) = true) ↔ left = true ∧ right = true := by
    intro left right
    cases left <;> cases right <;> decide
  induction values generalizing bound with
  | nil => constructor <;> intro _ <;> rfl
  | cons llValue llRest llIH =>
    constructor
    · intro h
      have hpair := (llAndBridge _ _).mp h
      exact And.intro (Nat.le_of_ble_eq_true hpair.left) ((llIH bound).mp hpair.right)
    · intro h
      have hleft : Nat.blt llValue bound = true := Nat.ble_eq_true_of_le h.left
      have hright : allBelow bound llRest = true := (llIH bound).mpr h.right
      exact (llAndBridge _ _).mpr (And.intro hleft hright)

public theorem congruence_refl (value : Nat) : ((value + 0) = (value + 0)) := by
  congr 1

public theorem congruence_unfolds (a : Nat) : (((a + 0) + 3) = (a + 3)) := by
  congr 1

end Reflection.Main
