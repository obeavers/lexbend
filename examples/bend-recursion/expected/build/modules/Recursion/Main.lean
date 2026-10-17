module
public import Init
public import LexLeanRuntime.Portable
public import Recursion.Syntax
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
set_option linter.constructorNameAsVariable false
namespace Recursion.Main

mutual
@[expose] public def roseSize (Item : Type) : (rose : Recursion.Syntax.Rose (Item)) -> Nat
  | Recursion.Syntax.Rose.node _ children => (1 + forestSize (Item) (children))
termination_by structural rose => rose

@[expose] public def forestSize (Item : Type) : (forest : List (Recursion.Syntax.Rose (Item))) -> Nat
  | List.nil => 0
  | List.cons head tail => (roseSize (Item) (head) + forestSize (Item) (tail))
termination_by structural forest => forest
end

mutual
@[expose] public def isEven : (number : Nat) -> Bool
  | Nat.zero => true
  | Nat.succ previous => isOdd (previous)
termination_by structural number => number

@[expose] public def isOdd : (number : Nat) -> Bool
  | Nat.zero => false
  | Nat.succ previous => isEven (previous)
termination_by structural number => number
end

public theorem countdown_decreases (number : Nat) (_steps : Nat) : (((Nat.blt (number) (2)) = false) -> ((LexLeanRuntime.subtract (number) (2) : Nat) < number)) := by
  intros
  try set_option linter.unusedSimpArgs false in simp only [← Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_true, true_and, Option.some.injEq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, LexLeanRuntime.subtract, LexLeanRuntime.multiply] at *
  all_goals omega

@[expose, semireducible] public def countdown (number : Nat) (steps : Nat) : Nat := (match (generalizing := false) __decrease0 : (Nat.blt (number) (2)) with | true => steps | false => countdown ((LexLeanRuntime.subtract (number) (2) : Nat)) ((steps + 1)))
termination_by number
decreasing_by all_goals first | (have __evidence := countdown_decreases (number) (steps) (__decrease0); subst_vars; exact __evidence)

public theorem reduce_decreases (value : Nat) (bound : Nat) : (((Nat.beq (bound) (0)) = false) -> (((Nat.blt (value) (bound)) = false) -> ((LexLeanRuntime.subtract (value) (bound) : Nat) < value))) := by
  intros
  try set_option linter.unusedSimpArgs false in simp only [← Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_true, true_and, Option.some.injEq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, LexLeanRuntime.subtract, LexLeanRuntime.multiply] at *
  all_goals omega

@[expose, semireducible] public def reduce (value : Nat) (bound : Nat) : Nat := (match (generalizing := false) __decrease0 : (Nat.beq (bound) (0)) with | true => value | false => (match (generalizing := false) __decrease1 : (Nat.blt (value) (bound)) with | true => value | false => reduce ((LexLeanRuntime.subtract (value) (bound) : Nat)) (bound)))
termination_by value
decreasing_by all_goals first | (have __evidence := reduce_decreases (value) (bound) (__decrease0) (__decrease1); subst_vars; exact __evidence)

public theorem search_decreases (target : Nat) (low : Nat) (high : Nat) : (((Nat.blt (low) (high)) = true) -> (((Nat.ble (target) ((low + low))) = false) -> ((LexLeanRuntime.subtract (high) ((low + 1)) : Nat) < (LexLeanRuntime.subtract (high) (low) : Nat)))) := by
  intros
  try set_option linter.unusedSimpArgs false in simp only [← Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_true, true_and, Option.some.injEq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, LexLeanRuntime.subtract, LexLeanRuntime.multiply] at *
  all_goals omega

@[expose, semireducible] public def search (target : Nat) (low : Nat) (high : Nat) : Nat := (match (generalizing := false) __decrease0 : (Nat.blt (low) (high)) with | true => (match (generalizing := false) __decrease1 : (Nat.ble (target) ((low + low))) with | true => low | false => search (target) ((low + 1)) (high)) | false => high)
termination_by (LexLeanRuntime.subtract (high) (low) : Nat)
decreasing_by all_goals first | (have __evidence := search_decreases (target) (low) (high) (__decrease0) (__decrease1); subst_vars; exact __evidence)

public theorem rose_size : (roseSize (Nat) (Recursion.Syntax.Rose.node (1) ((Recursion.Syntax.Rose.node (2) (([] : List (Recursion.Syntax.Rose (Nat)))) :: (Recursion.Syntax.Rose.node (3) (([] : List (Recursion.Syntax.Rose (Nat)))) :: ([] : List (Recursion.Syntax.Rose (Nat))))))) = 3) := by
  rfl

public theorem ten_is_even : (isEven (10) = true) := by
  decide

public theorem countdown_nine : (countdown (9) (0) = 4) := by
  decide

public theorem reduce_twenty_three : (reduce (23) (5) = 3) := by
  decide

public theorem search_first : (search (7) (0) (10) = 4) := by
  decide

@[expose] public def weight : (term : Recursion.Syntax.Term) -> Nat
  | Recursion.Syntax.Term.literal _ => 1
  | Recursion.Syntax.Term.plus left right => (((weight (left) + weight (left)) + weight (right)) + 1)

public theorem reassociate_literal (term : Recursion.Syntax.Term) (left : Recursion.Syntax.Term) (right : Recursion.Syntax.Term) (value : Nat) : ((term = Recursion.Syntax.Term.plus (left) (right)) -> ((left = Recursion.Syntax.Term.literal (value)) -> (weight (right) < weight (term)))) := by
  intros
  subst_vars
  try set_option linter.unusedSimpArgs false in simp only [weight, ← Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_true, true_and, Option.some.injEq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, LexLeanRuntime.subtract, LexLeanRuntime.multiply] at *
  all_goals omega

public theorem reassociate_plus (term : Recursion.Syntax.Term) (left : Recursion.Syntax.Term) (right : Recursion.Syntax.Term) (inner : Recursion.Syntax.Term) (rest : Recursion.Syntax.Term) : ((term = Recursion.Syntax.Term.plus (left) (right)) -> ((left = Recursion.Syntax.Term.plus (inner) (rest)) -> (weight (Recursion.Syntax.Term.plus (inner) (Recursion.Syntax.Term.plus (rest) (right))) < weight (term)))) := by
  intros
  subst_vars
  try set_option linter.unusedSimpArgs false in simp only [weight, ← Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_true, true_and, Option.some.injEq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, LexLeanRuntime.subtract, LexLeanRuntime.multiply] at *
  all_goals omega

@[expose, semireducible] public def reassociate (term : Recursion.Syntax.Term) : Recursion.Syntax.Term := (match (generalizing := false) __decrease0 : term with | Recursion.Syntax.Term.literal value => Recursion.Syntax.Term.literal (value) | Recursion.Syntax.Term.plus left right => (match (generalizing := false) __decrease1 : left with | Recursion.Syntax.Term.literal value => Recursion.Syntax.Term.plus (Recursion.Syntax.Term.literal (value)) (reassociate (right)) | Recursion.Syntax.Term.plus inner rest => reassociate (Recursion.Syntax.Term.plus (inner) (Recursion.Syntax.Term.plus (rest) (right)))))
termination_by weight (term)
decreasing_by all_goals first | (have __evidence := reassociate_literal (term) _ _ _ (__decrease0) (__decrease1); subst_vars; exact __evidence) | (have __evidence := reassociate_plus (term) _ _ _ _ (__decrease0) (__decrease1); subst_vars; exact __evidence)

public theorem reassociate_weight : (weight (reassociate (Recursion.Syntax.Term.plus (Recursion.Syntax.Term.plus (Recursion.Syntax.Term.literal (1)) (Recursion.Syntax.Term.literal (2))) (Recursion.Syntax.Term.literal (3)))) = 7) := by
  decide

public theorem prune_plus (term : Recursion.Syntax.Term) (left : Recursion.Syntax.Term) (right : Recursion.Syntax.Term) (inner : Recursion.Syntax.Term) (rest : Recursion.Syntax.Term) : ((term = Recursion.Syntax.Term.plus (left) (right)) -> ((left = Recursion.Syntax.Term.plus (inner) (rest)) -> (weight (Recursion.Syntax.Term.plus (inner) (right)) < weight (term)))) := by
  intros
  subst_vars
  try set_option linter.unusedSimpArgs false in simp only [weight, ← Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_true, true_and, Option.some.injEq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, LexLeanRuntime.subtract, LexLeanRuntime.multiply] at *
  all_goals omega

@[expose, semireducible] public def prune (term : Recursion.Syntax.Term) : Recursion.Syntax.Term := (match (generalizing := false) __decrease0 : term with | Recursion.Syntax.Term.literal value => Recursion.Syntax.Term.literal (value) | Recursion.Syntax.Term.plus left right => (match (generalizing := false) __decrease1 : left with | Recursion.Syntax.Term.literal _ => prune (right) | Recursion.Syntax.Term.plus inner _ => prune (Recursion.Syntax.Term.plus (inner) (right))))
termination_by weight (term)
decreasing_by all_goals first | (have __evidence := reassociate_literal (term) _ _ _ (__decrease0) (__decrease1); subst_vars; exact __evidence) | (have __evidence := prune_plus (term) _ _ _ _ (__decrease0) (__decrease1); subst_vars; exact __evidence)

public theorem prune_result : (weight (prune (Recursion.Syntax.Term.plus (Recursion.Syntax.Term.plus (Recursion.Syntax.Term.literal (1)) (Recursion.Syntax.Term.literal (2))) (Recursion.Syntax.Term.literal (3)))) = 1) := by
  decide

public theorem ping_to_pong (number : Nat) : (((Nat.beq (number) (0)) = false) -> ((number + number) < ((number + number) + 1))) := by
  intros
  try set_option linter.unusedSimpArgs false in simp only [← Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_true, true_and, Option.some.injEq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, LexLeanRuntime.subtract, LexLeanRuntime.multiply] at *
  all_goals omega

public theorem pong_to_ping (number : Nat) : (((Nat.beq (number) (0)) = false) -> ((((LexLeanRuntime.subtract (number) (1) : Nat) + (LexLeanRuntime.subtract (number) (1) : Nat)) + 1) < (number + number))) := by
  intros
  try set_option linter.unusedSimpArgs false in simp only [← Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_true, true_and, Option.some.injEq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, LexLeanRuntime.subtract, LexLeanRuntime.multiply] at *
  all_goals omega

end Recursion.Main
