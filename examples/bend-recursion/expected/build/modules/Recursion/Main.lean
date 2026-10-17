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
@[expose] public def exprSize : (expression : Recursion.Syntax.Expr) -> Nat
  | Recursion.Syntax.Expr.literal _ => 1
  | Recursion.Syntax.Expr.plus left right => ((exprSize (left) + exprSize (right)) + 1)
  | Recursion.Syntax.Expr.block statements result => (statementsSize (statements) + exprSize (result))
termination_by structural expression => expression

@[expose] public def statementsSize : (statements : List (Recursion.Syntax.Stmt)) -> Nat
  | List.nil => 0
  | List.cons head tail => (statementSize (head) + statementsSize (tail))
termination_by structural statements => statements

@[expose] public def statementSize : (statement : Recursion.Syntax.Stmt) -> Nat
  | Recursion.Syntax.Stmt.assign _ value => (exprSize (value) + 1)
  | Recursion.Syntax.Stmt.sequence first second => (statementSize (first) + statementSize (second))
termination_by structural statement => statement
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

public theorem expression_size : (exprSize (Recursion.Syntax.Expr.block ((Recursion.Syntax.Stmt.assign ("x") (Recursion.Syntax.Expr.literal (1)) :: ([] : List (Recursion.Syntax.Stmt)))) (Recursion.Syntax.Expr.plus (Recursion.Syntax.Expr.literal (2)) (Recursion.Syntax.Expr.literal (3)))) = 5) := by
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

mutual
@[expose] public def foldExpr : (expression : Recursion.Syntax.Expr) -> Recursion.Syntax.Expr
  | Recursion.Syntax.Expr.literal value => Recursion.Syntax.Expr.literal (value)
  | Recursion.Syntax.Expr.plus left right => (let foldedLeft : Recursion.Syntax.Expr := foldExpr (left); (let foldedRight : Recursion.Syntax.Expr := foldExpr (right); (match foldedLeft with | Recursion.Syntax.Expr.literal leftValue => (match foldedRight with | Recursion.Syntax.Expr.literal rightValue => Recursion.Syntax.Expr.literal ((leftValue + rightValue)) | Recursion.Syntax.Expr.plus _ _ => Recursion.Syntax.Expr.plus (foldedLeft) (foldedRight) | Recursion.Syntax.Expr.block _ _ => Recursion.Syntax.Expr.plus (foldedLeft) (foldedRight)) | Recursion.Syntax.Expr.plus _ _ => Recursion.Syntax.Expr.plus (foldedLeft) (foldedRight) | Recursion.Syntax.Expr.block _ _ => Recursion.Syntax.Expr.plus (foldedLeft) (foldedRight))))
  | Recursion.Syntax.Expr.block statements result => Recursion.Syntax.Expr.block (foldStatements (statements)) (foldExpr (result))
termination_by structural expression => expression

@[expose] public def foldStatements : (statements : List (Recursion.Syntax.Stmt)) -> List (Recursion.Syntax.Stmt)
  | List.nil => ([] : List (Recursion.Syntax.Stmt))
  | List.cons head tail => (foldStatement (head) :: foldStatements (tail))
termination_by structural statements => statements

@[expose] public def foldStatement : (statement : Recursion.Syntax.Stmt) -> Recursion.Syntax.Stmt
  | Recursion.Syntax.Stmt.assign target value => Recursion.Syntax.Stmt.assign (target) (foldExpr (value))
  | Recursion.Syntax.Stmt.sequence first second => Recursion.Syntax.Stmt.sequence (foldStatement (first)) (foldStatement (second))
termination_by structural statement => statement
end

public theorem folding_sample : (foldExpr (Recursion.Syntax.Expr.block ((Recursion.Syntax.Stmt.assign ("x") (Recursion.Syntax.Expr.plus (Recursion.Syntax.Expr.literal (1)) (Recursion.Syntax.Expr.literal (2))) :: ([] : List (Recursion.Syntax.Stmt)))) (Recursion.Syntax.Expr.plus (Recursion.Syntax.Expr.literal (2)) (Recursion.Syntax.Expr.plus (Recursion.Syntax.Expr.literal (3)) (Recursion.Syntax.Expr.literal (4))))) = Recursion.Syntax.Expr.block ((Recursion.Syntax.Stmt.assign ("x") (Recursion.Syntax.Expr.literal (3)) :: ([] : List (Recursion.Syntax.Stmt)))) (Recursion.Syntax.Expr.literal (9))) := by
  rfl

mutual
@[expose] public def walk : (fuel : Nat) -> (path : List (Nat)) -> Nat
  | Nat.zero, _path => 0
  | Nat.succ remaining, path => (match path with | List.nil => 0 | List.cons number rest => (match depth (remaining) (number) with | Option.none => walk (remaining) (rest) | Option.some halvings => (halvings + walk (remaining) (rest))))
termination_by structural fuel _ => fuel

@[expose] public def depth : (fuel : Nat) -> (number : Nat) -> Option (Nat)
  | Nat.zero, _number => Option.none
  | Nat.succ remaining, number => (match number with | Nat.zero => Option.some (walk (remaining) (([] : List (Nat)))) | Nat.succ smaller => (match smaller with | Nat.zero => Option.some (0) | Nat.succ lower => (match depth (remaining) (lower) with | Option.none => Option.none | Option.some halvings => Option.some ((halvings + 1)))))
termination_by structural fuel _ => fuel
end

public theorem walk_sample : (walk (10) ((4 :: (7 :: (1 :: ([] : List (Nat)))))) = 5) := by
  rfl

public theorem walk_exhausted : (walk (3) ((9 :: ([] : List (Nat)))) = 0) := by
  rfl

public theorem depth_nine : (depth (6) (9) = Option.some (4)) := by
  rfl

@[expose] public def secondOfTwo (values : List (Nat)) : Nat := (match values with | List.nil => 0 | List.cons head rest => (match rest with | List.nil => 0 | List.cons later more => (match more with | List.nil => (match later with | Nat.zero => head | Nat.succ previous => previous) | List.cons _ _ => 0)))

public theorem second_of_two : (secondOfTwo ((5 :: (3 :: ([] : List (Nat))))) = 2) := by
  rfl

public theorem second_of_two_zero : (secondOfTwo ((5 :: (0 :: ([] : List (Nat))))) = 5) := by
  rfl

@[expose] public def firstEven : (values : List (Nat)) -> Option (Nat)
  | List.nil => Option.none
  | List.cons head rest => (match isEven (head) with | Bool.true => Option.some (head) | Bool.false => firstEven (rest))

public theorem first_even : (firstEven ((3 :: (5 :: (8 :: (2 :: ([] : List (Nat))))))) = Option.some (8)) := by
  rfl

@[expose] public def applyTwice (step : ((Nat) -> (Nat))) (value : Nat) : Nat := (step ((step (value))))

@[expose] public def stepUnlessZero (step : ((Nat) -> (Nat))) (value : Nat) : Nat := (match (Nat.beq (value) (0)) with | Bool.true => 0 | Bool.false => applyTwice (step) (value))

@[expose] public def shiftTwice (low : Nat) (high : Nat) (value : Nat) : Nat := applyTwice ((fun (n : Nat) => ((n + low) + (high + high)))) (value)

public theorem shift_twice : (shiftTwice (1) (2) (3) = 13) := by
  rfl

public theorem step_unless_zero : ((stepUnlessZero ((fun (n : Nat) => (n + 2))) (5) = 9) /\ (stepUnlessZero ((fun (n : Nat) => (n + 2))) (0) = 0)) := by
  decide

@[expose] public def scaledHead (values : List (Nat)) (factor : Nat) : Nat := (let scale : Nat := (factor + factor); (match values with | List.nil => scale | List.cons head _ => (head + scale)))

public theorem scaled_head : ((scaledHead ((3 :: ([] : List (Nat)))) (2) = 7) /\ (scaledHead (([] : List (Nat))) (2) = 4)) := by
  decide

public theorem or_associative : (forall (a : Bool), (forall (b : Bool), (forall (c : Bool), (((a || b) || c) = (a || (b || c)))))) := by
  decide

public theorem less_next (left : Nat) (right : Nat) : ((Nat.blt ((left + 1)) ((right + 1))) = (Nat.blt (left) (right))) := by
  rfl

public theorem equal_next (left : Nat) (right : Nat) : ((Nat.beq ((left + 1)) ((right + 1))) = (Nat.beq (left) (right))) := by
  rfl

public theorem less_successor (item : Nat) (bound : Nat) : ((Nat.blt (item) ((bound + 1))) = ((Nat.blt (item) (bound)) || (Nat.beq (item) (bound)))) := by
  induction item generalizing bound with
  | zero =>
    cases bound with
    | zero =>
      rfl
    | succ smaller =>
      rfl
  | succ previous hypothesis =>
    cases bound with
    | zero =>
      rfl
    | succ smaller =>
      simp only [equal_next, hypothesis, less_next]

public inductive Signal where
  | low
  | high

@[expose] public def isHigh (signal : Signal) : Bool := (match signal with | Signal.low => false | Signal.high => true)

@[expose] public def joinAll (Item : Type) : (front : List (Item)) -> (back : List (Item)) -> List (Item)
  | List.nil, back => back
  | List.cons head rest, back => (head :: joinAll (Item) (rest) (back))

@[expose] public def anyHigh : (signals : List (Signal)) -> Bool
  | List.nil => false
  | List.cons head rest => (isHigh (head) || anyHigh (rest))

public theorem any_high_join (front : List (Signal)) (back : List (Signal)) : (anyHigh (joinAll (Signal) (front) (back)) = (anyHigh (front) || anyHigh (back))) := by
  induction front with
  | nil =>
    rfl
  | cons head rest hypothesis =>
    simp only [anyHigh, hypothesis, joinAll, or_associative]

@[expose] public def swapSum (low : Nat) (high : Nat) : Nat := (let swapped : (Prod (Nat) (Nat)) := (high, low); (let doubled : Nat := (let bumped : Nat := ((swapped).1 + 1); (bumped + bumped)); (doubled + (swapped).2)))

public theorem swap_sum : (swapSum (2) (3) = 10) := by
  rfl

public theorem implied_pair (x : Nat) (y : Nat) : (((x < y) -> ((y <= 3) /\ (x <= 2))) -> ((x < y) -> ((y <= 3) /\ (x <= 2)))) := by
  intros
  try set_option linter.unusedSimpArgs false in simp only [← Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_true, true_and, Option.some.injEq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, LexLeanRuntime.subtract, LexLeanRuntime.multiply] at *
  all_goals omega

public theorem assumed_pair (x : Nat) (y : Nat) : ((((x <= 1) /\ (y <= 1)) -> ((x + y) <= 2)) -> ((x <= 1) -> ((y <= 1) -> ((x + y) <= 3)))) := by
  intros
  try set_option linter.unusedSimpArgs false in simp only [← Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_true, true_and, Option.some.injEq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, LexLeanRuntime.subtract, LexLeanRuntime.multiply] at *
  all_goals omega

public theorem some_bounded (x : Nat) (v : Nat) : ((Option.some (x) = Option.some (v)) -> ((x <= 4) -> (v <= 4))) := by
  intros
  try set_option linter.unusedSimpArgs false in simp only [← Bool.not_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_true, true_and, Option.some.injEq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, LexLeanRuntime.subtract, LexLeanRuntime.multiply] at *
  all_goals omega

end Recursion.Main
