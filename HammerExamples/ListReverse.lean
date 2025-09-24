-- Example from MIL C06S03: inductive structures

import Mathlib.Tactic
import Hammer


set_option trace.hammer.premises true
set_option trace.hammer.debug true
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option trace.aesop true

variable {α : Type*}


open List Lean PremiseSelection

def shmeverse : List α → List α
  | []      => []
  | a :: as => shmeverse as ++ [a]

theorem shmeverse_nil : shmeverse ([] : List α) = [] := rfl
theorem shmeverse_cons (a : α) (as : List α) : shmeverse (a :: as) = shmeverse as ++ [a] := rfl

theorem shmeverse_append (as bs : List α) : shmeverse (as ++ bs) = shmeverse bs ++ shmeverse as := by
  induction' as with a as ih
  . simp_all only [nil_append, self_eq_append_right, shmeverse_nil]
  simp [*, shmeverse_cons, cons_append]

theorem shmeverse_append' (as bs : List α) : shmeverse (as ++ bs) = shmeverse bs ++ shmeverse as := by
  induction' as with a as ih
  simp_all only [nil_append, self_eq_append_right]
  rfl

  -- duper [*, shmeverse_nil, shmeverse_cons, cons_append] -- works
  -- simp [*, shmeverse_nil, shmeverse_cons, cons_append] -- works
  -- hammer [cons_append, shmeverse_cons, ih, append_assoc] -- fails: cons_append is removed from premises

  sorry

-- theorem shmeverse_shmeverse (as : List α) : shmeverse (shmeverse as) = as := by
--   induction' as with a as ih <;> simp_all [shmeverse, shmeverse_append]
/-
In this next example, the hammer works if `cons_append` is given manually, but for some reason,
we cannot coax premise selection to find that.

This doesn't help either:
-- set_premise_selector
--   mepoSelector (useRarity := false)
-/
theorem shmeverse_shmeverse' (as : List α) : shmeverse (shmeverse as) = as := by
  induction' as with a as ih
  · rfl
  -- simp [*, shmeverse, shmeverse_append] -- works
  -- duper [*, shmeverse, shmeverse_append, nil_append, cons_append] -- works
  -- hammer [shmeverse, shmeverse_append, cons_append] {disableAesop := true} -- works
  -- hammer [shmeverse, shmeverse_cons, shmeverse_append] {disableAesop := true, autoPremises := 32} -- fails (external prover could not solve)
  sorry
