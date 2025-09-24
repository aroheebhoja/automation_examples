-- Examples from MIL C03S04: conjunction and iff
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Hammer


set_option trace.hammer.premises true
set_option trace.hammer.debug true
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option trace.aesop true

-- hammer: success
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  -- rcases h with ⟨h0, h1⟩
  -- constructor
  -- · exact h0
  -- intro h2
  -- apply h1
  -- apply Nat.dvd_antisymm h0 h2
  simp_all only [ne_eq, true_and]
  obtain ⟨left, right⟩ := h
  apply Aesop.BuiltinRules.not_intro
  intro a
  duper [*, Nat.dvd_antisymm] {preprocessing := full}

-- hammer: filled in partial proof
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  -- constructor
  -- · rintro ⟨h0, h1⟩
  --   constructor
  --   · exact h0
  --   intro h2
  --   apply h1
  --   rw [h2]
  -- rintro ⟨h0, h1⟩
  -- constructor
  -- · exact h0
  -- intro h2
  -- apply h1
  -- apply le_antisymm h0 h2
  simp_all only [not_le, ne_eq, and_congr_right_iff]
  intro a
  apply Iff.intro
  · intro a_1
    apply Aesop.BuiltinRules.not_intro
    intro a_2
    subst a_2
    simp_all only [le_refl, lt_self_iff_false]
  · intro a_1
    -- sorry
    -- hammer: success (had to call it again here)
    duper [*, le_iff_lt_or_eq] {preprocessing := full}


theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  pow_eq_zero h'

-- hammer: looped for 5 minutes without timing out
-- hammer {disableAesop := true}: failed (external prover could not solve)
example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  
  constructor
  -- hammer {disableAesop := true} [add_comm]: success
  duper [*, add_comm, aux, sq_eq_zero_iff] {preprocessing := full}
  -- hammer: success
  simp_all []
  -- · intro h
  --   constructor
  --   · exact aux h
  --   rw [add_comm] at h
  --   exact aux h
  -- rintro ⟨rfl, rfl⟩
  -- norm_num

-- hammer: filled in partial proof
theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  -- rw [Monotone]
  -- push_neg
  -- rfl
  simp_all only [gt_iff_lt]
  apply Iff.intro
  · intro a
    -- hammer [Monotone] {disableAesop := true}
    /-
    hammer failed to preprocess facts for translation.
    Error: Auto.LamReif.reifTermCheckType :: LamTerm
    (∀ x0 : #0, (∀ x1 : #0, ((!4 (!22 x0) x1) = (!1 x0 x1)))) is not type correct
    -/
    sorry
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    obtain ⟨left, right⟩ := h
    apply Aesop.BuiltinRules.not_intro
    intro a
    -- hammer [Monotone] {disableAesop := true} : failed
    /-
    hammer failed to preprocess facts for translation.
    Error: Auto.LamReif.reifTermCheckType :: LamTerm
    ((!13 !17 !18) = !8) is not type correct
    -/
    sorry

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff]
  use 0, 1
  norm_num

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

-- hammer: success
example : a < b ↔ a ≤ b ∧ a ≠ b := by
  simp_all only [ne_eq]
  apply Iff.intro
  · intro a_1
    apply And.intro
    · duper [*, le_iff_lt_or_eq] {preprocessing := full}
    · apply Aesop.BuiltinRules.not_intro
      intro a_2
      subst a_2
      simp_all only [lt_self_iff_false]
  · intro a_1
    obtain ⟨left, right⟩ := a_1
    duper [*, le_iff_lt_or_eq] {preprocessing := full}
  -- rw [lt_iff_le_not_ge]
  -- constructor
  -- · rintro ⟨h0, h1⟩
  --   constructor
  --   · exact h0
  --   intro h2
  --   apply h1
  --   rw [h2]
  -- rintro ⟨h0, h1⟩
  -- constructor
  -- · exact h0
  -- intro h2
  -- apply h1
  -- apply le_antisymm h0 h2

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

-- hammer: success
example : ¬a < a := by
  -- rw [lt_iff_le_not_ge]
  -- rintro ⟨h0, h1⟩
  -- exact h1 h0
  simp_all only [lt_self_iff_false, not_false_eq_true]

-- hammer: success
example : a < b → b < c → a < c := by
  -- simp only [lt_iff_le_not_ge]
  -- rintro ⟨h0, h1⟩ ⟨h2, h3⟩
  -- constructor
  -- · apply le_trans h0 h2
  -- intro h4
  -- apply h1
  -- apply le_trans h2 h4
  intro a_1 a_2
  duper [*, LT.lt.trans_le, le_of_lt] {preprocessing := full}
