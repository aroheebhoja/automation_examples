import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Hammer

set_option trace.hammer.premises true
set_option trace.hammer.debug true
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option trace.aesop true

variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

-- hammer: success
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp_all only [subset_inter_iff, inter_subset_right, and_true]
  duper [*, inter_subset_inter_left, subset_inter_iff] {preprocessing := full}

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

-- hammer: success
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  duper [*, subset_union_compl_iff_inter_subset,
  subset_union_right, union_subset_union_right, union_subset_iff,
  inter_union_distrib_left, inter_union_compl]
  {preprocessing := full}

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

-- hammer -- failed (aesop failed)
-- hammer {disableAesop := true} -- failed
    /- hammer failed to preprocess facts for translation.
     Error: Auto.LamReif.reifTermCheckType :: LamTerm
     (∀ x0 : #0, (∀ x1 : #0, ((!0 x0 (λx2 : #1, ((!10 x1 x2) → False)))
     = (!1 x0 x1)))) is not type correct -/

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  hammer {disableAesop := true}

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  -- simp_all -- fails
  -- duper -- fails
  intro x hx
  simp_all -- works

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  · intro h
    exact mem_of_mem_inter_left h
  · intro h
    rw [mem_inter_iff]
    use h
    exact mem_union_left t h

example : s ∩ (s ∪ t) = s := by
  simp_all

-- hammer: success
example : s ∩ (s ∪ t) = s := by
  simp_all only [inter_eq_left, subset_union_left]

example : s ∪ s ∩ t = s := by
  simp_all

-- hammer: success
example : s ∪ s ∩ t = s := by
  simp_all only [union_eq_left, inter_subset_left]

example : s \ t ∪ t = s ∪ t := by
  simp_all

-- hammer: success
example : s \ t ∪ t = s ∪ t := by
  simp_all only [diff_union_self]

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro h
    rw [mem_diff, mem_union]
    rw [mem_union, mem_diff, mem_diff] at h
    constructor
    · rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · left; exact h
      · right; exact h
    · rw [mem_inter_iff]
      intro ⟨h1, h2⟩
      rcases h with ⟨_, h⟩ | ⟨_, h⟩
      · exact h h2
      · exact h h1
  · simp_all
    tauto

-- hammer: success
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x : 1
  simp_all only [mem_union, mem_diff, mem_inter_iff, not_and]
  apply Iff.intro
  · intro a
    cases a with
    | inl h => simp_all only [or_false, not_false_eq_true, imp_self, and_self]
    | inr h_1 => simp_all only [or_true, not_true_eq_false, implies_true, and_self]
  · intro a
    obtain ⟨left, right⟩ := a
    cases left with
    | inl h => simp_all only [forall_const, not_false_eq_true, and_self, not_true_eq_false, or_false]
    | inr h_1 => simp_all only [not_true_eq_false, imp_false, and_self, not_false_eq_true, or_true]

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example : evens ∪ odds = univ := by
  ext x
  -- hammer [Classical.em] {disableAesop := true} -- failed
    /-
    hammer failed to preprocess facts for translation.
    Error: Auto.LamReif.reifTermCheckType ::
    LamTerm (∀ x0 : Nat, (∀ x1 : (Nat → Prop),
    ((!2 (!6 (λx2 : Nat, (x1 x2))) x0) ↔ (x1 x0)))) is not type correct
    -/
  sorry

variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  rw [mem_union, mem_iInter, mem_iInter]
  constructor
  · intro h i
    rw [mem_union]
    rcases h with h | h
    · right; assumption
    · left; exact h i
  · intro h
    by_cases hs : x ∈ s
    · left; assumption
    right
    intro i
    specialize h i
    rw [mem_union] at h
    exact Or.resolve_right h hs

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  -- hammer fails here
  ext x
  -- hammer {disableAesop := true} -- works
  simp_all []
  duper [*] {preprocessing := full}

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  rw [mem_iUnion₂]
  rcases Nat.exists_infinite_primes x with ⟨p, ⟨hp2, hp1⟩⟩
  use p, hp1, hp2

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  -- hammer [mem_iUnion₂, Nat.exists_infinite_primes] {disableAesop := true} -- failed
  /-
  hammer failed to preprocess facts for translation.
  Error: Auto.LamReif.reifTermCheckType ::
  LamTerm (∀ x0 : Nat, (∀ x1 : Nat, ((!0 (x0 ≤) x1) = (x0 ≤ x1)))) is not type correct
  -/
  sorry
