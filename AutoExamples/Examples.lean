import Mathlib.Data.List.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Hammer


set_option trace.hammer.premises true
set_option trace.hammer.debug true
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option trace.aesop true

/-
Found 2312 unindexed premises in the environment, which exceeds the
maximum number of new premises (2048). Discarding premises beyond this limit
-/

-- failure

example {α : Type} [DecidableEq α] {L M : List α}
  (hl : L.Nodup) (hsubset : L ⊆ M) : L.length ≤ M.length := by
  have h1 : L ⊆ M.dedup := by
    -- exact fun _ x ↦ List.subset_dedup M (hsubset x)
    apply List.Subset.trans
    · exact hsubset
    · apply List.subset_dedup
  have h2 : M.dedup.length ≤ M.length := by
    -- apply List.Sublist.length_le
    -- exact List.dedup_sublist M
    -- hammer failed to find premise `List.Sublist.length_le`
    -- called hammer [List.Sublist.length_le]
    duper [*, List.dedup_sublist, List.Sublist.length_le] {preprocessing := full}
  have h3 : L.length ≤ M.dedup.length := by
    have := List.nodup_dedup M
    -- rw [← List.toFinset_card_of_nodup hl,
    --     ← List.toFinset_card_of_nodup (List.nodup_dedup M)]
    -- apply Finset.card_le_card
    -- repeat any_goals rw [← List.toFinset_eq]
    -- repeat assumption

    simp_all only [ge_iff_le]
    -- hammer [Finset.card_le_card, List.toFinset_eq]
    -- hammer [Finset.card_le_card, List.toFinset_eq] {disableAesop := true}
    -- duper [Finset.card_le_card, List.toFinset_eq, List.toFinset_card_of_nodup, List.nodup_dedup]
    sorry
  exact le_trans h3 h2


-- failure
theorem exists_mem_notMem_of_nodup_of_len_lt {α : Type} [DecidableEq α] {L M : List α}
  (hl : L.Nodup) (hm : M.Nodup) (hlen : L.length < M.length) :
  ∃ x ∈ M, x ∉ L := by
  -- rw [← List.toFinset_card_of_nodup hl, ← List.toFinset_card_of_nodup hm] at hlen
  -- apply Finset.exists_mem_notMem_of_card_lt_card at hlen
  -- simp_all

  -- hammer
  /- Without {disableAesop := true}, hammer does not seem to call zipperposition -/

  -- hammer [List.toFinset_card_of_nodup, Finset.exists_mem_notMem_of_card_lt_card, List.mem_toFinset] {disableAesop := true}
  duper [*, List.toFinset_card_of_nodup, Finset.exists_mem_notMem_of_card_lt_card, List.mem_toFinset]
    {preprocessing := full}

-- This worked only when giving it the two relevant lemmas
theorem dropLast_nodup_of_nodup {α : Type} [DecidableEq α] {L : List α}
    (hl : L.Nodup) : L.dropLast.Nodup := by
    -- hammer [List.Sublist.nodup, List.dropLast_sublist] {disableAesop := true}
    -- hammer {autoPremises := 32}

    duper [*, List.dropLast_eq_take, List.Sublist.nodup, List.dropLast_sublist] {preprocessing := full}

theorem back_of_back? {α : Type} {A : Array α} {a : α} (h : A.back? = some a) :
  ∃ h, A.back h = a := by
  use Array.size_pos_iff.mpr (Array.back?_isSome.mp
      (Option.isSome_of_eq_some h))

  rw [Array.back]
  rw [Array.back?] at h
  --simp [Array.getElem_eq_iff]
  --exact Array.getElem_eq_iff.mpr h
  -- hammer [Array.back, Array.back?, Array.getElem_eq_iff] {disableAesop := true}
  sorry

-- can't apply theorems..?
theorem chain'_rel_of_idx_consec {α : Type u} {R : α → α → Prop}
  {l : List α} {i j : Nat} (hi : i < l.length) (hj : j < l.length)
  (h1 : List.Chain' R l) (h2 : j = i + 1) :
  (R l[i] l[j]) := by

  -- hammer [Nat.lt_sub_of_add_lt]
  -- Are we serious here bro
  sorry

-- success
theorem pop_size_lt {α : Type} (A : Array α) (h : A ≠ #[]) :
  (A.pop).size < A.size := by
  simp_all only [ne_eq, Array.size_pop, tsub_lt_self_iff, zero_lt_one, and_true]
  apply Decidable.byContradiction
  intro a
  simp_all only [not_lt, nonpos_iff_eq_zero, Array.size_eq_zero_iff]

-- success
theorem tail_nodup_of_nodup {α : Type} {l : List α} (h : l.Nodup) : l.tail.Nodup := by
  apply List.Nodup.sublist
  · apply List.tail_sublist
  · exact h

/- Looped without timing out for 5 minutes -/
theorem mem_of_mem_pop {α : Type*} {x : α} {xs : Array α} (h : x ∈ xs.pop) : x ∈ xs := by
  --hammer
  sorry

/- Looped without timing out for 5 minutes -/
theorem getLast_not_mem_dropLast_of_nodup {α : Type u} {l : List α}
  (h1 : l ≠ []) (h2 : l.Nodup) : (l.getLast h1) ∉ l.dropLast := by
  -- hammer
  sorry

-- Sanity check
example : True := by
  simp_all only
