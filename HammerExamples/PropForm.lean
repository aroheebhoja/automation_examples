import Mathlib.Tactic
import Hammer

set_option trace.hammer.premises true
set_option trace.hammer.debug true
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option trace.aesop true


inductive PropForm : Type where
  | var (n : ℕ)           : PropForm
  | fls                   : PropForm
  | conj (A B : PropForm) : PropForm
  | disj (A B : PropForm) : PropForm
  | impl (A B : PropForm) : PropForm
namespace PropForm

def eval : PropForm → (ℕ → Bool) → Bool
  | var n,    v => v n
  | fls,      _ => false
  | conj A B, v => A.eval v && B.eval v
  | disj A B, v => A.eval v || B.eval v
  | impl A B, v => ! A.eval v || B.eval v

def vars : PropForm → Finset ℕ
  | var n    => {n}
  | fls      => ∅
  | conj A B => A.vars ∪ B.vars
  | disj A B => A.vars ∪ B.vars
  | impl A B => A.vars ∪ B.vars

def subst : PropForm → ℕ → PropForm → PropForm
  | var n,    m, C => if n = m then C else var n
  | fls,      _, _ => fls
  | conj A B, m, C => conj (A.subst m C) (B.subst m C)
  | disj A B, m, C => disj (A.subst m C) (B.subst m C)
  | impl A B, m, C => impl (A.subst m C) (B.subst m C)

theorem subst_eq_of_not_mem_vars' (A : PropForm) (n : ℕ) (C : PropForm):
    n ∉ A.vars → A.subst n C = A := by
  cases A <;> simp_all [subst, vars, subst_eq_of_not_mem_vars']; tauto

example (A : PropForm) (n : ℕ) (C : PropForm):
    n ∉ A.vars → A.subst n C = A := by
  cases A
  -- hammer failed on all cases
  stop
  sorry

-- theorem subst_eval_eq' (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → Bool) :
--     (A.subst n C).eval v = A.eval (fun m => if m = n then C.eval v else v m) := by
--   cases A <;> simp [subst, eval, subst_eval_eq'];
--     split <;> simp_all [eval]

example (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → Bool) :
    (A.subst n C).eval v = A.eval (fun m => if m = n then C.eval v else v m) := by
  cases A
  -- hammer failed on all cases
  stop
  sorry


end PropForm
