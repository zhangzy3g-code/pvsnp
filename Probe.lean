import Mathlib
import PvsNP.Defs
import CookLevin

/-! Template-fix probe battery round 2 (2026-11-28). -/

-- ===== Signatures round 2 =====
#check @List.mem_cons_of_mem
#check @List.mem_cons

-- P1: bare List.mem_cons_self (implicit args) in refine position
example (a : assgn) (C : clause) (z : var) :
    evalClause (z :: a) ((true, z) :: C) = true := by
  rw [evalClause_literal_iff]
  refine ⟨(true, z), List.mem_cons_self, ?_⟩
  simp [evalLiteral, evalVar]
-- P2: bare List.mem_cons_self as hypothesis argument (helper-lemma usage pattern)
example (z : var) (C : clause) (hC : ∀ l ∈ (true, z) :: C, l.2 ≠ z) : (true, z).2 ≠ z :=
  hC (true, z) List.mem_cons_self
-- P3: List.mem_cons_of_mem with explicit head arg
example (C : clause) (z : var) (l : literal) (hl : l ∈ C) : l ∈ (true, z) :: C :=
  List.mem_cons_of_mem _ hl
-- P4: List.mem_cons.mp in rcases position (used throughout tpl03)
example (a : assgn) (C : clause) (z : var) (E : clause)
    (hE : E ∈ ((true, z) :: C) :: ([] : cnf)) : True := by
  rcases List.mem_cons.mp hE with rfl | hE
  · trivial
  · trivial
-- P5: conp site A in real context (lambda goal + by_contra + hspec contradiction)
example (L : Language Bool) (V : List Bool × List Bool → Bool) (p : Polynomial ℕ)
    (hspec : ∀ x : List Bool, x ∈ Lᶜ ↔
      ∃ w : List Bool, w.length ≤ p.eval x.length ∧ V (x, w) = true)
    (x : List Bool) (hx : x ∈ L) (w : List Bool) (hw : w.length ≤ p.eval x.length) :
    (fun xw => !V xw) (x, w) = true := by
  by_contra hcon
  have hVtrue : V (x, w) = true := by
    cases hVw : V (x, w) with
    | true => rfl
    | false => simp [hVw] at hcon
  have hxc : x ∈ Lᶜ := (hspec x).mpr ⟨w, hw, hVtrue⟩
  exact ((Set.mem_compl_iff L x).mp hxc) hx
-- P6: eb calc first step in real (set) context, @-explicit eval_eq_sum_range
example (p : Polynomial ℕ) (m : ℕ) :
    p.eval m = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * m ^ i := by
  set d := p.natDegree with hd
  exact @Polynomial.eval_eq_sum_range ℕ _ p m
-- P7: same step via rw in set context
example (p : Polynomial ℕ) (m : ℕ) :
    p.eval m = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * m ^ i := by
  set d := p.natDegree with hd
  rw [Polynomial.eval_eq_sum_range]
