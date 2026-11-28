import Mathlib
import PvsNP.Defs
import CookLevin

/-! Template-fix probe battery round 4 (2026-11-28): full-simp literal lemmas
and the filter-based "force z false" route for tpl03. -/

-- R1f: evalLiteral_cons_assign via full simp
theorem r1f {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (z :: a) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  simp [evalLiteral, evalVar, hv]

-- R2f: evalLiteral_erase_assign via full simp + mem_erase_of_ne as rewrite
theorem r2f {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (a.erase z) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  simp [evalLiteral, evalVar, List.mem_erase_of_ne hv]

-- R3f: evalLiteral_filter_assign via full simp
theorem r3f {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (a.filter (· ≠ z)) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  simp [evalLiteral, evalVar, hv]

-- R5f: (false, z) literal closer under filter assignment
example (a : assgn) (D : clause) (z : var) :
    evalClause (a.filter (· ≠ z)) ((false, z) :: D) = true := by
  rw [evalClause_literal_iff]
  refine ⟨(false, z), List.mem_cons_self, ?_⟩
  simp [evalLiteral, evalVar]

-- R7f: restructured filter-branch first-clause case (pattern of R7, filter version)
example (a : assgn) (C : clause) (z : var)
    (evalClause_filter_assign : ∀ {C : clause}, (∀ l ∈ C, l.2 ≠ z) →
      ∀ (a : assgn), evalClause (a.filter (· ≠ z)) C = evalClause a C)
    (hC : ∀ l ∈ C, l.2 ≠ z) (hCa : evalClause a C = true) :
    evalClause (a.filter (· ≠ z)) ((true, z) :: C) = true := by
  have hCz : evalClause (a.filter (· ≠ z)) C = true := by
    rw [evalClause_filter_assign hC]; exact hCa
  rw [evalClause_literal_iff] at hCz ⊢
  obtain ⟨l, hlC, hval⟩ := hCz
  exact ⟨l, List.mem_cons_of_mem _ hlC, hval⟩
