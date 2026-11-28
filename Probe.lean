import Mathlib
import PvsNP.Defs
import CookLevin

/-! Template-fix probe battery round 3 (2026-11-28): tpl03 literal lemmas. -/

-- ===== Name hunt for erase membership =====
#check @List.mem_erase_iff
#check @List.mem_of_erase
#check @List.not_mem_erase
#check @List.mem_erase_of_ne
#check @List.erase_eq_erase_iff

-- R1: evalLiteral_cons_assign replacement (simp only, no rw under decide)
theorem r1 {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (z :: a) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  simp only [evalLiteral, evalVar, List.mem_cons, hv, false_or]

-- R2: evalLiteral_erase_assign replacement (full-simp membership fact)
theorem r2 {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (a.erase z) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  have hmem : (v ∈ a.erase z) = (v ∈ a) := by simp [hv]
  simp only [evalLiteral, evalVar, hmem]

-- R5: (false, z) literal closer under erase assignment (candidate line ~136 context)
example (a : assgn) (D : clause) (z : var) :
    evalClause (a.erase z) ((false, z) :: D) = true := by
  rw [evalClause_literal_iff]
  refine ⟨(false, z), List.mem_cons_self, ?_⟩
  simp [evalLiteral, evalVar]

-- R6: (true, z) literal closer under cons assignment (candidate line ~154 context)
example (a : assgn) (C : clause) (z : var) :
    evalClause (z :: a) ((true, z) :: C) = true := by
  rw [evalClause_literal_iff]
  refine ⟨(true, z), List.mem_cons_self, ?_⟩
  simp [evalLiteral, evalVar]

-- R7: restructured erase-branch first-clause case (candidate lines ~118-132 replacement)
example (a : assgn) (C : clause) (z : var)
    (evalClause_erase_assign : ∀ {C : clause}, (∀ l ∈ C, l.2 ≠ z) →
      ∀ (a : assgn), evalClause (a.erase z) C = evalClause a C)
    (hC : ∀ l ∈ C, l.2 ≠ z) (hCa : evalClause a C = true) :
    evalClause (a.erase z) ((true, z) :: C) = true := by
  have hCz : evalClause (a.erase z) C = true := by
    rw [evalClause_erase_assign hC]; exact hCa
  rw [evalClause_literal_iff] at hCz ⊢
  obtain ⟨l, hlC, hval⟩ := hCz
  exact ⟨l, List.mem_cons_of_mem _ hlC, hval⟩

-- R8a: forward exfalso branch, (false, z) case (rw [hll] direction fix)
example (a : assgn) (z : var) (l : literal)
    (hval : evalLiteral a l = true) (hll : l = (false, z))
    (hzv : evalVar a z = true) : False := by
  rw [hll] at hval
  simp [evalLiteral, hzv] at hval

-- R8b: forward exfalso branch, (true, z) case
example (a : assgn) (z : var) (l : literal)
    (hval : evalLiteral a l = true) (hll : l = (true, z))
    (hzf : evalVar a z = false) : False := by
  rw [hll] at hval
  simp [evalLiteral, hzf] at hval
