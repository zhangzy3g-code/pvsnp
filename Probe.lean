import Mathlib
import PvsNP.Defs
import CookLevin

/-! Template-fix probe battery round 5 (2026-11-28): literal lemmas via
by_cases on membership + congrArg finish (avoids transported-instance residue). -/

-- R1g: evalLiteral_cons_assign
theorem r1g {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (z :: a) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  have hvar : evalVar (z :: a) v = evalVar a v := by
    by_cases h : v ∈ a
    · have h1 : v ∈ z :: a := List.mem_cons_of_mem _ h
      simp [evalVar, h, h1]
    · have h1 : v ∉ z :: a := by
        simp only [List.mem_cons, not_or]
        exact ⟨hv, h⟩
      simp [evalVar, h, h1]
  exact congrArg (fun b : Bool => decide (b = s)) hvar

-- R2g: evalLiteral_erase_assign
theorem r2g {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (a.erase z) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  have hvar : evalVar (a.erase z) v = evalVar a v := by
    by_cases h : v ∈ a
    · have h1 : v ∈ a.erase z := (List.mem_erase_of_ne hv).mpr h
      simp [evalVar, h, h1]
    · have h1 : v ∉ a.erase z := fun hh => h ((List.mem_erase_of_ne hv).mp hh)
      simp [evalVar, h, h1]
  exact congrArg (fun b : Bool => decide (b = s)) hvar

-- R3g: evalLiteral_filter_assign
theorem r3g {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (a.filter (· ≠ z)) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  have hvar : evalVar (a.filter (· ≠ z)) v = evalVar a v := by
    by_cases h : v ∈ a
    · have h1 : v ∈ a.filter (· ≠ z) := List.mem_filter.mpr ⟨h, hv⟩
      simp [evalVar, h, h1]
    · have h1 : v ∉ a.filter (· ≠ z) := fun hh => h (List.mem_filter.mp hh).1
      simp [evalVar, h, h1]
  exact congrArg (fun b : Bool => decide (b = s)) hvar
