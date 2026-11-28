import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Regression sample (own proof): if the complement of `l` never occurs in `N`,
    then deleting every clause that contains `l` preserves satisfiability.
    Forward: the same assignment works on a subset of clauses. Backward: force
    `l` to be true; clauses without `l` mention neither `l` nor its complement,
    so their evaluation is unchanged. -/
theorem PvsNP.Units.m3_pure_literal :
    ∀ (N : cnf) (l : literal), (∀ C ∈ N, (!l.1, l.2) ∉ C) →
      (SAT N ↔ SAT (N.filter (fun C => decide (l ∉ C)))) := by
  intro N l hpure
  obtain ⟨pol, v⟩ := l
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, (evalCnf_clause_iff a _).mpr ?_⟩
    intro C hC
    exact (evalCnf_clause_iff a N).mp ha C (List.mem_filter.mp hC).1
  · rintro ⟨a, ha⟩
    set a' : assgn := if pol then v :: a else a.filter (fun u => decide (u ≠ v)) with ha'_def
    have hforce : evalLiteral a' (pol, v) = true := by
      cases pol <;> simp [ha'_def, evalLiteral, evalVar, List.mem_filter]
    have hagree : ∀ u : var, u ≠ v → evalVar a' u = evalVar a u := by
      intro u hu
      cases pol <;> simp [ha'_def, evalVar, List.mem_filter, hu]
    refine ⟨a', (evalCnf_clause_iff a' N).mpr ?_⟩
    intro C hC
    by_cases hlC : (pol, v) ∈ C
    · exact (evalClause_literal_iff a' C).mpr ⟨(pol, v), hlC, hforce⟩
    · have hCa : evalClause a C = true :=
        (evalCnf_clause_iff a _).mp ha C
          (List.mem_filter.mpr ⟨hC, decide_eq_true hlC⟩)
      obtain ⟨⟨s, u⟩, hmem, hev⟩ := (evalClause_literal_iff a C).mp hCa
      have huv : u ≠ v := by
        rintro rfl
        by_cases hs : s = pol
        · subst hs; exact hlC hmem
        · have hsp : s = !pol := by cases s <;> cases pol <;> simp_all
          subst hsp; exact hpure C hC hmem
      refine (evalClause_literal_iff a' C).mpr ⟨(s, u), hmem, ?_⟩
      simp only [evalLiteral] at hev ⊢
      rw [hagree u huv]
      exact hev
