import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Regression sample (own proof): a clause containing both polarities of the
    same variable is true under every assignment, so prepending it to a CNF
    does not change satisfiability. -/
theorem PvsNP.Units.m3_tautology_clause :
    ∀ (N : cnf) (C : clause) (v : var), (true, v) ∈ C → (false, v) ∈ C →
      (SAT (C :: N) ↔ SAT N) := by
  intro N C v hpos hneg
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, (evalCnf_clause_iff a N).mpr ?_⟩
    intro D hD
    exact (evalCnf_clause_iff a (C :: N)).mp ha D (List.mem_cons_of_mem C hD)
  · rintro ⟨a, ha⟩
    refine ⟨a, (evalCnf_clause_iff a (C :: N)).mpr ?_⟩
    intro D hD
    rcases List.mem_cons.mp hD with hDC | hD
    · rw [hDC]
      by_cases hv : evalVar a v = true
      · exact (evalClause_literal_iff a C).mpr ⟨(true, v), hpos, by simp [evalLiteral, hv]⟩
      · have hv' : evalVar a v = false := by
          cases h : evalVar a v with
          | false => rfl
          | true => exact absurd h hv
        exact (evalClause_literal_iff a C).mpr ⟨(false, v), hneg, by simp [evalLiteral, hv']⟩
    · exact (evalCnf_clause_iff a N).mp ha D hD
