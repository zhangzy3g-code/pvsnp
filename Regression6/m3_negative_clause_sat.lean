import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Regression sample (own proof): if every clause contains a negative literal,
    the empty assignment (every variable `false`) satisfies the whole CNF. -/
theorem PvsNP.Units.m3_negative_clause_sat :
    ∀ N : cnf, (∀ C ∈ N, ∃ v : var, (false, v) ∈ C) → SAT N := by
  intro N hN
  refine ⟨[], (evalCnf_clause_iff _ _).mpr ?_⟩
  intro C hC
  obtain ⟨v, hv⟩ := hN C hC
  refine (evalClause_literal_iff _ _).mpr ⟨(false, v), hv, ?_⟩
  simp [evalLiteral, evalVar]
