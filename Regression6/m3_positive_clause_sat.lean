import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Regression sample (own proof): if every clause contains a positive literal,
    the assignment that sets every occurring variable to `true` satisfies the
    whole CNF. -/
theorem PvsNP.Units.m3_positive_clause_sat :
    ∀ N : cnf, (∀ C ∈ N, ∃ v : var, (true, v) ∈ C) → SAT N := by
  intro N hN
  refine ⟨N.flatten.map Prod.snd, (evalCnf_clause_iff _ _).mpr ?_⟩
  intro C hC
  obtain ⟨v, hv⟩ := hN C hC
  refine (evalClause_literal_iff _ _).mpr ⟨(true, v), hv, ?_⟩
  have hvin : v ∈ N.flatten.map Prod.snd :=
    List.mem_map.mpr ⟨(true, v), List.mem_flatten.mpr ⟨C, hC, hv⟩, rfl⟩
  have hvv : evalVar (N.flatten.map Prod.snd) v = true := decide_eq_true hvin
  simp only [evalLiteral, hvv, decide_true]
