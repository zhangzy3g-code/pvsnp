import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Regression sample (own proof): a CNF containing the empty clause cannot be
    satisfied, because the empty clause evaluates to `false` under every
    assignment. -/
theorem PvsNP.Units.m3_empty_clause_unsat : ∀ N : cnf, [] ∈ N → ¬ SAT N := by
  intro N hmem hsat
  obtain ⟨a, ha⟩ := hsat
  have hnil : evalClause a [] = true := (evalCnf_clause_iff a N).mp ha [] hmem
  have hempty : evalClause a ([] : clause) = false := rfl
  rw [hempty] at hnil
  exact Bool.false_ne_true hnil
