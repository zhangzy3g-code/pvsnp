import Mathlib
import CookLevin

-- Probe 1: does the constant exist at all in this environment?
#check @Set.mem_compl_iff

-- Probe 2: bare .mp / .mpr projection on the constant (the failing usage in m2_conp_verifier_iff)
example (s : Set Nat) (x : Nat) (h : x ∈ sᶜ) : x ∉ s := Set.mem_compl_iff.mp h

example (s : Set Nat) (x : Nat) (h : x ∉ s) : x ∈ sᶜ := Set.mem_compl_iff.mpr h

-- Probe 3: CookLevin constant existence + bare .mp (the failing usage in m3_fresh_var_split)
#check @evalCnf_clause_iff

example (a : assgn) (N : cnf) (h : evalCnf a N = true) :
    ∀ C, C ∈ N → evalClause a C = true := evalCnf_clause_iff.mp h

-- Probe 4: Polynomial lemma shape (the mismatch in m2_eb_poly)
#check @Polynomial.eval_eq_sum_range

-- Probe 5: the `cases h : e` + `exact h` pattern from m2_conp_verifier_iff line ~71
example (V : Nat → Bool) (x : Nat) (hcon : ¬ (!V x) = true) : V x = true := by
  cases hVw : V x with
  | true => exact hVw
  | false => simp [hVw] at hcon
