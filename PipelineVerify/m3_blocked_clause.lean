import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Self-authored proof (self-authored-20261128): self-authored proof for `m3_blocked_clause`,
    written from the statement alone for the desk pre-solve bank. -/
theorem PvsNP.Units.m3_blocked_clause :
    ∀ (N : cnf) (C : clause) (l : literal), l ∈ C →
  (∀ D ∈ N, (!l.1, l.2) ∈ D → ∃ m ∈ C, m ≠ l ∧ (!m.1, m.2) ∈ D) →
    (SAT (C :: N) ↔ SAT N) := by
  intro N C l hlC hblocked
  obtain ⟨pol, v⟩ := l
  have hBool : ∀ {s t : Bool}, s ≠ t → s = !t := by
    intro s t h
    cases s <;> cases t <;> simp_all
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, (evalCnf_clause_iff a N).mpr fun D hD =>
      (evalCnf_clause_iff a (C :: N)).mp ha D (List.mem_cons_of_mem C hD)⟩
  · rintro ⟨a, ha⟩
    by_cases hCa : evalClause a C = true
    · refine ⟨a, (evalCnf_clause_iff a (C :: N)).mpr fun D hD => ?_⟩
      rcases List.mem_cons.mp hD with rfl | hDN
      · exact hCa
      · exact (evalCnf_clause_iff a N).mp ha D hDN
    · -- a falsifies C; flip l to true and repair every clause of N.
      set a' : assgn := if pol then v :: a else a.filter (fun u => decide (u ≠ v)) with ha'_def
      have hforce : evalLiteral a' (pol, v) = true := by
        cases pol <;> simp [ha'_def, evalLiteral, evalVar, List.mem_filter]
      have hagree : ∀ u : var, u ≠ v → evalVar a' u = evalVar a u := by
        intro u hu
        cases pol <;> simp [ha'_def, evalVar, List.mem_filter, hu]
      have hCfalse : ∀ m ∈ C, evalLiteral a m = false := by
        intro m hm
        by_cases h : evalLiteral a m = true
        · exact absurd ((evalClause_literal_iff a C).mpr ⟨m, hm, h⟩) hCa
        · have h2 : evalLiteral a m ≠ true := h
          cases h3 : evalLiteral a m with
          | false => rfl
          | true => exact absurd h3 h
      refine ⟨a', (evalCnf_clause_iff a' (C :: N)).mpr fun D hD => ?_⟩
      rcases List.mem_cons.mp hD with rfl | hDN
      · exact (evalClause_literal_iff a' C).mpr ⟨(pol, v), hlC, hforce⟩
      · have haD : evalClause a D = true := (evalCnf_clause_iff a N).mp ha D hDN
        by_cases hDl : (!pol, v) ∈ D
        · obtain ⟨m, hmC, hmne, hmD⟩ := hblocked D hDN hDl
          obtain ⟨ms, mv⟩ := m
          by_cases hmv : mv = v
          · subst hmv
            have hms : ms = !pol := hBool (fun h => hmne (by rw [h]))
            have hlit : (!ms, v) = (pol, v) := by rw [hms, Bool.not_not]
            exact (evalClause_literal_iff a' D).mpr ⟨(!ms, v), hmD, by rw [hlit]; exact hforce⟩
          · have hlit : evalLiteral a' (!ms, mv) = true := by
              have hf := hCfalse (ms, mv) hmC
              cases h1 : evalVar a mv <;> cases h2 : ms <;>
                simp [evalLiteral, h1, h2, hagree mv hmv] at hf ⊢
            exact (evalClause_literal_iff a' D).mpr ⟨(!ms, mv), hmD, hlit⟩
        · obtain ⟨m, hmD, hmtrue⟩ := (evalClause_literal_iff a D).mp haD
          obtain ⟨ms, mv⟩ := m
          by_cases hmv : mv = v
          · subst hmv
            by_cases hms : ms = pol
            · subst hms
              exact (evalClause_literal_iff a' D).mpr ⟨(pol, v), hmD, hforce⟩
            · have hms2 : ms = !pol := hBool hms
              rw [hms2] at hmD
              exact absurd hmD hDl
          · refine (evalClause_literal_iff a' D).mpr ⟨(ms, mv), hmD, ?_⟩
            simp only [evalLiteral] at hmtrue ⊢
            rw [hagree mv hmv]
            exact hmtrue
