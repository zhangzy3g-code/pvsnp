import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Self-authored proof (self-authored-20261128): self-authored proof for `m3_autarky`,
    written from the statement alone for the desk pre-solve bank. -/
theorem PvsNP.Units.m3_autarky :
    ∀ (N : cnf) (vs : List var) (a : assgn),
  (∀ C ∈ N, (∃ l ∈ C, l.2 ∈ vs) → ∃ l ∈ C, l.2 ∈ vs ∧ evalLiteral a l = true) →
    (SAT N ↔ SAT (N.filter (fun C => decide (∀ l ∈ C, l.2 ∉ vs)))) := by
  intro N vs a haut
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, (evalCnf_clause_iff b _).mpr fun C hC =>
      (evalCnf_clause_iff b N).mp hb C (List.mem_filter.mp hC).1⟩
  · rintro ⟨b, hb⟩
    set a' : assgn := a.filter (fun u => decide (u ∈ vs)) ++
      b.filter (fun u => decide (u ∉ vs)) with ha'_def
    have hagree_in : ∀ u : var, u ∈ vs → evalVar a' u = evalVar a u := by
      intro u hu
      simp [ha'_def, evalVar, List.mem_filter, List.mem_append, hu]
    have hagree_out : ∀ u : var, u ∉ vs → evalVar a' u = evalVar b u := by
      intro u hu
      simp [ha'_def, evalVar, List.mem_filter, List.mem_append, hu]
    refine ⟨a', (evalCnf_clause_iff a' N).mpr fun C hC => ?_⟩
    by_cases htouch : ∃ l ∈ C, l.2 ∈ vs
    · obtain ⟨l, hlC, hlvs, hltrue⟩ := haut C hC htouch
      obtain ⟨s, u⟩ := l
      refine (evalClause_literal_iff a' C).mpr ⟨(s, u), hlC, ?_⟩
      simp only [evalLiteral] at hltrue ⊢
      rw [hagree_in u hlvs]
      exact hltrue
    · have hC' : C ∈ N.filter (fun C => decide (∀ l ∈ C, l.2 ∉ vs)) := by
        rw [List.mem_filter]
        refine ⟨hC, ?_⟩
        simp only [decide_eq_true_eq]
        intro l hl hlv
        exact htouch ⟨l, hl, hlv⟩
      obtain ⟨m, hmC, hmtrue⟩ := (evalClause_literal_iff b C).mp
        ((evalCnf_clause_iff b _).mp hb C hC')
      obtain ⟨ms, mu⟩ := m
      have hmu : mu ∉ vs := fun hcon => htouch ⟨(ms, mu), hmC, hcon⟩
      refine (evalClause_literal_iff a' C).mpr ⟨(ms, mu), hmC, ?_⟩
      simp only [evalLiteral] at hmtrue ⊢
      rw [hagree_out mu hmu]
      exact hmtrue

#print axioms PvsNP.Units.m3_autarky

example : (1 : ℕ) = 2 := rfl
