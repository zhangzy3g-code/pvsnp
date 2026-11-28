import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Regression sample (own proof): the two clauses `¬x ∨ y` and `x ∨ ¬y` force
    `x` and `y` to take the same value, so under their presence every `x` in
    `N` may be replaced by `y` without changing satisfiability. Forward uses
    the same assignment; backward redefines the value of `x` to match `y`. -/
theorem PvsNP.Units.m3_equiv_literal_subst :
    ∀ (N : cnf) (x y : var), x ≠ y →
      (SAT ([(false, x), (true, y)] :: [(true, x), (false, y)] :: N) ↔
        SAT (N.map (fun C => C.map (fun l => if l.2 = x then (l.1, y) else l)))) := by
  intro N x y hxy
  constructor
  · rintro ⟨a, ha⟩
    have hC1 : evalClause a [(false, x), (true, y)] = true :=
      (evalCnf_clause_iff a _).mp ha _ (by simp)
    have hC2 : evalClause a [(true, x), (false, y)] = true :=
      (evalCnf_clause_iff a _).mp ha _
        (List.mem_cons_of_mem _ List.mem_cons_self)
    have hxy_eq : evalVar a x = evalVar a y := by
      cases hx : evalVar a x <;> cases hy : evalVar a y
      · rfl
      · exfalso
        have hbad : evalClause a [(true, x), (false, y)] = false := by
          simp [evalClause, evalLiteral, hx, hy]
        rw [hbad] at hC2
        exact Bool.false_ne_true hC2
      · exfalso
        have hbad : evalClause a [(false, x), (true, y)] = false := by
          simp [evalClause, evalLiteral, hx, hy]
        rw [hbad] at hC1
        exact Bool.false_ne_true hC1
      · rfl
    refine ⟨a, (evalCnf_clause_iff a _).mpr ?_⟩
    intro C' hC'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
    have hCa : evalClause a C = true :=
      (evalCnf_clause_iff a _).mp ha C
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))
    obtain ⟨⟨s, u⟩, hmem, hev⟩ := (evalClause_literal_iff a C).mp hCa
    refine (evalClause_literal_iff a _).mpr
      ⟨(fun l => if l.2 = x then (l.1, y) else l) (s, u),
        List.mem_map.mpr ⟨(s, u), hmem, rfl⟩, ?_⟩
    by_cases hu : u = x
    · have himg : (fun l => if l.2 = x then (l.1, y) else l) (s, u) = (s, y) := by
        simp [hu]
      rw [himg]
      simp only [evalLiteral] at hev ⊢
      rw [hu, hxy_eq] at hev
      exact hev
    · have himg : (fun l => if l.2 = x then (l.1, y) else l) (s, u) = (s, u) := by
        simp [hu]
      rw [himg]
      exact hev
  · rintro ⟨a, ha⟩
    set a' : assgn := if y ∈ a then x :: a
      else a.filter (fun u => decide (u ≠ x)) with ha'_def
    have hax : evalVar a' x = evalVar a y := by
      by_cases hy : y ∈ a <;> simp [ha'_def, evalVar, List.mem_filter, hy]
    have hagree : ∀ u : var, u ≠ x → evalVar a' u = evalVar a u := by
      intro u hu
      by_cases hy : y ∈ a <;>
        simp [ha'_def, evalVar, List.mem_filter, hu, hy]
    refine ⟨a', (evalCnf_clause_iff a' _).mpr ?_⟩
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · by_cases hy : evalVar a y = true
      · refine (evalClause_literal_iff a' _).mpr ⟨(true, y), by simp, ?_⟩
        simp only [evalLiteral]
        rw [hagree y hxy.symm, hy]
        rfl
      · have hy' : evalVar a y = false := by
          cases h : evalVar a y with
          | false => rfl
          | true => exact absurd h hy
        refine (evalClause_literal_iff a' _).mpr ⟨(false, x), by simp, ?_⟩
        simp only [evalLiteral]
        rw [hax, hy']
        rfl
    · rcases List.mem_cons.mp hC with rfl | hC
      · by_cases hy : evalVar a y = true
        · refine (evalClause_literal_iff a' _).mpr ⟨(true, x), by simp, ?_⟩
          simp only [evalLiteral]
          rw [hax, hy]
          rfl
        · have hy' : evalVar a y = false := by
            cases h : evalVar a y with
            | false => rfl
            | true => exact absurd h hy
          refine (evalClause_literal_iff a' _).mpr ⟨(false, y), by simp, ?_⟩
          simp only [evalLiteral]
          rw [hagree y hxy.symm, hy']
          rfl
      · have hCa : evalClause a (C.map (fun l => if l.2 = x then (l.1, y) else l)) = true :=
          (evalCnf_clause_iff a _).mp ha _ (List.mem_map.mpr ⟨C, hC, rfl⟩)
        obtain ⟨l', hl', hev⟩ := (evalClause_literal_iff a _).mp hCa
        obtain ⟨⟨s, u⟩, hmem, rfl⟩ := List.mem_map.mp hl'
        refine (evalClause_literal_iff a' C).mpr ⟨(s, u), hmem, ?_⟩
        by_cases hu : u = x
        · have himg : (fun l => if l.2 = x then (l.1, y) else l) (s, u) = (s, y) := by
            simp [hu]
          have h1 : evalLiteral a' (s, u) = evalLiteral a (s, y) := by
            simp only [evalLiteral, hu, hax]
          rw [h1, ← himg]
          exact hev
        · have himg : (fun l => if l.2 = x then (l.1, y) else l) (s, u) = (s, u) := by
            simp [hu]
          have h1 : evalLiteral a' (s, u) = evalLiteral a (s, u) := by
            simp only [evalLiteral, hagree u hu]
          rw [h1, ← himg]
          exact hev
