import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_fresh_var_split

/-- Evaluating a literal whose variable is not `z` is unaffected by forcing `z` true. -/
theorem evalLiteral_cons_assign {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (z :: a) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  simp only [evalLiteral, evalVar, List.mem_cons]
  rw [show (v = z ∨ v ∈ a) = (v ∈ a) from by simp [hl]]

theorem evalLiteral_erase_assign {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (a.erase z) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  simp only [evalLiteral, evalVar, List.mem_erase]
  rw [show (v ∈ a ∧ v ≠ z) = (v ∈ a) from by simp [hl]]

theorem evalClause_cons_assign {z : var} {C : clause} (hC : ∀ l ∈ C, l.2 ≠ z) (a : assgn) :
    evalClause (z :: a) C = evalClause a C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      simp only [evalClause, List.any_cons]
      rw [evalLiteral_cons_assign (hC l (List.mem_cons_self l C)) a,
        ih (fun l hl => hC l (List.mem_cons_of_mem l hl))]

theorem evalClause_erase_assign {z : var} {C : clause} (hC : ∀ l ∈ C, l.2 ≠ z) (a : assgn) :
    evalClause (a.erase z) C = evalClause a C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      simp only [evalClause, List.any_cons]
      rw [evalLiteral_erase_assign (hC l (List.mem_cons_self l C)) a,
        ih (fun l hl => hC l (List.mem_cons_of_mem l hl))]

theorem evalCnf_cons_assign {z : var} {N : cnf} (hN : ∀ E ∈ N, ∀ l ∈ E, l.2 ≠ z) (a : assgn) :
    evalCnf (z :: a) N = evalCnf a N := by
  induction N with
  | nil => rfl
  | cons E N ih =>
      simp only [evalCnf, List.all_cons]
      rw [evalClause_cons_assign (hN E (List.mem_cons_self E N)) a,
        ih (fun E hE => hN E (List.mem_cons_of_mem E hE))]

theorem evalCnf_erase_assign {z : var} {N : cnf} (hN : ∀ E ∈ N, ∀ l ∈ E, l.2 ≠ z) (a : assgn) :
    evalCnf (a.erase z) N = evalCnf a N := by
  induction N with
  | nil => rfl
  | cons E N ih =>
      simp only [evalCnf, List.all_cons]
      rw [evalClause_erase_assign (hN E (List.mem_cons_self E N)) a,
        ih (fun E hE => hN E (List.mem_cons_of_mem E hE))]

theorem statement : ∀ (N : cnf) (C D : clause) (z : var), (∀ E ∈ (C ++ D) :: N, ∀ l ∈ E, l.2 ≠ z) →
    (SAT (((true, z) :: C) :: ((false, z) :: D) :: N) ↔ SAT ((C ++ D) :: N)) := by
  intro N C D z hz
  have hC : ∀ l ∈ C, l.2 ≠ z :=
    fun l hl => hz (C ++ D) (List.mem_cons_self _ _) l (List.mem_append_left D hl)
  have hD : ∀ l ∈ D, l.2 ≠ z :=
    fun l hl => hz (C ++ D) (List.mem_cons_self _ _) l (List.mem_append_right C hl)
  have hN : ∀ E ∈ N, ∀ l ∈ E, l.2 ≠ z :=
    fun E hE l hl => hz E (List.mem_cons_of_mem _ hE) l hl
  constructor
  · rintro ⟨a, ha⟩
    have ha' : evalCnf a (((true, z) :: C) :: ((false, z) :: D) :: N) = true := ha
    rw [evalCnf_clause_iff] at ha'
    have h1 := ha' ((true, z) :: C) (List.mem_cons_self _ _)
    have h2 := ha' ((false, z) :: D) (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
    refine ⟨a, ?_⟩
    rw [satisfiesCnf, evalCnf_clause_iff]
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hEN
    · -- E = C ++ D
      by_cases hzv : evalVar a z = true
      · -- (false, z) evaluates to false, so D must be satisfied
        rw [evalClause_literal_iff] at h2 ⊢
        obtain ⟨l, hl, hval⟩ := h2
        rcases List.mem_cons.mp hl with hll | hlD
        · exfalso
          rw [← hll] at hval
          simp [evalLiteral, hzv] at hval
        · exact ⟨l, List.mem_append_right C hlD, hval⟩
      · -- (true, z) evaluates to false, so C must be satisfied
        have hzf : evalVar a z = false := by
          cases hv : evalVar a z with
          | true => exact absurd hv hzv
          | false => rfl
        rw [evalClause_literal_iff] at h1 ⊢
        obtain ⟨l, hl, hval⟩ := h1
        rcases List.mem_cons.mp hl with hll | hlC
        · exfalso
          rw [← hll] at hval
          simp [evalLiteral, hzf] at hval
        · exact ⟨l, List.mem_append_left D hlC, hval⟩
    · exact ha' E (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hEN))
  · rintro ⟨a, ha⟩
    have ha' : evalCnf a ((C ++ D) :: N) = true := ha
    rw [evalCnf_clause_iff] at ha'
    have hCD := ha' (C ++ D) (List.mem_cons_self _ _)
    have haN : satisfiesCnf a N := by
      rw [satisfiesCnf, evalCnf_clause_iff]
      intro E hE
      exact ha' E (List.mem_cons_of_mem _ hE)
    by_cases hCa : evalClause a C = true
    · -- force z false: (false, z) holds, C preserved
      refine ⟨a.erase z, ?_⟩
      rw [satisfiesCnf, evalCnf_clause_iff]
      intro E hE
      rcases List.mem_cons.mp hE with rfl | hE
      · rw [evalClause_literal_iff]
        exact ⟨(true, z), List.mem_cons_self _ _,
          by
            have hCz : evalClause (a.erase z) C = true := by
              rw [evalClause_erase_assign hC]; exact hCa
            rw [evalClause_literal_iff] at hCz
            obtain ⟨l, hlC, hval⟩ := hCz
            exact ⟨l, List.mem_cons_of_mem _ hlC, hval⟩⟩
      rcases List.mem_cons.mp hE with rfl | hE
      · rw [evalClause_literal_iff]
        refine ⟨(false, z), List.mem_cons_self _ _, ?_⟩
        simp [evalLiteral, evalVar]
      · have : evalClause (a.erase z) E = evalClause a E :=
          evalClause_erase_assign (hN E hE) a
        rw [this]
        exact (evalCnf_clause_iff.mp haN) E hE
    · -- C is false under a, so D is true under a; force z true
      have hDa : evalClause a D = true := by
        rw [evalClause] at hCD hCa ⊢
        simp [List.any_append] at hCD hCa ⊢
        rcases hCD with h | h
        · exact absurd h hCa
        · exact h
      refine ⟨z :: a, ?_⟩
      rw [satisfiesCnf, evalCnf_clause_iff]
      intro E hE
      rcases List.mem_cons.mp hE with rfl | hE
      · rw [evalClause_literal_iff]
        refine ⟨(true, z), List.mem_cons_self _ _, ?_⟩
        simp [evalLiteral, evalVar]
      rcases List.mem_cons.mp hE with rfl | hE
      · have hDz : evalClause (z :: a) D = true := by
          rw [evalClause_cons_assign hD]; exact hDa
        rw [evalClause_literal_iff] at hDz ⊢
        obtain ⟨l, hlD, hval⟩ := hDz
        exact ⟨l, List.mem_cons_of_mem _ hlD, hval⟩
      · have : evalClause (z :: a) E = evalClause a E :=
          evalClause_cons_assign (hN E hE) a
        rw [this]
        exact (evalCnf_clause_iff.mp haN) E hE

end PvsNP.Units.m3_fresh_var_split

theorem PvsNP.Units.m3_fresh_var_split : ∀ (N : cnf) (C D : clause) (z : var), (∀ E ∈ (C ++ D) :: N, ∀ l ∈ E, l.2 ≠ z) →
    (SAT (((true, z) :: C) :: ((false, z) :: D) :: N) ↔ SAT ((C ++ D) :: N)) :=
  PvsNP.Units.m3_fresh_var_split.statement
