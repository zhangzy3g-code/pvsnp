/-
模板 tpl03 — SAT 族：新鲜变量分裂（在新变量上对子句做 case split）
来源：pvsnp-repo/PvsNP/Units/m3_fresh_var_split.lean（本队证明；与 drafts/m3_fresh_var_split_check.lean 仅差 1 行）
编译状态：⚠ 已结算文本在钉版 Lean v4.36.0 下不过（mem_cons_self 全隐式参数、
  List.mem_erase 改名、裸 .mp 投影、rw 方向与 simp 规范形漂移等多处构造问题）；
  2026-11-28 已按钉版修复并过 Actions 终验＋公理门，见
  desk-auto/TEMPLATE-FIX-20261128.md。陈述未动。
填空点：① 两个分裂子句的形状（这里 (true,z)::C 与 (false,z)::D 合并为 C++D，按题换）；
  ② 新鲜性假设的陈述（这里 ∀ E ∈ (C++D)::N, ∀ l ∈ E, l.2 ≠ z）；
  ③ 反向的赋值强制方式（z 真用 z::a、z 假用 a.filter (· ≠ z)，配 tpl01 部件 B；
     2026-11-28 修复注：原稿 z 假用 a.erase z 有真漏洞——erase 只删首个 z，
     赋值含重复 z 时 (false, z) 在 a.erase z 下不成立，已改 filter 并新增 filter 同余链）。
引理链：evalLiteral/evalClause/evalCnf 的 cons_assign、erase_assign 与 filter_assign 同余链 → 主定理双向。
-/
import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_fresh_var_split

/-- Evaluating a literal whose variable is not `z` is unaffected by forcing `z` true. -/
theorem evalLiteral_cons_assign {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (z :: a) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  have hvar : evalVar (z :: a) v = evalVar a v := by
    by_cases h : v ∈ a
    · have h1 : v ∈ z :: a := List.mem_cons_of_mem _ h
      simp [evalVar, h, h1]
    · have h1 : v ∉ z :: a := by
        simp only [List.mem_cons, not_or]
        exact ⟨hv, h⟩
      simp [evalVar, h, h1]
  exact congrArg (fun b : Bool => decide (b = s)) hvar

theorem evalLiteral_erase_assign {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (a.erase z) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  have hvar : evalVar (a.erase z) v = evalVar a v := by
    by_cases h : v ∈ a
    · have h1 : v ∈ a.erase z := (List.mem_erase_of_ne hv).mpr h
      simp [evalVar, h, h1]
    · have h1 : v ∉ a.erase z := fun hh => h ((List.mem_erase_of_ne hv).mp hh)
      simp [evalVar, h, h1]
  exact congrArg (fun b : Bool => decide (b = s)) hvar

theorem evalClause_cons_assign {z : var} {C : clause} (hC : ∀ l ∈ C, l.2 ≠ z) (a : assgn) :
    evalClause (z :: a) C = evalClause a C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      show evalLiteral (z :: a) l || evalClause (z :: a) C
          = evalLiteral a l || evalClause a C
      rw [evalLiteral_cons_assign (hC l List.mem_cons_self) a,
        ih (fun l hl => hC l (List.mem_cons_of_mem _ hl))]

theorem evalClause_erase_assign {z : var} {C : clause} (hC : ∀ l ∈ C, l.2 ≠ z) (a : assgn) :
    evalClause (a.erase z) C = evalClause a C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      show evalLiteral (a.erase z) l || evalClause (a.erase z) C
          = evalLiteral a l || evalClause a C
      rw [evalLiteral_erase_assign (hC l List.mem_cons_self) a,
        ih (fun l hl => hC l (List.mem_cons_of_mem _ hl))]

theorem evalCnf_cons_assign {z : var} {N : cnf} (hN : ∀ E ∈ N, ∀ l ∈ E, l.2 ≠ z) (a : assgn) :
    evalCnf (z :: a) N = evalCnf a N := by
  induction N with
  | nil => rfl
  | cons E N ih =>
      show evalClause (z :: a) E && evalCnf (z :: a) N
          = evalClause a E && evalCnf a N
      rw [evalClause_cons_assign (hN E List.mem_cons_self) a,
        ih (fun E hE => hN E (List.mem_cons_of_mem _ hE))]

theorem evalCnf_erase_assign {z : var} {N : cnf} (hN : ∀ E ∈ N, ∀ l ∈ E, l.2 ≠ z) (a : assgn) :
    evalCnf (a.erase z) N = evalCnf a N := by
  induction N with
  | nil => rfl
  | cons E N ih =>
      show evalClause (a.erase z) E && evalCnf (a.erase z) N
          = evalClause a E && evalCnf a N
      rw [evalClause_erase_assign (hN E List.mem_cons_self) a,
        ih (fun E hE => hN E (List.mem_cons_of_mem _ hE))]

/-- Evaluating a literal whose variable is not `z` is unaffected by deleting
every occurrence of `z` from the assignment. (Forcing `z` false must use
`filter`, not `List.erase`: `erase` removes only the first occurrence, so
`(false, z)` need not hold under `a.erase z` when `z` occurs twice.) -/
theorem evalLiteral_filter_assign {z : var} {l : literal} (hl : l.2 ≠ z) (a : assgn) :
    evalLiteral (a.filter (· ≠ z)) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  have hvar : evalVar (a.filter (· ≠ z)) v = evalVar a v := by
    by_cases h : v ∈ a
    · have h1 : v ∈ a.filter (· ≠ z) := List.mem_filter.mpr ⟨h, by simp [hv]⟩
      simp [evalVar, h, h1, hv]
    · have h1 : v ∉ a.filter (· ≠ z) := fun hh => h (List.mem_filter.mp hh).1
      simp [evalVar, h, h1]
  exact congrArg (fun b : Bool => decide (b = s)) hvar

theorem evalClause_filter_assign {z : var} {C : clause} (hC : ∀ l ∈ C, l.2 ≠ z) (a : assgn) :
    evalClause (a.filter (· ≠ z)) C = evalClause a C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      show evalLiteral (a.filter (· ≠ z)) l || evalClause (a.filter (· ≠ z)) C
          = evalLiteral a l || evalClause a C
      rw [evalLiteral_filter_assign (hC l List.mem_cons_self) a,
        ih (fun l hl => hC l (List.mem_cons_of_mem _ hl))]

theorem evalCnf_filter_assign {z : var} {N : cnf} (hN : ∀ E ∈ N, ∀ l ∈ E, l.2 ≠ z) (a : assgn) :
    evalCnf (a.filter (· ≠ z)) N = evalCnf a N := by
  induction N with
  | nil => rfl
  | cons E N ih =>
      show evalClause (a.filter (· ≠ z)) E && evalCnf (a.filter (· ≠ z)) N
          = evalClause a E && evalCnf a N
      rw [evalClause_filter_assign (hN E List.mem_cons_self) a,
        ih (fun E hE => hN E (List.mem_cons_of_mem _ hE))]

theorem statement : ∀ (N : cnf) (C D : clause) (z : var), (∀ E ∈ (C ++ D) :: N, ∀ l ∈ E, l.2 ≠ z) →
    (SAT (((true, z) :: C) :: ((false, z) :: D) :: N) ↔ SAT ((C ++ D) :: N)) := by
  intro N C D z hz
  have hC : ∀ l ∈ C, l.2 ≠ z :=
    fun l hl => hz (C ++ D) List.mem_cons_self l (List.mem_append_left D hl)
  have hD : ∀ l ∈ D, l.2 ≠ z :=
    fun l hl => hz (C ++ D) List.mem_cons_self l (List.mem_append_right C hl)
  have hN : ∀ E ∈ N, ∀ l ∈ E, l.2 ≠ z :=
    fun E hE l hl => hz E (List.mem_cons_of_mem _ hE) l hl
  constructor
  · rintro ⟨a, ha⟩
    have ha' : evalCnf a (((true, z) :: C) :: ((false, z) :: D) :: N) = true := ha
    rw [evalCnf_clause_iff] at ha'
    have h1 := ha' ((true, z) :: C) List.mem_cons_self
    have h2 := ha' ((false, z) :: D) (List.mem_cons_of_mem _ List.mem_cons_self)
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
          rw [hll] at hval
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
          rw [hll] at hval
          simp [evalLiteral, hzf] at hval
        · exact ⟨l, List.mem_append_left D hlC, hval⟩
    · exact ha' E (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hEN))
  · rintro ⟨a, ha⟩
    have ha' : evalCnf a ((C ++ D) :: N) = true := ha
    rw [evalCnf_clause_iff] at ha'
    have hCD := ha' (C ++ D) List.mem_cons_self
    have haN : satisfiesCnf a N := by
      rw [satisfiesCnf, evalCnf_clause_iff]
      intro E hE
      exact ha' E (List.mem_cons_of_mem _ hE)
    by_cases hCa : evalClause a C = true
    · -- force z false: (false, z) holds, C preserved
      refine ⟨a.filter (· ≠ z), ?_⟩
      rw [satisfiesCnf, evalCnf_clause_iff]
      intro E hE
      rcases List.mem_cons.mp hE with rfl | hE
      · have hCz : evalClause (a.filter (· ≠ z)) C = true := by
          rw [evalClause_filter_assign hC]; exact hCa
        rw [evalClause_literal_iff] at hCz ⊢
        obtain ⟨l, hlC, hval⟩ := hCz
        exact ⟨l, List.mem_cons_of_mem _ hlC, hval⟩
      rcases List.mem_cons.mp hE with rfl | hE
      · rw [evalClause_literal_iff]
        refine ⟨(false, z), List.mem_cons_self, ?_⟩
        simp [evalLiteral, evalVar]
      · have : evalClause (a.filter (· ≠ z)) E = evalClause a E :=
          evalClause_filter_assign (hN E hE) a
        rw [this]
        exact ((evalCnf_clause_iff a N).mp haN) E hE
    · -- C is false under a, so D is true under a; force z true
      have hDa : evalClause a D = true := by
        rw [evalClause_literal_iff] at hCD ⊢
        obtain ⟨l, hl, hval⟩ := hCD
        rcases List.mem_append.mp hl with hlC | hlD
        · exfalso
          apply hCa
          rw [evalClause_literal_iff]
          exact ⟨l, hlC, hval⟩
        · exact ⟨l, hlD, hval⟩
      refine ⟨z :: a, ?_⟩
      rw [satisfiesCnf, evalCnf_clause_iff]
      intro E hE
      rcases List.mem_cons.mp hE with rfl | hE
      · rw [evalClause_literal_iff]
        refine ⟨(true, z), List.mem_cons_self, ?_⟩
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
        exact ((evalCnf_clause_iff a N).mp haN) E hE

end PvsNP.Units.m3_fresh_var_split

theorem PvsNP.Units.m3_fresh_var_split : ∀ (N : cnf) (C D : clause) (z : var), (∀ E ∈ (C ++ D) :: N, ∀ l ∈ E, l.2 ≠ z) →
    (SAT (((true, z) :: C) :: ((false, z) :: D) :: N) ↔ SAT ((C ++ D) :: N)) :=
  PvsNP.Units.m3_fresh_var_split.statement
