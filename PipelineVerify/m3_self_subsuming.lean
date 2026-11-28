-- [desk-auto instantiate] batch 20261128-122658 · template tpl06（tpl06_sat_self_subsuming.lean）
-- 题面与模板陈述逐字一致（空白规范化后比对），仅替换定理名；终验走私有 Actions 全量三行 import。
/-
模板 tpl06 — SAT 族：自消解删除（self-subsuming：(¬v::D) 在 (v::C) 与 C⊆D 下可缩）
来源：pvsnp-repo/PvsNP/Units/m3_self_subsuming.lean（本队证明，与 drafts/m3_self_subsuming_draft.lean 证明体一致）
编译状态：✅ 已结算文本。
填空点：① 两个相关子句的形状（这里 (true,v)::C 与 (false,v)::D）；
  ② 保留哪一侧（这里删 (false,v) 头保留 D）；③ 对 evalVar a v 的真假分工。
引理链：无辅助引理——evalCnf_clause_iff 逐子句 + 对 v 的 by_cases + tpl05 式见证传输。
-/
import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_self_subsuming

theorem statement : ∀ (N : cnf) (C D : clause) (v : var), (∀ l ∈ C, l ∈ D) →
    (SAT (((true, v) :: C) :: ((false, v) :: D) :: N)
      ↔ SAT (((true, v) :: C) :: D :: N)) := by
  intro N C D v hsub
  constructor
  · rintro ⟨a, ha⟩
    have ha' : evalCnf a (((true, v) :: C) :: ((false, v) :: D) :: N) = true := ha
    rw [evalCnf_clause_iff] at ha'
    have hTC := ha' _ List.mem_cons_self
    have hFD := ha' _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hN : ∀ E ∈ N, evalClause a E = true :=
      fun E hE => ha' E (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hE))
    have hD : evalClause a D = true := by
      by_cases hv : evalVar a v = true
      · rw [evalClause_literal_iff] at hFD ⊢
        obtain ⟨l, hl, hlev⟩ := hFD
        rcases List.mem_cons.mp hl with h | h
        · rw [h] at hlev
          have hcontra : evalVar a v = false := of_decide_eq_true hlev
          rw [hv] at hcontra
          exact Bool.noConfusion hcontra
        · exact ⟨l, h, hlev⟩
      · have hvf : evalVar a v = false := by
          cases h : evalVar a v with
          | true => exact absurd h hv
          | false => rfl
        rw [evalClause_literal_iff] at hTC ⊢
        obtain ⟨m, hm, hmev⟩ := hTC
        rcases List.mem_cons.mp hm with h | h
        · rw [h] at hmev
          have hcontra : evalVar a v = true := of_decide_eq_true hmev
          rw [hvf] at hcontra
          exact Bool.noConfusion hcontra
        · exact ⟨m, hsub m h, hmev⟩
    refine ⟨a, ?_⟩
    show evalCnf a (((true, v) :: C) :: D :: N) = true
    rw [evalCnf_clause_iff]
    intro E hE
    rcases List.mem_cons.mp hE with h | hE
    · rw [h]; exact hTC
    · rcases List.mem_cons.mp hE with h | hE
      · rw [h]; exact hD
      · exact hN E hE
  · rintro ⟨a, ha⟩
    have ha' : evalCnf a (((true, v) :: C) :: D :: N) = true := ha
    rw [evalCnf_clause_iff] at ha'
    have hTC := ha' _ List.mem_cons_self
    have hD := ha' _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hN : ∀ E ∈ N, evalClause a E = true :=
      fun E hE => ha' E (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hE))
    have hFD : evalClause a ((false, v) :: D) = true := by
      by_cases hv : evalVar a v = true
      · rw [evalClause_literal_iff] at hD ⊢
        obtain ⟨l, hl, hlev⟩ := hD
        exact ⟨l, List.mem_cons_of_mem _ hl, hlev⟩
      · have hvf : evalVar a v = false := by
          cases h : evalVar a v with
          | true => exact absurd h hv
          | false => rfl
        rw [evalClause_literal_iff]
        refine ⟨(false, v), List.mem_cons_self, ?_⟩
        show decide (evalVar a v = false) = true
        rw [hvf]
        rfl
    refine ⟨a, ?_⟩
    show evalCnf a (((true, v) :: C) :: ((false, v) :: D) :: N) = true
    rw [evalCnf_clause_iff]
    intro E hE
    rcases List.mem_cons.mp hE with h | hE
    · rw [h]; exact hTC
    · rcases List.mem_cons.mp hE with h | hE
      · rw [h]; exact hFD
      · exact hN E hE

end PvsNP.Units.m3_self_subsuming

/-- Self-subsuming resolution step: with C ⊆ D, the clause (false, v) :: D is redundant next to (true, v) :: C. -/
theorem PvsNP.Units.m3_self_subsuming : ∀ (N : cnf) (C D : clause) (v : var), (∀ l ∈ C, l ∈ D) →
    (SAT (((true, v) :: C) :: ((false, v) :: D) :: N)
      ↔ SAT (((true, v) :: C) :: D :: N)) :=
  PvsNP.Units.m3_self_subsuming.statement
