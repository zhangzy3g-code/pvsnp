/-
模板 tpl05 — SAT 族：子句删除（subsumption：被包含的子句可删）
来源：pvsnp-repo/PvsNP/Units/m3_subsumption.lean（本队证明；与 drafts/m3_subsumption_check.lean 仅差 import 头一行）
编译状态：✅ 已结算文本。本轮最短模板之一（39 行），m3 波次高频题型。
填空点：① 包含假设的形式（这里 ∀ l ∈ C, l ∈ D，逐字面包含；变体见 tpl06）；
  ② 被删子句在 CNF 中的位置（这里紧跟 C 之后，按题面 cons 深度调整 mem 链）。
引理链：无辅助引理——evalCnf_clause_iff + evalClause_literal_iff 见证文字直传即完。
-/
import Mathlib
import PvsNP.Defs
import CookLevin

open CookLevin.Lang

/-- A clause subsumed by an earlier clause adds no constraint (vendored model):
any assignment satisfying `C` satisfies `D` through the same literal, and
dropping `D` keeps every satisfying assignment. -/
theorem PvsNP.Units.m3_subsumption : ∀ (N : cnf) (C D : clause), (∀ l ∈ C, l ∈ D) →
    (SAT (C :: D :: N) ↔ SAT (C :: N)) := by
  intro N C D hsub
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    show evalCnf a (C :: N) = true
    rw [evalCnf_clause_iff]
    intro E hE
    rcases List.mem_cons.mp hE with h | hE
    · rw [h]
      exact (evalCnf_clause_iff a _).mp ha C List.mem_cons_self
    · exact (evalCnf_clause_iff a _).mp ha E
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hE))
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    show evalCnf a (C :: D :: N) = true
    rw [evalCnf_clause_iff]
    intro E hE
    rcases List.mem_cons.mp hE with h | hE
    · rw [h]
      exact (evalCnf_clause_iff a _).mp ha C List.mem_cons_self
    rcases List.mem_cons.mp hE with h | hE
    · rw [h]
      have hC : evalClause a C = true :=
        (evalCnf_clause_iff a _).mp ha C List.mem_cons_self
      rw [evalClause_literal_iff] at hC ⊢
      obtain ⟨l, hlC, hl⟩ := hC
      exact ⟨l, hsub l hlC, hl⟩
    · exact (evalCnf_clause_iff a _).mp ha E (List.mem_cons_of_mem _ hE)
