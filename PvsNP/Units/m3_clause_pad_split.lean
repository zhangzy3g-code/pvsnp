/-
模板 tpl04 — SAT 族：子句双边填充一对互补文字后可拆回（子句手术）
来源：pvsnp-repo/PvsNP/Units/m3_clause_pad_split.lean（本队证明，与 drafts/m3_clause_pad_split_draft.lean 证明体一致）
编译状态：✅ 已结算文本；且本队 PR #14 提交的正是这份证明——本地编译＋服务端 lint 均通过（败于席位竞速，非证明问题）。
填空点：① 填充文字对（(true,z)/(false,z)）与追加位置（这里 C ++ [l] 尾加，cons 头加见 tpl03）；
  ② evalClause_append_singleton 的求值展开式按子句形状换。
引理链：evalClause_append_singleton → evalCnf_clause_iff 逐子句 case → 互补文字同真矛盾收尾。
-/
import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_clause_pad_split

/-- Appending one literal to a clause: the evaluation is the old one, or the
new literal's. -/
theorem evalClause_append_singleton (a : assgn) (C : clause) (l : literal) :
    evalClause a (C ++ [l]) = (evalClause a C || evalLiteral a l) := by
  unfold evalClause
  rw [List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem statement : ∀ (N : cnf) (C : clause) (z : var),
    SAT ((C ++ [(true, z)]) :: (C ++ [(false, z)]) :: N) ↔ SAT (C :: N) := by
  intro N C z
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    show evalCnf a (C :: N) = true
    have ha' : evalCnf a ((C ++ [(true, z)]) :: (C ++ [(false, z)]) :: N) = true := ha
    rw [evalCnf_clause_iff] at ha'
    rw [evalCnf_clause_iff]
    have ha := ha'
    have h1 := ha _ List.mem_cons_self
    have h2 := ha _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hN : ∀ E ∈ N, evalClause a E = true :=
      fun E hE => ha E (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hE))
    intro E hE
    rcases List.mem_cons.mp hE with h | hE
    · rw [h]
      rw [evalClause_append_singleton] at h1 h2
      rcases (Bool.or_eq_true_iff.mp h1) with hC | ht
      · exact hC
      · rcases (Bool.or_eq_true_iff.mp h2) with hC | hf
        · exact hC
        · exfalso
          have hzt : evalVar a z = true := of_decide_eq_true ht
          have hzf : evalVar a z = false := of_decide_eq_true hf
          rw [hzt] at hzf
          exact Bool.noConfusion hzf
    · exact hN E hE
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    show evalCnf a ((C ++ [(true, z)]) :: (C ++ [(false, z)]) :: N) = true
    have ha' : evalCnf a (C :: N) = true := ha
    rw [evalCnf_clause_iff] at ha'
    rw [evalCnf_clause_iff]
    have ha := ha'
    intro E hE
    rcases List.mem_cons.mp hE with h | hE
    · rw [h, evalClause_append_singleton]
      have hC := ha C List.mem_cons_self
      simp [hC]
    · rcases List.mem_cons.mp hE with h | hE
      · rw [h, evalClause_append_singleton]
        have hC := ha C List.mem_cons_self
        simp [hC]
      · exact ha E (List.mem_cons_of_mem _ hE)

end PvsNP.Units.m3_clause_pad_split

/-- Splitting a clause on a fresh padding literal (both signs) preserves satisfiability. -/
theorem PvsNP.Units.m3_clause_pad_split : ∀ (N : cnf) (C : clause) (z : var),
    SAT ((C ++ [(true, z)]) :: (C ++ [(false, z)]) :: N) ↔ SAT (C :: N) :=
  PvsNP.Units.m3_clause_pad_split.statement
