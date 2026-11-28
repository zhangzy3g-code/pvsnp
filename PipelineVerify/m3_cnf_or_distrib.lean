-- [desk-auto instantiate] batch 20261128-122658 · template tpl10（tpl10_sat_cnf_distrib.lean）
-- 题面与模板陈述逐字一致（空白规范化后比对），仅替换定理名；终验走私有 Actions 全量三行 import。
/-
模板 tpl10 — SAT 族：CNF 层分配律（evalCnf 的 flatMap 分配恒等式）
来源：pvsnp-repo/PvsNP/Units/m3_cnf_or_distrib.lean（本队证明，与 drafts/m3_cnf_or_distrib_draft.lean 证明体一致）
编译状态：✅ 已结算文本。
填空点：① 分配构造（这里 N₁.flatMap (fun C => N₂.map (fun D => C ++ D))，按题换 map/filter 组合）；
  ② 逻辑核：∀C∀D, P C ∨ Q D ↔ (∀C, P C) ∨ (∀D, Q D) 的 by_cases 证法可整体复用。
引理链：evalClause_append（子句拼接求值 = ||）→ hflat（flatMap 成员资格桥）→ key（分配律）→ 三处 evalCnf_clause_iff 收尾。
-/
import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_cnf_or_distrib

theorem evalClause_append (a : assgn) (C D : clause) :
    evalClause a (C ++ D) = (evalClause a C || evalClause a D) := by
  unfold evalClause
  rw [List.any_append]

theorem statement : ∀ (a : assgn) (N₁ N₂ : cnf),
    evalCnf a (N₁.flatMap (fun C => N₂.map (fun D => C ++ D)))
      = (evalCnf a N₁ || evalCnf a N₂) := by
  intro a N₁ N₂
  have hflat : (∀ C ∈ N₁, ∀ D ∈ N₂, evalClause a (C ++ D) = true)
      ↔ ∀ E ∈ N₁.flatMap (fun C => N₂.map (fun D => C ++ D)),
        evalClause a E = true := by
    constructor
    · intro h E hE
      rw [List.mem_flatMap] at hE
      obtain ⟨C, hCN, hCE⟩ := hE
      rw [List.mem_map] at hCE
      obtain ⟨D, hDN, hDE⟩ := hCE
      rw [← hDE]
      exact h C hCN D hDN
    · intro h C hCN D hDN
      exact h _ (List.mem_flatMap.mpr ⟨C, hCN, List.mem_map.mpr ⟨D, hDN, rfl⟩⟩)
  have key : (∀ C ∈ N₁, ∀ D ∈ N₂, evalClause a (C ++ D) = true)
      ↔ (∀ C ∈ N₁, evalClause a C = true) ∨ (∀ D ∈ N₂, evalClause a D = true) := by
    constructor
    · intro h
      by_cases hN₁ : ∀ C ∈ N₁, evalClause a C = true
      · exact Or.inl hN₁
      · right
        obtain ⟨C₀, hC₀N, hC₀⟩ : ∃ C ∈ N₁, ¬ evalClause a C = true := by
          by_contra hc
          push_neg at hc
          exact hN₁ hc
        intro D hDN
        have hCD := h C₀ hC₀N D hDN
        rw [evalClause_append] at hCD
        have hC₀f : evalClause a C₀ = false := by
          cases hv : evalClause a C₀ with
          | true => exact absurd hv hC₀
          | false => rfl
        rw [hC₀f, Bool.false_or] at hCD
        exact hCD
    · rintro (h1 | h2) C hCN D hDN
      · rw [evalClause_append, h1 C hCN, Bool.true_or]
      · rw [evalClause_append, h2 D hDN, Bool.or_true]
  rw [Bool.eq_iff_iff, Bool.or_eq_true_iff]
  rw [evalCnf_clause_iff, evalCnf_clause_iff, evalCnf_clause_iff]
  exact hflat.symm.trans key

end PvsNP.Units.m3_cnf_or_distrib

/-- Evaluation distributes over the clause-wise disjunction of two CNFs. -/
theorem PvsNP.Units.m3_cnf_or_distrib : ∀ (a : assgn) (N₁ N₂ : cnf),
    evalCnf a (N₁.flatMap (fun C => N₂.map (fun D => C ++ D)))
      = (evalCnf a N₁ || evalCnf a N₂) :=
  PvsNP.Units.m3_cnf_or_distrib.statement
