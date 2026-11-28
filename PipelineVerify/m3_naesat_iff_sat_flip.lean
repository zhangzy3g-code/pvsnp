-- [desk-auto instantiate] batch 20261128-122658 · template tpl09（tpl09_sat_nae_flip.lean）
-- 题面与模板陈述逐字一致（空白规范化后比对），仅替换定理名；终验走私有 Actions 全量三行 import。
/-
模板 tpl09 — SAT 族：NAE-SAT 与「公式 ∪ 逐字面取反公式」的等价
来源：pvsnp-repo/PvsNP/Units/m3_naesat_iff_sat_flip.lean（本队证明，与 drafts/m3_naesat_iff_sat_flip_draft.lean 证明体一致）
编译状态：✅ 已结算文本。
填空点：① 翻转映射（这里 fun l => (!l.1, l.2)，按题换成其他文字变换）；
  ② 目标公式的拼接形状（这里 N ++ N.map …）；③ NAE 条件的 any/any 陈述式。
引理链：evalLiteral_neg（取反翻转字面值，靠 decide 穷举）→ evalClause_map_neg → 主定理双向。
-/
import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_naesat_iff_sat_flip

/-- Negating a literal negates its value. -/
theorem evalLiteral_neg (a : assgn) (l : literal) :
    evalLiteral a (!l.1, l.2) = !evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have key : ∀ b t : Bool, decide (b = !t) = !decide (b = t) := by decide
  exact key _ _

/-- Evaluating the literal-wise negated clause is the "has a false literal"
test of the original. -/
theorem evalClause_map_neg (a : assgn) (C : clause) :
    evalClause a (C.map (fun l => (!l.1, l.2)))
      = C.any (fun l => !evalLiteral a l) := by
  unfold evalClause
  rw [List.any_map]
  congr 1
  funext l
  exact evalLiteral_neg a l

theorem statement : ∀ N : cnf,
    (∃ a : assgn, ∀ C ∈ N, C.any (evalLiteral a) = true
        ∧ C.any (fun l => !evalLiteral a l) = true)
      ↔ SAT (N ++ N.map (fun C => C.map (fun l => (!l.1, l.2)))) := by
  intro N
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    show evalCnf a (N ++ N.map (fun C => C.map (fun l => (!l.1, l.2)))) = true
    rw [evalCnf_clause_iff]
    intro E hE
    rw [List.mem_append] at hE
    rcases hE with hE | hE
    · exact (ha E hE).1
    · rw [List.mem_map] at hE
      obtain ⟨C, hCN, rfl⟩ := hE
      rw [evalClause_map_neg]
      exact (ha C hCN).2
  · rintro ⟨a, ha⟩
    have ha' : evalCnf a (N ++ N.map (fun C => C.map (fun l => (!l.1, l.2)))) = true := ha
    rw [evalCnf_clause_iff] at ha'
    refine ⟨a, fun C hCN => ⟨?_, ?_⟩⟩
    · exact ha' C (List.mem_append_left _ hCN)
    · have h2 := ha' (C.map (fun l => (!l.1, l.2)))
        (List.mem_append_right _ (List.mem_map.mpr ⟨C, hCN, rfl⟩))
      rwa [evalClause_map_neg] at h2

end PvsNP.Units.m3_naesat_iff_sat_flip

/-- NAE-satisfiability of N is satisfiability of N together with its literal-wise negation. -/
theorem PvsNP.Units.m3_naesat_iff_sat_flip : ∀ N : cnf,
    (∃ a : assgn, ∀ C ∈ N, C.any (evalLiteral a) = true
        ∧ C.any (fun l => !evalLiteral a l) = true)
      ↔ SAT (N ++ N.map (fun C => C.map (fun l => (!l.1, l.2)))) :=
  PvsNP.Units.m3_naesat_iff_sat_flip.statement
