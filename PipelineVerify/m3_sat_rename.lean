/-
模板 tpl02 — SAT 族：变量重命名下 SAT 不变（赋值双向传输）
来源：pvsnp-repo/PvsNP/Units/m3_sat_rename.lean（本队证明；与 drafts/m3_sat_rename_check.lean 仅差 import 头一行）
编译状态：✅ 已结算文本——即平台全量内核校验通过的版本。
填空点：① 重命名在文字上的作用式（这里 C.map (fun l => (l.1, f l.2))，按题面换）；
  ② 单射性假设的来源；③ pullback 的过滤谓词（这里 filter 到 varsOfCnf N 且 f v ∈ a'）。
引理链：evalVar_map_apply → evalLiteral_map → evalClause_map（正向）；
  pullback + evalVar_pullback + evalClause_pullback（反向）；主定理双向组装。
套用：namespace 与最终定理名换成新 unit key，题面逐字以放题快照为准。
-/
import Mathlib
import PvsNP.Defs
import CookLevin

open CookLevin.Lang

namespace PvsNP.Units.m3_sat_rename

variable {f : var → var}

/-- Evaluating the `f`-image of an assignment at a renamed variable is the same
as evaluating the original assignment there; injectivity is what makes the
membership test match. -/
theorem evalVar_map_apply (hf : Function.Injective f) (a : assgn) (v : var) :
    evalVar (a.map f) (f v) = evalVar a v := by
  unfold evalVar
  congr 1
  apply propext
  rw [List.mem_map]
  constructor
  · rintro ⟨u, hu, hfu⟩
    have huv : u = v := hf hfu
    exact huv ▸ hu
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- A literal keeps its value when both it and the assignment are renamed. -/
theorem evalLiteral_map (hf : Function.Injective f) (a : assgn) (l : literal) :
    evalLiteral (a.map f) (l.1, f l.2) = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  exact congrArg (fun w => decide (w = s)) (evalVar_map_apply hf a v)

/-- A clause keeps its value when both it and the assignment are renamed. -/
theorem evalClause_map (hf : Function.Injective f) (a : assgn) (C : clause) :
    evalClause (a.map f) (C.map (fun l => (l.1, f l.2))) = evalClause a C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      show (evalLiteral (a.map f) (l.1, f l.2) ||
              evalClause (a.map f) (C.map (fun l => (l.1, f l.2)))) =
            (evalLiteral a l || evalClause a C)
      rw [ih, evalLiteral_map hf a l]

/-- The assignment extracted from `a'` by pulling back along `f`, restricted to
the variables of `N`. -/
def pullback (f : var → var) (N : cnf) (a' : assgn) : assgn :=
  (SAT_inNP.varsOfCnf N).filter (fun v => f v ∈ a')

theorem evalVar_pullback {N : cnf} {a' : assgn} {v : var}
    (hv : v ∈ SAT_inNP.varsOfCnf N) :
    evalVar (pullback f N a') v = evalVar a' (f v) := by
  by_cases h : f v ∈ a' <;> simp [evalVar, pullback, List.mem_filter, hv, h]

/-- A clause whose variables all occur in `N` keeps its value when read under
the pulled-back assignment instead of under the renamed assignment `a'`. -/
theorem evalClause_pullback {N : cnf} (a' : assgn) {C : clause}
    (hC : ∀ l ∈ C, l.2 ∈ SAT_inNP.varsOfCnf N) :
    evalClause a' (C.map (fun l => (l.1, f l.2))) = evalClause (pullback f N a') C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      have hl : l.2 ∈ SAT_inNP.varsOfCnf N := hC l List.mem_cons_self
      have ih' := ih (fun l' hl' => hC l' (List.mem_cons_of_mem l hl'))
      have hlit : evalLiteral a' (l.1, f l.2) = evalLiteral (pullback f N a') l := by
        obtain ⟨s, v⟩ := l
        exact congrArg (fun w => decide (w = s)) (evalVar_pullback hl).symm
      show (evalLiteral a' (l.1, f l.2) ||
              evalClause a' (C.map (fun l => (l.1, f l.2)))) =
            (evalLiteral (pullback f N a') l || evalClause (pullback f N a') C)
      rw [ih', hlit]

end PvsNP.Units.m3_sat_rename

/-- Renaming variables injectively preserves satisfiability (vendored model):
transport a satisfying assignment along the renaming in both directions —
backwards by mapping it with `f`, forwards by pulling it back to the variables
that occur in the formula. -/
theorem PvsNP.Units.m3_sat_rename : ∀ (N : cnf) (f : var → var), Function.Injective f →
    (SAT (N.map (fun C => C.map (fun l => (l.1, f l.2)))) ↔ SAT N) := by
  intro N f hf
  constructor
  · rintro ⟨a', ha'⟩
    refine ⟨PvsNP.Units.m3_sat_rename.pullback f N a', ?_⟩
    show evalCnf (PvsNP.Units.m3_sat_rename.pullback f N a') N = true
    rw [evalCnf_clause_iff]
    intro C hC
    have hC' : evalClause a' (C.map (fun l => (l.1, f l.2))) = true :=
      (evalCnf_clause_iff a' _).mp ha' _
        (List.mem_map.mpr ⟨C, hC, rfl⟩)
    rwa [PvsNP.Units.m3_sat_rename.evalClause_pullback a'
      (fun l hl => SAT_inNP.varsOfCnf_mem N C l hC hl)] at hC'
  · rintro ⟨a, ha⟩
    refine ⟨a.map f, ?_⟩
    show evalCnf (a.map f) (N.map (fun C => C.map (fun l => (l.1, f l.2)))) = true
    rw [evalCnf_clause_iff]
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
    rw [PvsNP.Units.m3_sat_rename.evalClause_map hf]
    exact (evalCnf_clause_iff a N).mp ha C₀ hC₀
