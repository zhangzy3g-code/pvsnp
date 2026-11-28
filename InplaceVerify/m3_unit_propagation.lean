-- [desk-auto instantiate] batch 20261128-122658 · template tpl07（tpl07_sat_unit_propagation.lean）
-- 题面与模板陈述逐字一致（空白规范化后比对），仅替换定理名；终验走私有 Actions 全量三行 import。
/-
模板 tpl07 — SAT 族：单位传播等价（unit propagation）
来源：pvsnp-repo/PvsNP/Units/m3_unit_propagation.lean（本队证明；与 drafts/m3_unit_propagation_check.lean 仅差 import 头一行）
编译状态：✅ 已结算文本。
填空点：① propagated 变换的定义（删含 l 的子句、其余子句删 ¬l，按题面 filter/map 式换）；
  ② forceLit 的构造（按 l.1 决定 cons 还是 filter 掉 l.2）；
  ③ 目标命题里变换的书写形式必须与 propagated 展开后逐字一致。
引理链：evalLiteral_negLit → evalVar_forceLit_self / of_ne → evalLiteral_forceLit
  → sat_propagated_of_sat（正向）/ sat_of_sat_propagated（反向）。
-/
import Mathlib
import PvsNP.Defs
import CookLevin

open CookLevin.Lang

namespace PvsNP.Units.m3_unit_propagation

/-- The literal opposite to `l`. -/
abbrev negLit (l : literal) : literal := (!l.1, l.2)

/-- The propagated form of `N` under the unit literal `l`. -/
def propagated (l : literal) (N : cnf) : cnf :=
  (N.filter (fun C => decide (l ∉ C))).map
    (fun C => C.filter (fun m => decide (m ≠ negLit l)))

/-- If `evalLiteral a l = true` then the opposite literal evaluates to `false`. -/
theorem evalLiteral_negLit {a : assgn} {l : literal}
    (h : evalLiteral a l = true) : evalLiteral a (negLit l) = false := by
  obtain ⟨s, v⟩ := l
  have h1 : evalVar a v = s := of_decide_eq_true h
  show decide (evalVar a v = !s) = false
  rw [h1]
  cases s <;> rfl

/-- The assignment obtained from `a` by forcing the literal `l` to be true:
keep `l.2` in the assignment iff `l.1` says so, and remove it otherwise. -/
def forceLit (l : literal) (a : assgn) : assgn :=
  if l.1 then l.2 :: a.filter (fun v => v ≠ l.2) else a.filter (fun v => v ≠ l.2)

theorem evalVar_forceLit_self (l : literal) (a : assgn) :
    evalVar (forceLit l a) l.2 = l.1 := by
  obtain ⟨s, v⟩ := l
  by_cases hs : s = true
  · simp [forceLit, hs, evalVar]
  · have hs' : s = false := by simpa using hs
    simp [forceLit, hs', evalVar]

theorem evalVar_forceLit_of_ne {l : literal} {a : assgn} {v : var} (hv : v ≠ l.2) :
    evalVar (forceLit l a) v = evalVar a v := by
  obtain ⟨s, w⟩ := l
  by_cases hs : s = true
  · simp [forceLit, hs, evalVar, List.mem_filter, hv]
  · have hs' : s = false := by simpa using hs
    simp [forceLit, hs', evalVar, List.mem_filter, hv]

theorem evalLiteral_forceLit (l : literal) (a : assgn) :
    evalLiteral (forceLit l a) l = true := by
  obtain ⟨s, v⟩ := l
  show decide (evalVar (forceLit (s, v) a) v = s) = true
  rw [evalVar_forceLit_self]
  simp

/-- Forwards: a satisfying assignment of `[l] :: N` satisfies the propagated
formula. -/
theorem sat_propagated_of_sat {N : cnf} {l : literal} {a : assgn}
    (ha : satisfiesCnf a ([l] :: N)) : satisfiesCnf a (propagated l N) := by
  have hunit : evalClause a [l] = true :=
    (evalCnf_clause_iff a _).mp ha [l] List.mem_cons_self
  have hl : evalLiteral a l = true := by
    have := hunit
    unfold evalClause at this
    simpa using this
  show evalCnf a (propagated l N) = true
  rw [evalCnf_clause_iff]
  intro E hE
  unfold propagated at hE
  rw [List.mem_map] at hE
  obtain ⟨C, hC, rfl⟩ := hE
  rw [List.mem_filter] at hC
  obtain ⟨hCN, hlC⟩ := hC
  have hsatC : evalClause a C = true :=
    (evalCnf_clause_iff a _).mp ha C (List.mem_cons_of_mem _ hCN)
  rw [evalClause_literal_iff] at hsatC ⊢
  obtain ⟨m, hmC, hm⟩ := hsatC
  have hmne : m ≠ negLit l := by
    intro hmeq
    rw [hmeq, evalLiteral_negLit hl] at hm
    exact Bool.false_ne_true hm
  exact ⟨m, List.mem_filter.mpr ⟨hmC, by simpa using hmne⟩, hm⟩

/-- Backwards: a satisfying assignment of the propagated formula extends to
one of `[l] :: N` by forcing `l`. -/
theorem sat_of_sat_propagated {N : cnf} {l : literal} {a : assgn}
    (ha : satisfiesCnf a (propagated l N)) : satisfiesCnf (forceLit l a) ([l] :: N) := by
  show evalCnf (forceLit l a) ([l] :: N) = true
  rw [evalCnf_clause_iff]
  intro E hE
  rcases List.mem_cons.mp hE with h | hE
  · rw [h]
    show evalClause (forceLit l a) [l] = true
    unfold evalClause
    simpa using evalLiteral_forceLit l a
  · by_cases hlE : l ∈ E
    · rw [evalClause_literal_iff]
      exact ⟨l, hlE, evalLiteral_forceLit l a⟩
    · have hsatE : evalClause a (E.filter (fun m => decide (m ≠ negLit l))) = true := by
        have hmem : E.filter (fun m => decide (m ≠ negLit l)) ∈ propagated l N := by
          unfold propagated
          rw [List.mem_map]
          exact ⟨E, List.mem_filter.mpr ⟨hE, by simpa using hlE⟩, rfl⟩
        exact (evalCnf_clause_iff a _).mp ha _ hmem
      rw [evalClause_literal_iff] at hsatE ⊢
      obtain ⟨m, hm, hmev⟩ := hsatE
      rw [List.mem_filter] at hm
      obtain ⟨hmE, hmne⟩ := hm
      refine ⟨m, hmE, ?_⟩
      by_cases hvar : m.2 = l.2
      · -- m is on l's variable and differs from the opposite literal, so m = l
        have hml : m = (l.1, l.2) := by
          have hne : m ≠ negLit l := by simpa using hmne
          obtain ⟨sm, vm⟩ := m
          obtain ⟨sl, vl⟩ := l
          have hvar' : vm = vl := hvar
          have hsm : sm = sl := by
            by_contra hcon
            apply hne
            have hsm2 : sm = !sl := by cases sl <;> cases sm <;> simp_all
            rw [hsm2, hvar']
          rw [Prod.ext_iff]
          exact ⟨hsm, hvar'⟩
        rw [hml]
        exact evalLiteral_forceLit l a
      · obtain ⟨sm, vm⟩ := m
        have hcongr : evalVar (forceLit l a) vm = evalVar a vm :=
          evalVar_forceLit_of_ne hvar
        have h2 : decide (evalVar a vm = sm) = true := hmev
        show decide (evalVar (forceLit l a) vm = sm) = true
        rw [hcongr]
        exact h2

theorem statement : ∀ (N : cnf) (l : literal),
    SAT ([l] :: N) ↔
      SAT ((N.filter (fun C => decide (l ∉ C))).map
        (fun C => C.filter (fun m => decide (m ≠ (!l.1, l.2))))) := by
  intro N l
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, sat_propagated_of_sat ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨forceLit l a, sat_of_sat_propagated ha⟩

end PvsNP.Units.m3_unit_propagation

/-- Unit propagation on a unit clause preserves satisfiability (vendored
model): clauses containing the unit literal drop out, and the opposite literal
is deleted from the remaining clauses. -/
theorem PvsNP.Units.m3_unit_propagation : ∀ (N : cnf) (l : literal),
    SAT ([l] :: N) ↔
      SAT ((N.filter (fun C => decide (l ∉ C))).map
        (fun C => C.filter (fun m => decide (m ≠ (!l.1, l.2))))) :=
  PvsNP.Units.m3_unit_propagation.statement
