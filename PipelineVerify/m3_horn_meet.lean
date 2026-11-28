-- [desk-auto instantiate] batch 20261128-122658 · template tpl08（tpl08_sat_horn_meet.lean）
-- 题面与模板陈述逐字一致（空白规范化后比对），仅替换定理名；终验走私有 Actions 全量三行 import。
/-
模板 tpl08 — SAT 族：Horn 公式满足赋值的交闭包（meet）
来源：pvsnp-repo/PvsNP/Units/m3_horn_meet.lean（本队证明，与 drafts/m3_horn_meet_draft.lean 证明体一致）
编译状态：✅ 已结算文本。
填空点：① Horn 条件的陈述（这里 (C.filter (fun l => l.1)).length ≤ 1，按题面计数口径换）；
  ② 交集赋值的定义（这里 a.filter (· ∈ b)，evalVar 交 = && 的引理随之换）；
  ③ 唯一正文字的提取方式（filter 长度 ≤1 的 case 分析）。
引理链：lit_false_of_var_true / lit_false_of_var_false → hvar（交集 evalVar = &&）
  → hneg（负文字变量在 a、b 皆真）→ huniq（正文字唯一）→ hcontra 收尾。
-/
import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_horn_meet

/-- A negative literal whose variable is assigned `true` evaluates to `false`. -/
theorem lit_false_of_var_true (x : assgn) (l : literal) (hl1 : l.1 = false)
    (hx : evalVar x l.2 = true) : evalLiteral x l = false := by
  obtain ⟨s, v⟩ := l
  have hs : s = false := hl1
  subst hs
  show decide (evalVar x v = false) = false
  simp [hx]

/-- A positive literal whose variable is assigned `false` evaluates to `false`. -/
theorem lit_false_of_var_false (x : assgn) (l : literal) (hl1 : l.1 = true)
    (hx : evalVar x l.2 = false) : evalLiteral x l = false := by
  obtain ⟨s, v⟩ := l
  have hs : s = true := hl1
  subst hs
  show decide (evalVar x v = true) = false
  simp [hx]

theorem statement : ∀ (N : cnf) (a b : assgn),
    (∀ C ∈ N, (C.filter (fun l => l.1)).length ≤ 1) →
    satisfiesCnf a N → satisfiesCnf b N →
      satisfiesCnf (a.filter (fun v => decide (v ∈ b))) N := by
  intro N a b hhorn ha hb
  set m := a.filter (fun v => decide (v ∈ b)) with hm
  have hvar : ∀ v, evalVar m v = (evalVar a v && evalVar b v) := by
    intro v
    by_cases ha1 : v ∈ a <;> by_cases hb1 : v ∈ b <;>
      simp [evalVar, hm, List.mem_filter, ha1, hb1]
  show evalCnf m N = true
  rw [evalCnf_clause_iff]
  intro C hCN
  by_contra hC
  -- Every literal of C is false under m.
  have hall : ∀ l ∈ C, evalLiteral m l = false := by
    intro l hl
    cases hv : evalLiteral m l with
    | true =>
        exfalso
        apply hC
        rw [evalClause_literal_iff]
        exact ⟨l, hl, hv⟩
    | false => rfl
  -- Negative literals of C have their variable true in both a and b.
  have hneg : ∀ l ∈ C, l.1 = false → evalVar a l.2 = true ∧ evalVar b l.2 = true := by
    intro l hl hl1
    have hfl := hall l hl
    obtain ⟨s, v⟩ := l
    have hs : s = false := hl1
    subst hs
    have hmv : evalVar m v = true := by
      have h2 : decide (evalVar m v = false) = false := hfl
      cases hv : evalVar m v with
      | true => rfl
      | false => simp [hv] at h2
    rw [hvar] at hmv
    constructor
    · cases h : evalVar a v with
      | true => rfl
      | false => simp [h] at hmv
    · cases h : evalVar b v with
      | true => rfl
      | false => simp [h] at hmv
  -- A satisfying assignment cannot have all of C's literals false.
  have hcontra : ∀ (x : assgn), satisfiesCnf x N →
      (∀ l ∈ C, evalLiteral x l = false) → False := by
    intro x hx hfalse
    have hx' : evalCnf x N = true := hx
    rw [evalCnf_clause_iff] at hx'
    have hxC := hx' C hCN
    rw [evalClause_literal_iff] at hxC
    obtain ⟨l, hlC, hlev⟩ := hxC
    rw [hfalse l hlC] at hlev
    exact Bool.noConfusion hlev
  by_cases hpos : ∃ l ∈ C, l.1 = true
  · obtain ⟨p, hpC, hp1⟩ := hpos
    -- p is the unique positive literal of C.
    have huniq : ∀ l ∈ C, l.1 = true → l = p := by
      intro l hlC hl1
      have hpf : p ∈ C.filter (fun l => l.1) := List.mem_filter.mpr ⟨hpC, hp1⟩
      have hlf : l ∈ C.filter (fun l => l.1) := List.mem_filter.mpr ⟨hlC, hl1⟩
      have hlen := hhorn C hCN
      cases hfil : C.filter (fun l => l.1) with
      | nil => simp [hfil] at hpf
      | cons x t =>
          cases t with
          | nil =>
              have hpx : p = x := by simpa [hfil] using hpf
              have hlx : l = x := by simpa [hfil] using hlf
              rw [hlx, hpx]
          | cons y t =>
              rw [hfil] at hlen
              simp only [List.length_cons] at hlen
              omega
    -- p is false under m; so its variable fails in a or in b.
    have hpf := hall p hpC
    have hmv : evalVar m p.2 = false := by
      obtain ⟨s, v⟩ := p
      have hs : s = true := hp1
      subst hs
      have h2 : decide (evalVar m v = true) = false := hpf
      cases hv : evalVar m v with
      | true => simp [hv] at h2
      | false => rfl
    rw [hvar] at hmv
    by_cases hav : evalVar a p.2 = true
    · have hbv : evalVar b p.2 = false := by
        cases h : evalVar b p.2 with
        | true => simp [hav, h] at hmv
        | false => rfl
      apply hcontra b hb
      intro l hlC
      by_cases hl1 : l.1 = true
      · have hlp : l = p := huniq l hlC hl1
        rw [hlp]
        exact lit_false_of_var_false b p hp1 hbv
      · have hl1f : l.1 = false := by
          cases h : l.1 with
          | true => exact absurd h hl1
          | false => rfl
        exact lit_false_of_var_true b l hl1f (hneg l hlC hl1f).2
    · have havf : evalVar a p.2 = false := by
        cases h : evalVar a p.2 with
        | true => exact absurd h hav
        | false => rfl
      apply hcontra a ha
      intro l hlC
      by_cases hl1 : l.1 = true
      · have hlp : l = p := huniq l hlC hl1
        rw [hlp]
        exact lit_false_of_var_false a p hp1 havf
      · have hl1f : l.1 = false := by
          cases h : l.1 with
          | true => exact absurd h hl1
          | false => rfl
        exact lit_false_of_var_true a l hl1f (hneg l hlC hl1f).1
  · -- No positive literal: every literal is negative, all false under a.
    apply hcontra a ha
    intro l hlC
    have hl1f : l.1 = false := by
      by_contra hne
      exact hpos ⟨l, hlC, by
        cases h : l.1 with
        | true => rfl
        | false => exact absurd h hne⟩
    exact lit_false_of_var_true a l hl1f (hneg l hlC hl1f).1

end PvsNP.Units.m3_horn_meet

/-- Horn formulas are closed under pointwise intersection of satisfying assignments. -/
theorem PvsNP.Units.m3_horn_meet : ∀ (N : cnf) (a b : assgn), (∀ C ∈ N, (C.filter (fun l => l.1)).length ≤ 1) →
    satisfiesCnf a N → satisfiesCnf b N →
      satisfiesCnf (a.filter (fun v => decide (v ∈ b))) N :=
  PvsNP.Units.m3_horn_meet.statement
