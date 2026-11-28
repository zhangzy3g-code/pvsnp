-- [desk-auto instantiate] batch 20261128-122658 · template tpl11（tpl11_sat_counting_falsifiers.lean）
-- 题面与模板陈述逐字一致（空白规范化后比对），仅替换定理名；终验走私有 Actions 全量三行 import。
/-
模板 tpl11 — SAT 计数族：子句 falsifying assignments 的精确计数 2^(n-k)
来源：drafts/m3_clause_falsifiers_count_draft.lean（本队证明，与 pvsnp-repo 已结算文件逐字节一致）
编译状态：◐ 正文与已结算文件逐字节一致；该 unit 结算记分归属未核实（同期战报记为被他人抢走），不得标「本队已结算」（2026-11-27 dot 评审纠正）。注意本文件 import 全量 Mathlib，编译比精确 import 慢。
填空点：① 计数对象与计数域（这里 (range n).sublists.filter (fun a => !evalClause a C)，按题换 filter 谓词）；
  ② 指数式（2 ^ (n - C.length)，按题换）；③ Nodup/变量界假设的陈述（(C.map Prod.snd).Nodup、∀ l ∈ C, l.2 < n）。
引理链：nodup_length_le_of_lt → evalClause_eq_false_iff / evalClause_congr → falsifies_erase_split
  → count_falsifiers_range（对 n 归纳，分「n 出现/不出现」两支）。
-/
import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_clause_falsifiers_count

/-- A `Nodup` list of naturals, all `< m`, has length at most `m`. -/
theorem nodup_length_le_of_lt : ∀ {l : List ℕ} {m : ℕ}, l.Nodup →
    (∀ x ∈ l, x < m) → l.length ≤ m := by
  intro l m h hs
  induction m generalizing l with
  | zero =>
    cases l with
    | nil => simp
    | cons x xs =>
      exfalso
      exact Nat.not_lt_zero _ (hs x (List.mem_cons_self _ _))
  | succ m ih =>
    have herase : (l.erase m).Nodup := List.Nodup.sublist List.erase_sublist h
    have hsub : ∀ x ∈ l.erase m, x < m := by
      intro x hx
      have hxmem : x ∈ l := List.mem_of_mem_erase hx
      have hlt := hs x hxmem
      have hne : x ≠ m := (List.Nodup.mem_erase_iff h).mp hx |>.1
      omega
    have ih' := ih herase hsub
    have hlen : l.length ≤ (l.erase m).length + 1 := by
      rw [List.length_erase]
      split
      · have hpos : 0 < l.length := List.length_pos_of_mem ‹m ∈ l›
        omega
      · omega
    omega

/-- A clause is false iff every literal in it evaluates to `false`. -/
theorem evalClause_eq_false_iff (a : assgn) (C : clause) :
    evalClause a C = false ↔ ∀ l ∈ C, evalLiteral a l = false := by
  simp [evalClause]

/-- Appending one literal to a clause: the evaluation is the old one, or the
new literal's. -/
theorem evalClause_cons (a : assgn) (l : literal) (C : clause) :
    evalClause a (l :: C) = (evalLiteral a l || evalClause a C) := by
  simp [evalClause]

/-- `evalClause` only depends on the membership of the clause's variables. -/
theorem evalClause_congr {a b : assgn} {C : clause}
    (h : ∀ v ∈ C.map Prod.snd, (v ∈ a) ↔ (v ∈ b)) :
    evalClause a C = evalClause b C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    have hC : ∀ v ∈ C.map Prod.snd, (v ∈ a) ↔ (v ∈ b) := by
      intro v hv
      exact h v (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hv)
    have hl : evalLiteral a l = evalLiteral b l := by
      obtain ⟨s, v⟩ := l
      have hv : (v ∈ a) ↔ (v ∈ b) :=
        h v (by rw [List.map_cons]; exact List.mem_cons_self _ _)
      simp only [evalLiteral, evalVar]
      rw [show decide (v ∈ a) = decide (v ∈ b) from by simp [hv]]
    rw [evalClause_cons, evalClause_cons, hl, ih hC]

/-- Falsifying a clause splits over erasing one of its literals. -/
theorem falsifies_erase_split (a : assgn) (C : clause) (l₀ : literal)
    (hCnodup : C.Nodup) (hl₀ : l₀ ∈ C) :
    (∀ l ∈ C, evalLiteral a l = false) ↔
      (evalLiteral a l₀ = false ∧ ∀ l ∈ C.erase l₀, evalLiteral a l = false) := by
  constructor
  · intro h
    exact ⟨h _ hl₀, fun l hl => h l (List.mem_of_mem_erase hl)⟩
  · rintro ⟨h0, h'⟩ l hl
    by_cases heq : l = l₀
    · rw [heq]; exact h0
    · exact h' l ((List.Nodup.mem_erase_iff hCnodup).mpr ⟨heq, hl⟩)

/-- The counting lemma, by induction on the size `n` of the variable universe:
a clause on `k` distinct variables (all `< n`) is false under exactly
`2 ^ (n - k)` of the assignments to `n` variables. -/
theorem count_falsifiers_range : ∀ (n : ℕ) (C : clause),
    (C.map Prod.snd).Nodup → (∀ l ∈ C, l.2 < n) →
    ((List.range n).sublists.filter (fun a => !evalClause a C)).length
      = 2 ^ (n - C.length) := by
  intro n
  induction n with
  | zero =>
    intro C hC hsub
    have hC0 : C = [] := by
      cases C with
      | nil => rfl
      | cons l C' =>
        exfalso
        exact Nat.not_lt_zero _ (hsub l (List.mem_cons_self _ _))
    subst hC0
    simp
  | succ n ih =>
    intro C hC hsub
    rw [List.range_succ, List.sublists_concat, List.filter_append, List.length_append,
      List.filter_map, List.length_map]
    by_cases hn : n ∈ C.map Prod.snd
    · -- `n` occurs in `C`: exactly one of the two extensions of each falsifier
      -- of the erased clause falsifies `C`.
      obtain ⟨l₀, hl₀C, hl₀2⟩ := List.mem_map.mp hn
      obtain ⟨s, v⟩ := l₀
      have hv : v = n := hl₀2
      subst hv
      have hCnodup : C.Nodup := List.Nodup.of_map Prod.snd hC
      have hinj : ∀ x ∈ C, ∀ y ∈ C, x.2 = y.2 → x = y :=
        (List.nodup_map_iff_inj_on hCnodup).mp hC
      have hC'len : (C.erase (s, n)).length = C.length - 1 :=
        List.length_erase_of_mem hl₀C
      have hC'nodup : ((C.erase (s, n)).map Prod.snd).Nodup :=
        List.Nodup.sublist (List.Sublist.map Prod.snd List.erase_sublist) hC
      have hC'sub : ∀ l ∈ C.erase (s, n), l.2 < n := by
        intro l hl
        have hlC : l ∈ C := List.mem_of_mem_erase hl
        have hlt := hsub l hlC
        have hne : l.2 ≠ n := by
          intro heq
          have heq2 : l = (s, n) := hinj l hlC (s, n) hl₀C heq
          rw [heq2] at hl
          exact (List.Nodup.mem_erase_iff hCnodup).mp hl |>.1 rfl
        omega
      have hna : ∀ a ∈ (List.range n).sublists, n ∉ a := by
        intro a ha hna
        have hsub' : a <+ List.range n := List.mem_sublists.mp ha
        have hmem : n ∈ List.range n := hsub'.subset hna
        rw [List.mem_range] at hmem
        exact Nat.lt_irrefl n hmem
      have hcongr' : ∀ a ∈ (List.range n).sublists,
          evalClause (a ++ [n]) (C.erase (s, n)) = evalClause a (C.erase (s, n)) := by
        intro a ha
        apply evalClause_congr
        intro u hu
        have hune : u ≠ n := by
          intro heq
          obtain ⟨l, hlC', hl2⟩ := List.mem_map.mp hu
          have heq2 : l = (s, n) := hinj l (List.mem_of_mem_erase hlC') (s, n) hl₀C
            (by rw [hl2, heq])
          rw [heq2] at hlC'
          exact (List.Nodup.mem_erase_iff hCnodup).mp hlC' |>.1 rfl
        simp [List.mem_append, hune]
      have hchar1 : ∀ a ∈ (List.range n).sublists, s = true →
          !evalClause a C = !evalClause a (C.erase (s, n)) := by
        intro a ha hs
        have hiff : (evalClause a C = false) ↔
            (evalClause a (C.erase (s, n)) = false) := by
          rw [evalClause_eq_false_iff,
            falsifies_erase_split a C (s, n) hCnodup hl₀C, evalClause_eq_false_iff]
          have hl0 : evalLiteral a (s, n) = false := by
            have hna' : n ∉ a := hna a ha
            simp only [evalLiteral, evalVar]
            rw [show decide (n ∈ a) = false from by simp [hna'], hs]
          simp [hl0]
        cases e1 : evalClause a C <;>
          cases e2 : evalClause a (C.erase (s, n)) <;> simp_all
      have hchar2 : ∀ a ∈ (List.range n).sublists, s = false →
          !evalClause a C = false := by
        intro a ha hs
        have hlit : evalLiteral a (s, n) = true := by
          have hna' : n ∉ a := hna a ha
          simp only [evalLiteral, evalVar]
          rw [show decide (n ∈ a) = false from by simp [hna']]
          simp [hs]
        have htrue : evalClause a C = true := by
          rw [evalClause_literal_iff]
          exact ⟨(s, n), hl₀C, hlit⟩
        simp [htrue]
      have hchar3 : ∀ a ∈ (List.range n).sublists, s = false →
          !evalClause (a ++ [n]) C = !evalClause a (C.erase (s, n)) := by
        intro a ha hs
        have hiff : (evalClause (a ++ [n]) C = false) ↔
            (evalClause a (C.erase (s, n)) = false) := by
          rw [evalClause_eq_false_iff,
            falsifies_erase_split (a ++ [n]) C (s, n) hCnodup hl₀C,
            evalClause_eq_false_iff]
          have hl0 : evalLiteral (a ++ [n]) (s, n) = false := by
            have hmem : n ∈ a ++ [n] := by simp
            simp only [evalLiteral, evalVar]
            rw [show decide (n ∈ a ++ [n]) = true from by simp [hmem], hs]
          have hlit : ∀ l ∈ C.erase (s, n),
              evalLiteral (a ++ [n]) l = evalLiteral a l := by
            intro l hl
            obtain ⟨s', v⟩ := l
            have hne : v ≠ n := by
              intro heq
              have hmem' : (s', v) ∈ C := List.mem_of_mem_erase hl
              have heq2 : (s', v) = (s, n) := hinj _ hmem' _ hl₀C (by rw [heq])
              rw [heq2] at hl
              exact (List.Nodup.mem_erase_iff hCnodup).mp hl |>.1 rfl
            simp only [evalLiteral, evalVar]
            rw [show decide (v ∈ a ++ [n]) = decide (v ∈ a) from by
              have hiff2 : (v ∈ a ++ [n]) ↔ (v ∈ a) := by simp [List.mem_append, hne]
              simp [hiff2]]
          constructor
          · rintro ⟨h0, h'⟩ l hl
            rw [← hlit l hl]
            exact h' l hl
          · intro h
            exact ⟨hl0, fun l hl => by rw [hlit l hl]; exact h l hl⟩
        cases e1 : evalClause (a ++ [n]) C <;>
          cases e2 : evalClause a (C.erase (s, n)) <;> simp_all
      have hchar4 : ∀ a ∈ (List.range n).sublists, s = true →
          !evalClause (a ++ [n]) C = false := by
        intro a ha hs
        have hlit : evalLiteral (a ++ [n]) (s, n) = true := by
          have hmem : n ∈ a ++ [n] := by simp
          simp only [evalLiteral, evalVar]
          rw [show decide (n ∈ a ++ [n]) = true from by simp [hmem]]
          simp [hs]
        have htrue : evalClause (a ++ [n]) C = true := by
          rw [evalClause_literal_iff]
          exact ⟨(s, n), hl₀C, hlit⟩
        simp [htrue]
      by_cases hs : s = true
      · have hfilter1 : ((List.range n).sublists.filter (fun a => !evalClause a C))
            = ((List.range n).sublists.filter (fun a => !evalClause a (C.erase (s, n)))) := by
          apply List.filter_congr
          intro a ha
          exact hchar1 a ha hs
        have hfilter2 : ((List.range n).sublists.filter
            (fun a => !evalClause (a ++ [n]) C)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro a ha
          simp [hchar4 a ha hs]
        rw [hfilter1, hfilter2, List.length_nil, ih hC'nodup hC'sub]
        have hlen : C.length = (C.erase (s, n)).length + 1 := by
          have hpos : 0 < C.length := List.length_pos_of_mem hl₀C
          omega
        have hexp : Nat.succ n - C.length = n - (C.erase (s, n)).length := by
          rw [Nat.succ_eq_add_one]; omega
        rw [hexp]
        simp
      · have hs' : s = false := (Bool.not_eq_true s).mp hs
        have hfilter1 : ((List.range n).sublists.filter (fun a => !evalClause a C)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro a ha
          simp [hchar2 a ha hs']
        have hfilter2 : ((List.range n).sublists.filter
            (fun a => !evalClause (a ++ [n]) C))
            = ((List.range n).sublists.filter
              (fun a => !evalClause a (C.erase (s, n)))) := by
          apply List.filter_congr
          intro a ha
          exact hchar3 a ha hs'
        rw [hfilter1, hfilter2, List.length_nil, ih hC'nodup hC'sub]
        have hlen : C.length = (C.erase (s, n)).length + 1 := by
          have hpos : 0 < C.length := List.length_pos_of_mem hl₀C
          omega
        have hexp : Nat.succ n - C.length = n - (C.erase (s, n)).length := by
          rw [Nat.succ_eq_add_one]; omega
        rw [hexp]
        simp
    · -- `n` does not occur in `C`: both extensions of each falsifier falsify `C`.
      have hsub' : ∀ l ∈ C, l.2 < n := by
        intro l hl
        have hlt := hsub l hl
        have hne : l.2 ≠ n := by
          intro heq
          have hmem : l.2 ∈ C.map Prod.snd := List.mem_map_of_mem Prod.snd hl
          exact hn (heq ▸ hmem)
        omega
      have hle : C.length ≤ n := by
        have h := nodup_length_le_of_lt hC (by
          intro v hv
          obtain ⟨l, hlC, hl2⟩ := List.mem_map.mp hv
          rw [← hl2]
          exact hsub' l hlC)
        rwa [List.length_map] at h
      have hcongrA : ∀ a : assgn, evalClause (a ++ [n]) C = evalClause a C := by
        intro a
        apply evalClause_congr
        intro u hu
        have hune : u ≠ n := by
          intro heq
          exact hn (heq ▸ hu)
        simp [List.mem_append, hune]
      have hfilter2 : ((List.range n).sublists.filter (fun a => !evalClause (a ++ [n]) C))
          = ((List.range n).sublists.filter (fun a => !evalClause a C)) := by
        apply List.filter_congr
        intro a _
        rw [hcongrA]
      rw [hfilter2, ih hC hsub']
      have hexp : Nat.succ n - C.length = (n - C.length) + 1 := by
        rw [Nat.succ_eq_add_one]; omega
      rw [hexp, pow_succ]
      omega

end PvsNP.Units.m3_clause_falsifiers_count

theorem PvsNP.Units.m3_clause_falsifiers_count :
    ∀ (n : ℕ) (C : clause), (C.map Prod.snd).Nodup → (∀ l ∈ C, l.2 < n) →
      ((List.range n).sublists.filter (fun a => !evalClause a C)).length
        = 2 ^ (n - C.length) :=
  PvsNP.Units.m3_clause_falsifiers_count.count_falsifiers_range
