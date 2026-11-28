import Mathlib
import PvsNP.Defs
import CookLevin

/-! Template-fix probe battery (2026-11-28). Each example is independent;
errors are expected for the "confirm failure" probes. -/

-- ===== Signatures =====
#check @List.mem_cons_self
#check @Set.mem_compl_iff
#check @evalCnf_clause_iff
#check @evalClause_literal_iff
#check @Nat.mul_le_mul_left
#check @Nat.one_le_pow
#check @pow_mul'
#check @Polynomial.eval_eq_sum_range
#check @List.mem_append

-- ===== conp (tpl16) =====
-- C1: full-application .mp
example (L : Language Bool) (x : List Bool) (h : x ∈ Lᶜ) : x ∉ L :=
  (Set.mem_compl_iff L x).mp h
-- C2: full-application .mpr
example (L : Language Bool) (x : List Bool) (h : x ∉ L) : x ∈ Lᶜ :=
  (Set.mem_compl_iff L x).mpr h
-- C3: hxL replacement (was simpa [Set.mem_compl_iff] using hx)
example (L : Language Bool) (x : List Bool) (hx : ¬ x ∈ Lᶜ) : x ∈ L := by
  by_contra h'
  exact hx ((Set.mem_compl_iff L x).mpr h')
-- C4: cases site A fix (true branch rfl instead of exact hVw)
example (V : List Bool × List Bool → Bool) (x w : List Bool)
    (hcon : ¬ V (x, w) = true) : V (x, w) = true := by
  cases hVw : V (x, w) with
  | true => rfl
  | false => simp [hVw] at hcon
-- C5: defeq fallbacks (just to know)
example (L : Language Bool) (x : List Bool) (h : x ∈ Lᶜ) : x ∉ L := h
example (L : Language Bool) (x : List Bool) (h : x ∉ L) : x ∈ Lᶜ := h
-- C6: cases site B replica (was passing; confirm untouched pattern still ok)
example (V : List Bool × List Bool → Bool) (x w : List Bool)
    (hVfalse : ¬ V (x, w) = true) : (fun xw => !V xw) (x, w) = true := by
  cases hVw : V (x, w) with
  | true => exact absurd hVw hVfalse
  | false => simp [hVw]

-- ===== fresh (tpl03) =====
-- F1: full-application .mp on evalCnf_clause_iff with satisfiesCnf hypothesis
example (a : assgn) (N : cnf) (haN : satisfiesCnf a N) (E : clause) (hE : E ∈ N) :
    evalClause a E = true :=
  ((evalCnf_clause_iff a N).mp haN) E hE
-- F1b: variant, unfold satisfiesCnf first
example (a : assgn) (N : cnf) (haN : satisfiesCnf a N) (E : clause) (hE : E ∈ N) :
    evalClause a E = true := by
  rw [satisfiesCnf] at haN
  exact ((evalCnf_clause_iff a N).mp haN) E hE
-- F2: mem_cons_self in refine position, replica of candidate line 152-154 context
example (a : assgn) (C : clause) (z : var) :
    evalClause (z :: a) ((true, z) :: C) = true := by
  rw [evalClause_literal_iff]
  refine ⟨(true, z), List.mem_cons_self _ _, ?_⟩
  simp [evalLiteral, evalVar]
-- F2x: same but exact + by-block third component
example (a : assgn) (C : clause) (z : var) :
    evalClause (z :: a) ((true, z) :: C) = true := by
  rw [evalClause_literal_iff]
  exact ⟨(true, z), List.mem_cons_self _ _, by simp [evalLiteral, evalVar]⟩
-- F2y: bare membership, term mode with args, tactic alternatives
example (C : clause) (z : var) : (true, z) ∈ (true, z) :: C := List.mem_cons_self _ _
example (C : clause) (z : var) : (true, z) ∈ (true, z) :: C := by simp
example (C : clause) (z : var) : (true, z) ∈ (true, z) :: C :=
  List.mem_cons.mpr (Or.inl rfl)
-- F4: replica of candidate lines 125-132 (exact position, erase branch; was passing)
example (a : assgn) (C : clause) (z : var) (hCz : evalClause (a.erase z) C = true) :
    evalClause (a.erase z) ((true, z) :: C) = true := by
  rw [evalClause_literal_iff]
  exact ⟨(true, z), List.mem_cons_self _ _,
    by
      rw [evalClause_literal_iff] at hCz
      obtain ⟨l, hlC, hval⟩ := hCz
      exact ⟨l, List.mem_cons_of_mem _ hlC, hval⟩⟩
-- F3: hDa replacement (no simp normal-form dance)
example (a : assgn) (C D : clause) (hCD : evalClause a (C ++ D) = true)
    (hCa : ¬ evalClause a C = true) : evalClause a D = true := by
  rw [evalClause_literal_iff] at hCD ⊢
  obtain ⟨l, hl, hval⟩ := hCD
  rcases List.mem_append.mp hl with hlC | hlD
  · exfalso
    apply hCa
    rw [evalClause_literal_iff]
    exact ⟨l, hlC, hval⟩
  · exact ⟨l, hlD, hval⟩

-- ===== eb (tpl17) =====
-- E1a: eval_eq_sum_range via exact (default transparency)
example (p : Polynomial ℕ) (m : ℕ) :
    p.eval m = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * m ^ i := by
  exact Polynomial.eval_eq_sum_range
-- E1b: via rw
example (p : Polynomial ℕ) (m : ℕ) :
    p.eval m = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * m ^ i := by
  rw [Polynomial.eval_eq_sum_range]
-- E1c: coeff defeq check
example (p : Polynomial ℕ) (i : ℕ) : p.coeff i = AddMonoidAlgebra.coeff p i := rfl
-- E1d: with set d (mirrors template context)
example (p : Polynomial ℕ) (m : ℕ) :
    p.eval m = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * m ^ i := by
  set d := p.natDegree with hd
  exact Polynomial.eval_eq_sum_range
-- E2a: pow_mul' variant for hpow
example (d E : ℕ) (f : ℕ → ℕ) (n : ℕ) (hfE : f n ≤ 2 ^ E) :
    (f n) ^ d ≤ 2 ^ (d * E) := by
  have h1 : (f n) ^ d ≤ (2 ^ E) ^ d := Nat.pow_le_pow_left hfE d
  rwa [← pow_mul'] at h1
-- E2b: mul_comm variant for hpow
example (d E : ℕ) (f : ℕ → ℕ) (n : ℕ) (hfE : f n ≤ 2 ^ E) :
    (f n) ^ d ≤ 2 ^ (d * E) := by
  have h1 : (f n) ^ d ≤ (2 ^ E) ^ d := Nat.pow_le_pow_left hfE d
  rw [← pow_mul, Nat.mul_comm E d] at h1
  exact h1
-- E3a: one_le_pow for (n+1)^D
example (n D : ℕ) : 1 ≤ (n + 1) ^ D := Nat.one_le_pow D (n + 1) (Nat.succ_pos n)
-- E3b: one_le_pow for 2^(d*E)
example (d E : ℕ) : (1 : ℕ) ≤ 2 ^ (d * E) := Nat.one_le_pow (d * E) 2 (by norm_num)
-- E3c: hN1 in set context
example (n D : ℕ) : True := by
  set N := (n + 1) ^ D with hN
  have hN1 : 1 ≤ N := Nat.one_le_pow D (n + 1) (Nat.succ_pos n)
  trivial
-- E4: hterm m=0 calc without the bare `= p.coeff i` middle step
example (c i d : ℕ) (h0 : (0 : ℕ) ^ i ≤ 1) (h1 : (0 : ℕ) ^ d + 1 ≥ 1) :
    c * (0 : ℕ) ^ i ≤ c * ((0 : ℕ) ^ d + 1) := by
  calc c * (0 : ℕ) ^ i
      ≤ c * 1 := Nat.mul_le_mul_left _ h0
    _ ≤ c * ((0 : ℕ) ^ d + 1) := Nat.mul_le_mul_left _ h1
-- E5: confirm positivity on 1 ≤ 2^_ still fails (control)
example (d E : ℕ) : (1 : ℕ) ≤ 2 ^ (d * E) := by positivity
