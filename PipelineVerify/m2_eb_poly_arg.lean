import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Self-authored proof (self-authored-20261128): exponential-bound closure for `m2_eb_poly_arg`,
    written from the statement alone for the desk pre-solve bank. -/
theorem PvsNP.Units.m2_eb_poly_arg :
    ∀ (f : ℕ → ℕ) (q : Polynomial ℕ), (∃ A D : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (A * (n + 1) ^ D)) →
  ∃ A D : ℕ, ∀ n : ℕ, f (q.eval n) ≤ 2 ^ (A * (n + 1) ^ D) := by
  intro f q hf
  obtain ⟨A, D, hf'⟩ := hf
  -- S = sum of coefficients of q, d = degree bound; q.eval n ≤ S * (n+1)^d
  set d := q.natDegree with hd
  set S := ∑ i ∈ Finset.range (d + 1), q.coeff i with hS
  have hq : ∀ n : ℕ, q.eval n ≤ S * (n + 1) ^ d := by
    intro n
    rw [Polynomial.eval_eq_sum_range]
    calc ∑ i ∈ Finset.range (d + 1), q.coeff i * n ^ i
        ≤ ∑ i ∈ Finset.range (d + 1), q.coeff i * (n + 1) ^ d := by
          apply Finset.sum_le_sum
          intro i hi
          apply Nat.mul_le_mul_left
          have hi' : i ≤ d := Nat.lt_succ.mp (Finset.mem_range.mp hi)
          calc n ^ i ≤ (n + 1) ^ i :=
                Nat.pow_le_pow_left (Nat.le_add_right n 1) i
            _ ≤ (n + 1) ^ d :=
                Nat.pow_le_pow_right (Nat.le_add_left 1 n) hi'
      _ = S * (n + 1) ^ d := by rw [Finset.sum_mul]
  refine ⟨A * (S + 1) ^ D, d * D, fun n => ?_⟩
  have hq1 : q.eval n + 1 ≤ (S + 1) * (n + 1) ^ d := by
    have hY : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (Nat.le_add_left 1 n)
    calc q.eval n + 1 ≤ S * (n + 1) ^ d + 1 * (n + 1) ^ d := by
          rw [one_mul]; exact Nat.add_le_add_right (hq n) _
      _ = (S + 1) * (n + 1) ^ d := by rw [add_mul]
  have hpow : (q.eval n + 1) ^ D ≤ ((S + 1) * (n + 1) ^ d) ^ D :=
    Nat.pow_le_pow_left hq1 D
  have hform : ((S + 1) * (n + 1) ^ d) ^ D = (S + 1) ^ D * (n + 1) ^ (d * D) := by
    rw [mul_pow, ← pow_mul]
  calc f (q.eval n) ≤ 2 ^ (A * (q.eval n + 1) ^ D) := hf' _
    _ ≤ 2 ^ (A * ((S + 1) ^ D * (n + 1) ^ (d * D))) := by
        apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
        exact Nat.mul_le_mul_left A (hform ▸ hpow)
    _ = 2 ^ ((A * (S + 1) ^ D) * (n + 1) ^ (d * D)) := by rw [mul_assoc]
