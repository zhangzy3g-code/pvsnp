import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m2_eb_poly

theorem statement :
    ∀ (p : Polynomial ℕ) (f : ℕ → ℕ),
      (∃ A D : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (A * (n + 1) ^ D)) →
      ∃ A D : ℕ, ∀ n : ℕ, p.eval (f n) ≤ 2 ^ (A * (n + 1) ^ D) := by
  intro p f ⟨A, D, hf⟩
  set d := p.natDegree with hd
  set C := ∑ i ∈ Finset.range (d + 1), p.coeff i with hC
  -- Claim 1: p.eval m ≤ C * (m ^ d + 1) for every m.
  have hclaim : ∀ m : ℕ, p.eval m ≤ C * (m ^ d + 1) := by
    intro m
    have hterm : ∀ i ∈ Finset.range (d + 1),
        p.coeff i * m ^ i ≤ p.coeff i * (m ^ d + 1) := by
      intro i hi
      have hid : i ≤ d := by
        have := Finset.mem_range.mp hi
        omega
      by_cases hm : m = 0
      · subst hm
        have h0 : (0 : ℕ) ^ i ≤ 1 := by cases i <;> simp
        have h1 : (0 : ℕ) ^ d + 1 ≥ 1 := by omega
        calc p.coeff i * (0 : ℕ) ^ i
            ≤ p.coeff i * 1 := Nat.mul_le_mul_left _ h0
          _ = p.coeff i := Nat.mul_one _
          _ ≤ p.coeff i * ((0 : ℕ) ^ d + 1) :=
            Nat.mul_le_mul_left _ h1
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        have hpow : m ^ i ≤ m ^ d := Nat.pow_le_pow_right hm1 hid
        calc p.coeff i * m ^ i
            ≤ p.coeff i * m ^ d := Nat.mul_le_mul_left _ hpow
          _ ≤ p.coeff i * (m ^ d + 1) :=
            Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    calc p.eval m
        = ∑ i ∈ Finset.range (d + 1), p.coeff i * m ^ i :=
          Polynomial.eval_eq_sum_range
      _ ≤ ∑ i ∈ Finset.range (d + 1), p.coeff i * (m ^ d + 1) :=
          Finset.sum_le_sum hterm
      _ = C * (m ^ d + 1) := by rw [Finset.sum_mul]
  -- Claim 2: assemble the final bound for each n.
  refine ⟨d * A + C + 1, D, fun n => ?_⟩
  set N := (n + 1) ^ D with hN
  set E := A * N with hE
  have hfE : f n ≤ 2 ^ E := hf n
  have hN1 : 1 ≤ N := by rw [hN]; positivity
  have hpow : (f n) ^ d ≤ 2 ^ (d * E) := by
    have h1 : (f n) ^ d ≤ (2 ^ E) ^ d := Nat.pow_le_pow_left hfE d
    rwa [← pow_mul] at h1
  have h2 : (f n) ^ d + 1 ≤ 2 ^ (d * E + 1) := by
    have hge : (1 : ℕ) ≤ 2 ^ (d * E) := by positivity
    have hsucc : 2 ^ (d * E + 1) = 2 ^ (d * E) * 2 := pow_succ _ _
    omega
  have h3 : C * ((f n) ^ d + 1) ≤ 2 ^ (C + (d * E + 1)) := by
    calc C * ((f n) ^ d + 1)
        ≤ C * 2 ^ (d * E + 1) := Nat.mul_le_mul_left _ h2
      _ ≤ 2 ^ C * 2 ^ (d * E + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self)
      _ = 2 ^ (C + (d * E + 1)) := (pow_add 2 C (d * E + 1)).symm
  have hexp : C + (d * E + 1) ≤ (d * A + C + 1) * N := by
    have h4 : (d * A + C + 1) * N = d * E + (C + 1) * N := by
      rw [hE]; ring
    rw [h4]
    have h5 : C + 1 ≤ (C + 1) * N := by
      calc C + 1 = (C + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (C + 1) * N := Nat.mul_le_mul_left _ hN1
    omega
  calc p.eval (f n)
      ≤ C * ((f n) ^ d + 1) := hclaim (f n)
    _ ≤ 2 ^ (C + (d * E + 1)) := h3
    _ ≤ 2 ^ ((d * A + C + 1) * N) :=
        Nat.pow_le_pow_right (by norm_num) hexp
    _ = 2 ^ ((d * A + C + 1) * (n + 1) ^ D) := by rw [hN]

end PvsNP.Units.m2_eb_poly

/-- Polynomial evaluation preserves exponential-polynomial bounds: if `f n`
is at most `2 ^ (A * (n + 1) ^ D)` then so is `p.eval (f n)`, with larger
constants. -/
theorem PvsNP.Units.m2_eb_poly :
    ∀ (p : Polynomial ℕ) (f : ℕ → ℕ),
      (∃ A D : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (A * (n + 1) ^ D)) →
      ∃ A D : ℕ, ∀ n : ℕ, p.eval (f n) ≤ 2 ^ (A * (n + 1) ^ D) :=
  PvsNP.Units.m2_eb_poly.statement
