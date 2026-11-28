import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Self-authored proof (self-authored-20261128): exponential-bound closure for `m2_eb_two_pow`,
    written from the statement alone for the desk pre-solve bank. -/
theorem PvsNP.Units.m2_eb_two_pow :
    ∀ (f : ℕ → ℕ) (A D K : ℕ), (∀ n : ℕ, f n ≤ A * (n + 1) ^ D) →
  ∃ B E : ℕ, ∀ n : ℕ, 2 ^ (f n ^ K) ≤ 2 ^ (B * (n + 1) ^ E) := by
  intro f A D K hf
  refine ⟨A ^ K, D * K, fun n => ?_⟩
  have hstep : (f n) ^ K ≤ (A * (n + 1) ^ D) ^ K :=
    Nat.pow_le_pow_left (hf n) K
  have hform : (A * (n + 1) ^ D) ^ K = A ^ K * (n + 1) ^ (D * K) := by
    rw [mul_pow, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (hform ▸ hstep)

#print axioms PvsNP.Units.m2_eb_two_pow

example : (1 : ℕ) = 2 := rfl
