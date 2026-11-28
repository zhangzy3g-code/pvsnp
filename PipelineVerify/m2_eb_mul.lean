import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Self-authored proof (self-authored-20261128): exponential-bound closure for `m2_eb_mul`,
    written from the statement alone for the desk pre-solve bank. -/
theorem PvsNP.Units.m2_eb_mul :
    ∀ f g : ℕ → ℕ, (∃ A D : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (A * (n + 1) ^ D)) → (∃ A D : ℕ, ∀ n : ℕ, g n ≤ 2 ^ (A * (n + 1) ^ D)) →
  ∃ A D : ℕ, ∀ n : ℕ, f n * g n ≤ 2 ^ (A * (n + 1) ^ D) := by
  intro f g hf hg
  obtain ⟨A₁, D₁, hf'⟩ := hf
  obtain ⟨A₂, D₂, hg'⟩ := hg
  refine ⟨A₁ + A₂, max D₁ D₂, fun n => ?_⟩
  have h1 : (n + 1) ^ D₁ ≤ (n + 1) ^ max D₁ D₂ :=
    Nat.pow_le_pow_right (Nat.le_add_left 1 n) (le_max_left D₁ D₂)
  have h2 : (n + 1) ^ D₂ ≤ (n + 1) ^ max D₁ D₂ :=
    Nat.pow_le_pow_right (Nat.le_add_left 1 n) (le_max_right D₁ D₂)
  calc f n * g n ≤ 2 ^ (A₁ * (n + 1) ^ D₁) * 2 ^ (A₂ * (n + 1) ^ D₂) :=
        Nat.mul_le_mul (hf' n) (hg' n)
    _ = 2 ^ (A₁ * (n + 1) ^ D₁ + A₂ * (n + 1) ^ D₂) := (pow_add 2 _ _).symm
    _ ≤ 2 ^ ((A₁ + A₂) * (n + 1) ^ max D₁ D₂) := by
        apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
        rw [add_mul]
        exact add_le_add (Nat.mul_le_mul_left A₁ h1) (Nat.mul_le_mul_left A₂ h2)

#print axioms PvsNP.Units.m2_eb_mul
