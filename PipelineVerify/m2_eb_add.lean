import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Self-authored proof (self-authored-20261128): exponential-bound closure for `m2_eb_add`,
    written from the statement alone for the desk pre-solve bank. -/
theorem PvsNP.Units.m2_eb_add :
    ∀ f g : ℕ → ℕ, (∃ A D : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (A * (n + 1) ^ D)) → (∃ A D : ℕ, ∀ n : ℕ, g n ≤ 2 ^ (A * (n + 1) ^ D)) →
  ∃ A D : ℕ, ∀ n : ℕ, f n + g n ≤ 2 ^ (A * (n + 1) ^ D) := by
  intro f g hf hg
  obtain ⟨A₁, D₁, hf'⟩ := hf
  obtain ⟨A₂, D₂, hg'⟩ := hg
  refine ⟨A₁ + A₂ + 1, max D₁ D₂, fun n => ?_⟩
  have h1 : (n + 1) ^ D₁ ≤ (n + 1) ^ max D₁ D₂ :=
    Nat.pow_le_pow_right (Nat.le_add_left 1 n) (le_max_left D₁ D₂)
  have h2 : (n + 1) ^ D₂ ≤ (n + 1) ^ max D₁ D₂ :=
    Nat.pow_le_pow_right (Nat.le_add_left 1 n) (le_max_right D₁ D₂)
  have hmono : ∀ A D : ℕ, D ≤ max D₁ D₂ → 2 ^ (A * (n + 1) ^ D) ≤ 2 ^ ((A₁ + A₂) * (n + 1) ^ max D₁ D₂) := by
    intro A D hD
    apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
    calc A * (n + 1) ^ D ≤ A * (n + 1) ^ max D₁ D₂ :=
          Nat.mul_le_mul_left A (Nat.pow_le_pow_right (Nat.le_add_left 1 n) hD)
      _ ≤ (A₁ + A₂) * (n + 1) ^ max D₁ D₂ :=
          Nat.mul_le_mul_right _ (Nat.le_add_right A A₂)
  have hsum : f n + g n ≤ 2 * 2 ^ ((A₁ + A₂) * (n + 1) ^ max D₁ D₂) := by
    calc f n + g n ≤ 2 ^ (A₁ * (n + 1) ^ D₁) + 2 ^ (A₂ * (n + 1) ^ D₂) :=
          add_le_add (hf' n) (hg' n)
      _ ≤ 2 ^ ((A₁ + A₂) * (n + 1) ^ max D₁ D₂) + 2 ^ ((A₁ + A₂) * (n + 1) ^ max D₁ D₂) :=
          add_le_add (hmono A₁ D₁ (le_max_left D₁ D₂)) (hmono A₂ D₂ (le_max_right D₁ D₂))
      _ = 2 * 2 ^ ((A₁ + A₂) * (n + 1) ^ max D₁ D₂) := (two_mul _).symm
  have hY : 1 ≤ (n + 1) ^ max D₁ D₂ := Nat.one_le_pow _ _ (Nat.le_add_left 1 n)
  calc f n + g n ≤ 2 * 2 ^ ((A₁ + A₂) * (n + 1) ^ max D₁ D₂) := hsum
    _ = 2 ^ ((A₁ + A₂) * (n + 1) ^ max D₁ D₂ + 1) := by rw [pow_succ']; ring_nf; rw [mul_comm]
    _ ≤ 2 ^ ((A₁ + A₂ + 1) * (n + 1) ^ max D₁ D₂) := by
        apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
        rw [add_mul, one_mul]
        exact Nat.add_le_add_left hY _
