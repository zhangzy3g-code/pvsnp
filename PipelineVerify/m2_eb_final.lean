import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- Self-authored proof (self-authored-20261128): exponential-bound closure for `m2_eb_final`,
    written from the statement alone for the desk pre-solve bank. -/
theorem PvsNP.Units.m2_eb_final :
    ∀ f : ℕ → ℕ, (∃ A D : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (A * (n + 1) ^ D)) → ∃ j : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (n ^ j) + j := by
  intro f hf
  obtain ⟨A, D, hf'⟩ := hf
  have hle2 : ∀ t : ℕ, t ≤ 2 ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ k ih =>
        calc k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
          _ ≤ 2 ^ k + 2 ^ k :=
              Nat.add_le_add_left (Nat.one_le_pow k 2 (by norm_num)) _
          _ = 2 ^ (k + 1) := by rw [pow_succ']; exact (two_mul _).symm
  have hA : A ≤ A * 2 ^ D := by
    conv_lhs => rw [← mul_one A]
    exact Nat.mul_le_mul_left A (Nat.one_le_pow D 2 (by norm_num))
  have h2A : 2 ^ A ≤ 2 ^ (A * 2 ^ D) := Nat.pow_le_pow_right (by norm_num) hA
  refine ⟨2 ^ (A * 2 ^ D) + 2 * D, fun n => ?_⟩
  have hpos : 0 < 2 ^ (A * 2 ^ D) + 2 * D :=
    Nat.add_pos_left (pow_pos (by norm_num) _) _
  by_cases hn0 : n = 0
  · subst hn0
    have hf0 := hf' 0
    simp only [zero_add, one_pow, mul_one] at hf0
    rw [zero_pow (Nat.ne_of_gt hpos)]
    calc f 0 ≤ 2 ^ A := hf0
      _ ≤ 2 ^ (A * 2 ^ D) := h2A
      _ ≤ 2 ^ (A * 2 ^ D) + 2 * D := Nat.le_add_right _ _
      _ ≤ 2 ^ 0 + (2 ^ (A * 2 ^ D) + 2 * D) := by
          rw [pow_zero]
          exact Nat.le_add_left _ _
  by_cases hn1 : n = 1
  · subst hn1
    have hf1 := hf' 1
    rw [show (1 + 1 : ℕ) = 2 from rfl] at hf1
    calc f 1 ≤ 2 ^ (A * 2 ^ D) := hf1
      _ ≤ 2 ^ (A * 2 ^ D) + 2 * D := Nat.le_add_right _ _
      _ ≤ 2 ^ (1 ^ (2 ^ (A * 2 ^ D) + 2 * D)) + (2 ^ (A * 2 ^ D) + 2 * D) :=
          Nat.le_add_left _ _
  · have h2 : 2 ≤ n := by omega
    have hsq : n + 1 ≤ n ^ 2 := by
      rw [pow_two]
      calc n + 1 ≤ n + n := Nat.add_le_add_left (by omega : 1 ≤ n) n
        _ = 2 * n := (two_mul n).symm
        _ = n * 2 := mul_comm 2 n
        _ ≤ n * n := Nat.mul_le_mul_left n h2
    have hpow1 : (n + 1) ^ D ≤ n ^ (2 * D) := by
      calc (n + 1) ^ D ≤ (n ^ 2) ^ D := Nat.pow_le_pow_left hsq D
        _ = n ^ (2 * D) := (pow_mul n 2 D).symm
    have hA2 : A ≤ n ^ (A * 2 ^ D) :=
      le_trans (le_trans (hle2 A) h2A) (Nat.pow_le_pow_left h2 _)
    have hkey : A * (n + 1) ^ D ≤ n ^ (2 ^ (A * 2 ^ D) + 2 * D) := by
      calc A * (n + 1) ^ D ≤ n ^ (A * 2 ^ D) * n ^ (2 * D) :=
            Nat.mul_le_mul hA2 hpow1
        _ = n ^ (A * 2 ^ D + 2 * D) := (pow_add n _ _).symm
        _ ≤ n ^ (2 ^ (A * 2 ^ D) + 2 * D) :=
            Nat.pow_le_pow_right (by omega : 1 ≤ n)
              (Nat.add_le_add_right (hle2 _) _)
    calc f n ≤ 2 ^ (A * (n + 1) ^ D) := hf' n
      _ ≤ 2 ^ (n ^ (2 ^ (A * 2 ^ D) + 2 * D)) :=
          Nat.pow_le_pow_right (by norm_num) hkey
      _ ≤ 2 ^ (n ^ (2 ^ (A * 2 ^ D) + 2 * D)) + (2 ^ (A * 2 ^ D) + 2 * D) :=
          Nat.le_add_right _ _
