import Formalization.NumericalEstimates

/-!
# From the finite digit scale to an inverse-square bound

The analytic argument naturally produces a denominator from a digit block of
length `r`.  This file performs the first scale conversion, choosing the
annulus parameter from the integer logarithm of `r`.
-/

noncomputable section

namespace DigitRestricted

/-- The defining upper estimate for the integer base-`b` logarithm, converted
to the real logarithm. -/
theorem realLog_lt_natLog_succ_mul {b N : ℕ} (hb : 2 ≤ b) (hN : 1 ≤ N) :
    Real.log (N : ℝ) < (Nat.log b N + 1 : ℕ) * Real.log (b : ℝ) := by
  have hnat := Nat.lt_pow_succ_log_self (by omega : 1 < b) N
  have hcast : (N : ℝ) < ((b ^ (Nat.log b N + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hlog := Real.strictMonoOn_log
    (show (N : ℝ) ∈ Set.Ioi 0 by change (0 : ℝ) < N; positivity)
    (show ((b ^ (Nat.log b N + 1) : ℕ) : ℝ) ∈ Set.Ioi 0 by
      change (0 : ℝ) < ((b ^ (Nat.log b N + 1) : ℕ) : ℝ)
      exact_mod_cast pow_pos (by omega : 0 < b) (Nat.log b N + 1))
    hcast
  rw [Nat.cast_pow] at hlog
  rw [Real.log_pow] at hlog
  simpa using hlog

/-- At a sufficiently large digit scale, the finite theorem gives an
approximation of order `r⁻²`. -/
theorem starApproximation_at_digit_scale {b : ℕ} (hb : 2 ≤ b) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (γ : ℝ) (r : ℕ), b ^ (2 * J + 1) ≤ r →
      ∃ n : ℕ, IsDigitRestrictedStarUpTo b r n ∧ n ≠ 0 ∧
        circleNorm (γ * n) ≤
          (((b ^ (4 * J + 3) : ℕ) : ℝ) / 2) / (r : ℝ) ^ 2 := by
  rcases necessaryStarApproximation hb with ⟨J, hJ, hnecessary⟩
  refine ⟨J, hJ, ?_⟩
  intro γ r hr
  let q : ℕ := Nat.log b r
  let p : ℕ := q - 2 * J
  let m : ℕ := 2 * p - 1
  have hblog : Nat.log b (b ^ (2 * J + 1)) ≤ Nat.log b r :=
    Nat.log_monotone hr
  have hq : 2 * J + 1 ≤ q := by
    rw [Nat.log_pow (by omega)] at hblog
    exact hblog
  have hp : 1 ≤ p := by dsimp [p]; omega
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hhalf : (m + 1) / 2 = p := by dsimp [m]; omega
  have hJtwo : J ≤ 2 ^ (2 * J) := by
    exact le_trans (by nlinarith : J ≤ 2 * J ^ 2 + 1)
      (Nat.two_mul_sq_add_one_le_two_pow_two_mul J)
  have hJbase : J ≤ b ^ (2 * J) := by
    exact hJtwo.trans (Nat.pow_le_pow_left hb (2 * J))
  have hpowlog : b ^ q ≤ r := by
    apply Nat.pow_log_le_self
    have : 0 < r := lt_of_lt_of_le (pow_pos (by omega) _) hr
    omega
  have hscale : J * b ^ ((m + 1) / 2) ≤ r := by
    rw [hhalf]
    calc
      J * b ^ p ≤ b ^ (2 * J) * b ^ p := Nat.mul_le_mul_right _ hJbase
      _ = b ^ q := by
        rw [← pow_add]
        congr 1
        dsimp [p]
        omega
      _ ≤ r := hpowlog
  rcases hnecessary γ m r hm hscale with ⟨n, hnstar, hnne, hn⟩
  refine ⟨n, hnstar, hnne, hn.trans ?_⟩
  have hrpos : 0 < r := lt_of_lt_of_le (pow_pos (by omega) _) hr
  have hrupper : r < b ^ (q + 1) := by
    simpa [q] using Nat.lt_pow_succ_log_self (by omega : 1 < b) r
  have hqsplit : q = p + 2 * J := by dsimp [p]; omega
  have hmexp : (q + 1) * 2 = m + (4 * J + 3) := by
    dsimp [m]
    omega
  have hrsquare : r ^ 2 ≤ b ^ m * b ^ (4 * J + 3) := by
    have hsquare : r ^ 2 < (b ^ (q + 1)) ^ 2 :=
      Nat.pow_lt_pow_left hrupper (by omega)
    rw [← pow_mul, hmexp, pow_add] at hsquare
    exact hsquare.le
  have hden₁ : (0 : ℝ) < 2 * (b : ℝ) ^ m := by positivity
  have hden₂ : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  apply (div_le_div_iff₀ hden₁ hden₂).2
  have hrsquareReal : (r : ℝ) ^ 2 ≤
      (b : ℝ) ^ m * (b : ℝ) ^ (4 * J + 3) := by exact_mod_cast hrsquare
  convert hrsquareReal using 1 <;> push_cast <;> ring

end DigitRestricted
