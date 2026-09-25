import Formalization.ExponentialContradiction

/-!
# Elementary numerical estimates

This file contains no Fourier analysis or additive combinatorics.  It reduces
the final finite contradiction to two transparent inequalities: enough
decay in `baseDecay b ^ L`, and enough binary digit subsets compared with the
base-`b` scale.
-/

noncomputable section

namespace DigitRestricted

/-- A deliberately loose elementary bound for a quadratic by the exponential
at half its argument.  It is what keeps the final scale proportional to
`b^(m/2)` rather than `b^m`. -/
theorem nat_sq_le_eight_two_pow_half (m : ℕ) :
    m ^ 2 ≤ 8 * 2 ^ ((m + 1) / 2) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm : m < 7
      · interval_cases m <;> norm_num
      · have hm7 : 7 ≤ m := by omega
        have hprev := ih (m - 2) (by omega)
        have hsub : m - 2 + 2 = m := by omega
        have hhalf : ((m - 2 + 1) / 2) + 1 = (m + 1) / 2 := by omega
        calc
          m ^ 2 ≤ 2 * (m - 2) ^ 2 := by
            nlinarith
          _ ≤ 2 * (8 * 2 ^ ((m - 2 + 1) / 2)) := Nat.mul_le_mul_left 2 hprev
          _ = 8 * 2 ^ ((m + 1) / 2) := by
            rw [← hhalf, pow_succ]
            ring

theorem nat_sq_le_eight_base_pow_half {b m : ℕ} (hb : 2 ≤ b) :
    m ^ 2 ≤ 8 * b ^ ((m + 1) / 2) := by
  calc
    m ^ 2 ≤ 8 * 2 ^ ((m + 1) / 2) := nat_sq_le_eight_two_pow_half m
    _ ≤ 8 * b ^ ((m + 1) / 2) := by gcongr

/-- A base-dependent exponent for which the fixed product-decay factor is
small enough for the final comparison. -/
theorem exists_baseDecay_power_bound {b : ℕ} (hb : 2 ≤ b) :
    ∃ K : ℕ, baseDecay b ^ K ≤ 1 / (160 * (b : ℝ) ^ 2) := by
  have htarget : (0 : ℝ) < 1 / (160 * (b : ℝ) ^ 2) := by positivity
  have hq_lt : baseDecay b < 1 := by
    rw [baseDecay]
    have : (0 : ℝ) < 1 / (2 * (b : ℝ) ^ 2) := by positivity
    linarith
  rcases exists_pow_lt_of_lt_one htarget hq_lt with ⟨K, hK⟩
  exact ⟨K, hK.le⟩

theorem baseDecay_mul_exponent_bound
    {b m K : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hK : baseDecay b ^ K ≤ 1 / (160 * (b : ℝ) ^ 2)) :
    baseDecay b ^ (K * m) ≤ 1 / (160 * (b : ℝ) ^ (2 * m)) := by
  have hq0 : 0 ≤ baseDecay b := baseDecay_nonneg hb
  have hpow := pow_le_pow_left₀ (pow_nonneg hq0 K) hK m
  rw [pow_mul]
  refine hpow.trans ?_
  have h160 : (160 : ℝ) ≤ 160 ^ m := by
    calc
      (160 : ℝ) = 160 ^ 1 := by ring
      _ ≤ 160 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hden : 160 * (b : ℝ) ^ (2 * m) ≤
      (160 * (b : ℝ) ^ 2) ^ m := by
    rw [mul_pow, ← pow_mul]
    gcongr
  calc
    (1 / (160 * (b : ℝ) ^ 2)) ^ m =
        1 / (160 * (b : ℝ) ^ 2) ^ m := by simp only [one_div, inv_pow]
    _ ≤ 1 / (160 * (b : ℝ) ^ (2 * m)) :=
      one_div_le_one_div_of_le
        (by positivity : (0 : ℝ) < 160 * (b : ℝ) ^ (2 * m)) hden

/-- A sufficiently large multiple of `b^ceil(m/2)` contains far more binary
digit subsets than the polynomial base-`b` loss in the Fourier estimate. -/
theorem binary_size_of_sqrt_scale
    {b r m : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hscale : (32 * b + 8) * b ^ ((m + 1) / 2) ≤ r) :
    160 * (b : ℝ) ^ (2 * m) < (2 : ℝ) ^ (r + 1) := by
  let u : ℕ := b ^ ((m + 1) / 2)
  have hu : 1 ≤ u := Nat.one_le_pow _ _ (by omega)
  have hsq : m ^ 2 ≤ 8 * u := by
    simpa [u] using nat_sq_le_eight_base_pow_half (b := b) (m := m) hb
  have hmU : m ≤ 8 * u := by
    have hmm : m ≤ m ^ 2 := by nlinarith
    exact hmm.trans hsq
  have hexponent : 4 * b * m + 8 ≤ r + 1 := by
    calc
      4 * b * m + 8 ≤ 4 * b * (8 * u) + 8 * u := by
        exact Nat.add_le_add (Nat.mul_le_mul_left (4 * b) hmU)
          (Nat.mul_le_mul_left 8 hu)
      _ = (32 * b + 8) * u := by ring
      _ ≤ r := by simpa [u] using hscale
      _ ≤ r + 1 := by omega
  have hbTwo : b ≤ 2 ^ (2 * b) := by
    exact le_trans (by nlinarith : b ≤ 2 * b ^ 2 + 1)
      (Nat.two_mul_sq_add_one_le_two_pow_two_mul b)
  have hbPower : b ^ (2 * m) ≤ 2 ^ (4 * b * m) := by
    calc
      b ^ (2 * m) ≤ (2 ^ (2 * b)) ^ (2 * m) := Nat.pow_le_pow_left hbTwo _
      _ = 2 ^ (4 * b * m) := by rw [← pow_mul]; congr 1 <;> ring
  have hnat : 160 * b ^ (2 * m) < 2 ^ (r + 1) := by
    calc
      160 * b ^ (2 * m) < 256 * b ^ (2 * m) := by
        gcongr
        norm_num
      _ ≤ 256 * 2 ^ (4 * b * m) := Nat.mul_le_mul_left 256 hbPower
      _ = 2 ^ (4 * b * m + 8) := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by omega) hexponent
  exact_mod_cast hnat

/-- Two elementary numerical hypotheses force the upper side of the finite
Fourier estimate strictly below its lower side. -/
theorem digitBlock_gap_of_decay
    {b r m L : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hdecay : baseDecay b ^ L ≤
      1 / (160 * (b : ℝ) ^ (2 * m)))
    (hsize : 160 * (b : ℝ) ^ (2 * m) < (2 : ℝ) ^ (r + 1)) :
    ((4 * b ^ m : ℕ) : ℝ) *
        (1 + (2 : ℝ) ^ (r + 1) * baseDecay b ^ L) <
      ((2 : ℕ) ^ (r + 1) - 1 : ℕ) /
        (5 * ((2 * b ^ m : ℕ) : ℝ)) := by
  let X : ℝ := (2 : ℝ) ^ (r + 1)
  let Y : ℝ := (b : ℝ) ^ m
  let q : ℝ := baseDecay b ^ L
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hXtwo : 2 ≤ X := by
    dsimp [X]
    have : (1 : ℕ) ≤ r + 1 := by omega
    calc
      (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r + 1) := pow_le_pow_right₀ (by norm_num) this
  have hpow : (b : ℝ) ^ (2 * m) = Y ^ 2 := by
    dsimp [Y]
    rw [show 2 * m = m * 2 by omega, pow_mul]
  have hsize' : 160 * Y ^ 2 < X := by simpa [X, hpow] using hsize
  have hdecay' : q ≤ 1 / (160 * Y ^ 2) := by simpa [q, hpow] using hdecay
  have hconstant : 4 * Y < X / (40 * Y) := by
    apply (lt_div_iff₀ (by positivity : 0 < 40 * Y)).2
    nlinarith
  have hdecayMul : (160 * Y ^ 2) * q ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 160 * Y ^ 2)).mp hdecay'
    simpa [mul_comm] using h
  have hoscillatory : 4 * Y * (X * q) ≤ X / (40 * Y) := by
    apply (le_div_iff₀ (by positivity : 0 < 40 * Y)).2
    have hmul := mul_le_mul_of_nonneg_right hdecayMul hX
    nlinarith
  have hupper : 4 * Y * (1 + X * q) < X / (20 * Y) := by
    calc
      4 * Y * (1 + X * q) = 4 * Y + 4 * Y * (X * q) := by ring
      _ < X / (40 * Y) + X / (40 * Y) := add_lt_add_of_lt_of_le hconstant hoscillatory
      _ = X / (20 * Y) := by field_simp; ring
  have hlower : X / (20 * Y) ≤ (X - 1) / (10 * Y) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 20 * Y)
      (by positivity : 0 < 10 * Y)).2
    nlinarith
  have hnat : 1 ≤ (2 : ℕ) ^ (r + 1) := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub hnat]
  push_cast
  change 4 * Y * (1 + X * q) < (X - 1) / (5 * (2 * Y))
  calc
    4 * Y * (1 + X * q) < X / (20 * Y) := hupper
    _ ≤ (X - 1) / (10 * Y) := hlower
    _ = (X - 1) / (5 * (2 * Y)) := by ring

/-! ## The finite approximation theorem -/

/-- The paper's `Necessary1.1`, with the harmless exact integer scale
`b^ceil(m/2)`.  This is the form needed to recover the inverse-square
logarithmic approximation rate. -/
theorem necessaryStarApproximation {b : ℕ} (hb : 2 ≤ b) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (γ : ℝ) (m r : ℕ), 1 ≤ m →
      J * b ^ ((m + 1) / 2) ≤ r →
      ∃ n : ℕ, IsDigitRestrictedStarUpTo b r n ∧ n ≠ 0 ∧
        circleNorm (γ * n) ≤ 1 / (2 * (b : ℝ) ^ m) := by
  rcases exists_baseDecay_power_bound hb with ⟨K, hK⟩
  let J : ℕ := 8 * K + 32 * b + 22
  refine ⟨J, by dsimp [J]; omega, ?_⟩
  intro γ m r hm hr
  let u : ℕ := b ^ ((m + 1) / 2)
  have hu : 1 ≤ u := Nat.one_le_pow _ _ (by omega)
  have hsq : m ^ 2 ≤ 8 * u := by
    simpa [u] using nat_sq_le_eight_base_pow_half (b := b) (m := m) hb
  have hmU : m ≤ 8 * u := by
    have hmm : m ≤ m ^ 2 := by nlinarith
    exact hmm.trans hsq
  have hKm : K * m ^ 2 ≤ 8 * K * u := by
    calc
      K * m ^ 2 ≤ K * (8 * u) := Nat.mul_le_mul_left K hsq
      _ = 8 * K * u := by ring
  have hsmallScale : (K * m) * m + m + 6 * u ≤ (8 * K + 14) * u := by
    calc
      (K * m) * m + m + 6 * u = K * m ^ 2 + m + 6 * u := by ring
      _ ≤ 8 * K * u + 8 * u + 6 * u := by omega
      _ = (8 * K + 14) * u := by ring
  have hJscale : J * u ≤ r := by simpa [J, u] using hr
  have hannulusScale : (K * m) * m + m + 6 * u ≤ r + 1 := by
    calc
      (K * m) * m + m + 6 * u ≤ (8 * K + 14) * u := hsmallScale
      _ ≤ J * u := by
        apply Nat.mul_le_mul_right u
        dsimp [J]
        omega
      _ ≤ r := hJscale
      _ ≤ r + 1 := by omega
  have hbinaryScale : (32 * b + 8) * u ≤ r := by
    calc
      (32 * b + 8) * u ≤ J * u := by
        apply Nat.mul_le_mul_right u
        dsimp [J]
        omega
      _ ≤ r := hJscale
  have hdecay := baseDecay_mul_exponent_bound hb hm hK
  have hsize := binary_size_of_sqrt_scale hb hm (by simpa [u] using hbinaryScale)
  have hgap := digitBlock_gap_of_decay hb hm hdecay hsize
  exact exists_starUpTo_approximation_of_gap hb hm γ
    (by simpa [u] using hannulusScale) hgap

end DigitRestricted
