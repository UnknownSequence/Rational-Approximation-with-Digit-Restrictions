import Formalization.AnnulusCounting
import Formalization.BakerLowerBound
import Formalization.ExponentialContradiction
import Formalization.NumericalEstimates
import Formalization.GlobalScale

/-!
# The analytic estimate over `𝔇_b⋆`

This module assembles the proof of `DigitRestricted.StarEstimate`.  The proof
has been split into independently checked layers:

* finite digit blocks (`BoundedDigits`),
* distance-to-integer and annulus propagation (`CircleDistance`, `Annuli`),
* Olson's small-frequency estimate (`SmallFrequencies`),
* exponential products and digit-sum decay (`ExponentialProduct`,
  `DigitSumUpper`, `AnnulusCounting`), and
* the explicit Fejér certificate replacing the cited Baker bound
  (`BakerLowerBound`).

No additional analytic-number-theory statement is postulated here.
-/

open scoped BigOperators

noncomputable section

namespace DigitRestricted

/-- The inverse-square logarithmic estimate over the enlarged digit set. -/
theorem starEstimate {b : ℕ} (hb : 2 ≤ b) : StarEstimate b := by
  rcases starApproximation_at_digit_scale hb with ⟨J, hJ, hscaleApprox⟩
  let T : ℕ := b ^ (2 * J + 1) + 1
  let Csmall : ℝ := (((T : ℝ) * Real.log (b : ℝ)) ^ 2) / 2
  let Clarge : ℝ :=
    2 * ((b ^ (4 * J + 3) : ℕ) : ℝ) * (Real.log (b : ℝ)) ^ 2
  let C : ℝ := 1 + Csmall + Clarge
  have hlogb : 0 < Real.log (b : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < b by omega)
  have hCsmall : 0 ≤ Csmall := by dsimp [Csmall]; positivity
  have hClarge : 0 ≤ Clarge := by dsimp [Clarge]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro γ N hN
  let t : ℕ := Nat.log b N
  let r : ℕ := t - 1
  have hNpos : N ≠ 0 := by omega
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hlogNat := realLog_lt_natLog_succ_mul hb (show 1 ≤ N by omega)
  by_cases ht : T ≤ t
  · have htlarge : b ^ (2 * J + 1) ≤ r := by
      dsimp [T, r] at ht ⊢
      omega
    rcases hscaleApprox γ r htlarge with ⟨n, hnup, hnne, hn⟩
    have hnN : n ≤ N := by
      calc
        n ≤ b ^ (r + 1) := hnup.le_pow_succ hb
        _ = b ^ t := by dsimp [r]; congr 1; omega
        _ ≤ N := by
          dsimp [t]
          exact Nat.pow_log_le_self b hNpos
    refine ⟨n, Nat.one_le_iff_ne_zero.mpr hnne, hnN,
      hnup.isDigitRestrictedStar, ?_⟩
    let C₀ : ℝ := (((b ^ (4 * J + 3) : ℕ) : ℝ) / 2)
    have hrpos : 0 < r := by
      have : 1 ≤ b ^ (2 * J + 1) := Nat.one_le_pow _ _ (by omega)
      omega
    have htEq : r + 1 = t := by dsimp [r]; omega
    have htBound : t + 1 ≤ 2 * r := by
      have hpowTwo : 2 ≤ b ^ (2 * J + 1) := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * J + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ b ^ (2 * J + 1) := Nat.pow_le_pow_left hb (2 * J + 1)
      omega
    have hlogUpper : Real.log (N : ℝ) ≤
        2 * (r : ℝ) * Real.log (b : ℝ) := by
      have htReal : ((t + 1 : ℕ) : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast htBound
      calc
        Real.log (N : ℝ) ≤ ((t + 1 : ℕ) : ℝ) * Real.log (b : ℝ) := by
          simpa [t] using hlogNat.le
        _ ≤ (2 * (r : ℝ)) * Real.log (b : ℝ) :=
          mul_le_mul_of_nonneg_right htReal hlogb.le
        _ = 2 * (r : ℝ) * Real.log (b : ℝ) := by ring
    have hsqlog : (Real.log (N : ℝ)) ^ 2 ≤
        4 * (r : ℝ) ^ 2 * (Real.log (b : ℝ)) ^ 2 := by
      have hright : 0 ≤ 2 * (r : ℝ) * Real.log (b : ℝ) := by positivity
      have hsquare := (sq_le_sq₀ hlogN.le hright).2 hlogUpper
      nlinarith
    have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
    have hcross : C₀ * (Real.log (N : ℝ)) ^ 2 ≤
        Clarge * (r : ℝ) ^ 2 := by
      calc
        C₀ * (Real.log (N : ℝ)) ^ 2 ≤
            C₀ * (4 * (r : ℝ) ^ 2 * (Real.log (b : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsqlog hC₀
        _ = Clarge * (r : ℝ) ^ 2 := by dsimp [C₀, Clarge]; ring
    have hfrac : C₀ / (r : ℝ) ^ 2 ≤
        Clarge / (Real.log (N : ℝ)) ^ 2 := by
      exact (div_le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast hrpos))
        (sq_pos_of_pos hlogN)).2 hcross
    have hClargeC : Clarge ≤ C := by dsimp [C]; linarith
    calc
      circleNorm (γ * n) ≤ C₀ / (r : ℝ) ^ 2 := by simpa [C₀] using hn
      _ ≤ Clarge / (Real.log (N : ℝ)) ^ 2 := hfrac
      _ ≤ C / (Real.log (N : ℝ)) ^ 2 := by gcongr
  · have htSmall : t < T := by omega
    have htBound : t + 1 ≤ T := by omega
    have hlogUpper : Real.log (N : ℝ) ≤
        (T : ℝ) * Real.log (b : ℝ) := by
      have htReal : ((t + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast htBound
      calc
        Real.log (N : ℝ) ≤ ((t + 1 : ℕ) : ℝ) * Real.log (b : ℝ) := by
          simpa [t] using hlogNat.le
        _ ≤ (T : ℝ) * Real.log (b : ℝ) :=
          mul_le_mul_of_nonneg_right htReal hlogb.le
    have hright : 0 ≤ (T : ℝ) * Real.log (b : ℝ) := by positivity
    have hsqlog : (Real.log (N : ℝ)) ^ 2 ≤
        ((T : ℝ) * Real.log (b : ℝ)) ^ 2 :=
      (sq_le_sq₀ hlogN.le hright).2 hlogUpper
    have hsmallC : Csmall ≤ C := by dsimp [C]; linarith
    have hhalf : (1 : ℝ) / 2 ≤ C / (Real.log (N : ℝ)) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hlogN)).2
      calc
        (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
            (1 / 2 : ℝ) * ((T : ℝ) * Real.log (b : ℝ)) ^ 2 := by gcongr
        _ = Csmall := by dsimp [Csmall]; ring
        _ ≤ C := hsmallC
    refine ⟨1, by omega, by omega, Or.inl (one_isDigitRestricted b), ?_⟩
    simpa using (circleNorm_le_half γ).trans hhalf

end DigitRestricted
