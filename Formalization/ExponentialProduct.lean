import Formalization.BoundedDigits
import Formalization.CircleDistance

/-!
# Exponential products for digit sums

This module formalizes the algebraic product expansion behind the paper's
lemma `Prodbound`, together with a convenient quadratic cosine bound.  The
constant `2` below is slightly weaker than the paper's displayed constant
`π`, but is positive and is fully sufficient for the decay argument.
-/

open scoped BigOperators

noncomputable section

namespace DigitRestricted

@[simp] theorem e_zero : e 0 = 1 := by
  simp [e]

@[simp] theorem e_neg (x : ℝ) : e (-x) = (e x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← e_add, neg_add_cancel, e_zero]

theorem prod_e_eq_e_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, e (f i) = e (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih, e_add]

/-- Euler's cosine identity in the normalization `e(x) = exp(2πix)`. -/
theorem e_add_e_neg (x : ℝ) :
    e x + e (-x) = ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) := by
  rw [e, e]
  have hneg : ((((2 * Real.pi * -x : ℝ) : ℂ) * Complex.I)) =
      ((((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [hneg]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  simp
  ring

/-- The norm of one binary digit factor. -/
theorem norm_one_add_e (x : ℝ) :
    ‖(1 : ℂ) + e x‖ = 2 * |Real.cos (Real.pi * x)| := by
  have hfactor : (1 : ℂ) + e x =
      e (x / 2) * ((2 * Real.cos (Real.pi * x) : ℝ) : ℂ) := by
    have hone : e (x / 2) * e (-x / 2) = 1 := by
      rw [← e_add]
      convert e_zero using 2 <;> ring
    calc
      (1 : ℂ) + e x = e (x / 2) * e (-x / 2) + e (x / 2) * e (x / 2) := by
        rw [hone, ← e_add]
        congr 2
        ring
      _ = e (x / 2) * (e (-x / 2) + e (x / 2)) := by ring
      _ = e (x / 2) * ((2 * Real.cos (Real.pi * x) : ℝ) : ℂ) := by
        rw [add_comm]
        rw [show -x / 2 = -(x / 2) by ring, e_add_e_neg]
        congr 3
        ring
  rw [hfactor, norm_mul, e_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- Absolute cosine is controlled by the nearest-integer distance. -/
theorem abs_cos_pi_le_one_sub_two_circleNorm_sq (x : ℝ) :
    |Real.cos (Real.pi * x)| ≤ 1 - 2 * circleNorm x ^ 2 := by
  let δ : ℝ := x - (round x : ℝ)
  have hδ : |δ| = circleNorm x := by rfl
  have hδhalf : |δ| ≤ 1 / 2 := by simpa [hδ] using circleNorm_le_half x
  have hangle : |Real.pi * δ| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hangleHalf : -(Real.pi / 2) ≤ Real.pi * δ ∧
      Real.pi * δ ≤ Real.pi / 2 := by
    rw [abs_le] at hδhalf
    constructor <;> nlinarith [Real.pi_pos]
  have hcosNonneg : 0 ≤ Real.cos (Real.pi * δ) :=
    Real.cos_nonneg_of_mem_Icc hangleHalf
  have hperiodic : |Real.cos (Real.pi * x)| = |Real.cos (Real.pi * δ)| := by
    have h := Real.cos_sub_int_mul_pi (Real.pi * x) (round x)
    have harg : Real.pi * x - (round x : ℝ) * Real.pi = Real.pi * δ := by
      dsimp [δ]
      ring
    rw [harg] at h
    rw [h]
    simp
  rw [hperiodic, abs_of_nonneg hcosNonneg]
  calc
    Real.cos (Real.pi * δ) ≤
        1 - 2 / Real.pi ^ 2 * (Real.pi * δ) ^ 2 :=
      Real.cos_le_one_sub_mul_cos_sq hangle
    _ = 1 - 2 * circleNorm x ^ 2 := by
      rw [← hδ]
      rw [sq_abs]
      field_simp [Real.pi_ne_zero]

theorem one_sub_two_circleNorm_sq_nonneg (x : ℝ) :
    0 ≤ 1 - 2 * circleNorm x ^ 2 := by
  have h := circleNorm_le_half x
  have h0 := circleNorm_nonneg x
  nlinarith [sq_nonneg (circleNorm x)]

/-- The exact binary-digit product expansion. -/
theorem digitCharacterSum_eq_prod (b r : ℕ) (k γ : ℝ) :
    (∑ s ∈ digitSubsets r, e (k * (digitValue b s : ℝ) * γ)) =
      ∏ d ∈ Finset.range (r + 1), (1 + e (k * (b : ℝ) ^ d * γ)) := by
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro s hs
  rw [prod_e_eq_e_sum]
  congr 2
  dsimp [digitValue]
  rw [Nat.cast_sum]
  simp_rw [Nat.cast_pow]
  rw [Finset.mul_sum, Finset.sum_mul]

/-- `Prodbound`, with the harmless coefficient `2` in place of `π`. -/
theorem productBound (b r : ℕ) (k γ : ℝ) :
    ‖∑ s ∈ digitSubsets r, e (k * (digitValue b s : ℝ) * γ)‖ ≤
      (2 : ℝ) ^ (r + 1) *
        ∏ d ∈ Finset.range (r + 1),
          (1 - 2 * circleNorm (k * (b : ℝ) ^ d * γ) ^ 2) := by
  rw [digitCharacterSum_eq_prod]
  calc
    ‖∏ d ∈ Finset.range (r + 1), (1 + e (k * (b : ℝ) ^ d * γ))‖ ≤
        ∏ d ∈ Finset.range (r + 1),
          ‖(1 : ℂ) + e (k * (b : ℝ) ^ d * γ)‖ :=
      Finset.norm_prod_le _ _
    _ = ∏ d ∈ Finset.range (r + 1),
          (2 * |Real.cos (Real.pi * (k * (b : ℝ) ^ d * γ))|) := by
      apply Finset.prod_congr rfl
      intro d hd
      exact norm_one_add_e _
    _ ≤ ∏ d ∈ Finset.range (r + 1),
          (2 * (1 - 2 * circleNorm (k * (b : ℝ) ^ d * γ) ^ 2)) := by
      apply Finset.prod_le_prod₀
      · intro d hd
        positivity
      · intro d hd
        gcongr
        exact abs_cos_pi_le_one_sub_two_circleNorm_sq _
    _ = (2 : ℝ) ^ (r + 1) *
        ∏ d ∈ Finset.range (r + 1),
          (1 - 2 * circleNorm (k * (b : ℝ) ^ d * γ) ^ 2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

end DigitRestricted
