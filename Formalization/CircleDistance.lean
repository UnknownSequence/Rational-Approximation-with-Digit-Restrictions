import Formalization.Core

/-!
# Distance to the nearest integer

Elementary facts about `circleNorm`, isolated from the exponential-sum
argument.  The additive circle already available in mathlib supplies the key
local-isometry fact used in the paper's `IntegerDistanceLemma`.
-/

noncomputable section

namespace DigitRestricted

/-- `circleNorm` is the norm on the unit additive circle. -/
theorem circleNorm_eq_unitAddCircle_norm (x : ℝ) :
    circleNorm x = ‖(x : UnitAddCircle)‖ := by
  simpa [circleNorm] using (UnitAddCircle.norm_eq (x := x)).symm

/-- The nearest-integer distance always lies in `[0, 1/2]`. -/
theorem circleNorm_le_half (x : ℝ) : circleNorm x ≤ 1 / 2 := by
  rw [circleNorm, abs_sub_round_eq_min]
  rcases le_total (Int.fract x) (1 / 2 : ℝ) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

/-- Nearest-integer distance is invariant under integer translation. -/
@[simp] theorem circleNorm_add_int (x : ℝ) (z : ℤ) :
    circleNorm (x + z) = circleNorm x := by
  simp only [circleNorm, round_add_intCast]
  push_cast
  congr 1
  ring

@[simp] theorem circleNorm_int_add (z : ℤ) (x : ℝ) :
    circleNorm (z + x) = circleNorm x := by
  rw [add_comm, circleNorm_add_int]

@[simp] theorem circleNorm_neg (x : ℝ) : circleNorm (-x) = circleNorm x := by
  rw [circleNorm_eq_unitAddCircle_norm, circleNorm_eq_unitAddCircle_norm]
  change ‖-(x : UnitAddCircle)‖ = ‖(x : UnitAddCircle)‖
  exact norm_neg _

/-- On the central interval, quotienting by the integers does not change the
absolute value.  The endpoints are included. -/
theorem circleNorm_eq_abs_of_abs_le_half {x : ℝ} (hx : |x| ≤ 1 / 2) :
    circleNorm x = |x| := by
  rw [circleNorm_eq_unitAddCircle_norm]
  exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 (by simpa using hx)

/-- Multiplication by a natural number scales nearest-integer distance exactly
as long as the result stays in the central half-interval. -/
theorem circleNorm_nat_mul_eq {x : ℝ} {k : ℕ}
    (hsmall : (k : ℝ) * circleNorm x ≤ 1 / 2) :
    circleNorm ((k : ℝ) * x) = (k : ℝ) * circleNorm x := by
  let z : ℤ := (k : ℤ) * round x
  have hrewrite : (k : ℝ) * x = (k : ℝ) * (x - (round x : ℝ)) + (z : ℝ) := by
    dsimp [z]
    push_cast
    ring
  rw [hrewrite, circleNorm_add_int]
  calc
    circleNorm ((k : ℝ) * (x - (round x : ℝ))) =
        |(k : ℝ) * (x - (round x : ℝ))| := by
      apply circleNorm_eq_abs_of_abs_le_half
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      simpa [circleNorm] using hsmall
    _ = (k : ℝ) * circleNorm x := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      rfl

/-- Triangle inequality for distance to the nearest integer. -/
theorem circleNorm_add_le (x y : ℝ) :
    circleNorm (x + y) ≤ circleNorm x + circleNorm y := by
  rw [circleNorm_eq_unitAddCircle_norm, circleNorm_eq_unitAddCircle_norm,
    circleNorm_eq_unitAddCircle_norm]
  change ‖(x : UnitAddCircle) + (y : UnitAddCircle)‖ ≤
    ‖(x : UnitAddCircle)‖ + ‖(y : UnitAddCircle)‖
  exact norm_add_le _ _

theorem circleNorm_finset_sum_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) :
    circleNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, circleNorm (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [circleNorm]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (circleNorm_add_le _ _).trans (add_le_add (le_refl _) ih)

/-- The annuli `G_b(t)` used to propagate a moderately large fractional part
along multiplication by the base. -/
def InAnnulus (b t : ℕ) (y : ℝ) : Prop :=
  1 / (2 * (b : ℝ) ^ t) < circleNorm y ∧
    circleNorm y ≤ 1 / (2 * (b : ℝ) ^ (t - 1))

/-- The paper's `IntegerDistanceLemma`. -/
theorem integerDistanceLemma {b t : ℕ} (hb : 2 ≤ b) (ht : 2 ≤ t) {y : ℝ}
    (hy : InAnnulus b t y) : InAnnulus b (t - 1) ((b : ℝ) * y) := by
  have hbpos : (0 : ℝ) < b := by positivity
  have hbone : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hpowpos (n : ℕ) : (0 : ℝ) < (b : ℝ) ^ n := pow_pos hbpos n
  have hscale : circleNorm ((b : ℝ) * y) = (b : ℝ) * circleNorm y := by
    apply circleNorm_nat_mul_eq
    calc
      (b : ℝ) * circleNorm y ≤ (b : ℝ) * (1 / (2 * (b : ℝ) ^ (t - 1))) :=
        mul_le_mul_of_nonneg_left hy.2 (Nat.cast_nonneg b)
      _ = 1 / (2 * (b : ℝ) ^ (t - 2)) := by
        rw [show t - 1 = (t - 2) + 1 by omega, pow_succ]
        field_simp
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (b : ℝ) ^ (t - 2))]
        have : (1 : ℝ) ≤ (b : ℝ) ^ (t - 2) := one_le_pow₀ hbone
        nlinarith
  constructor
  · rw [hscale]
    have hy1 := hy.1
    rw [show t = (t - 1) + 1 by omega, pow_succ] at hy1
    have := mul_lt_mul_of_pos_left hy1 hbpos
    field_simp at this ⊢
    nlinarith
  · rw [hscale]
    rw [show t - 1 - 1 = t - 2 by omega]
    calc
      (b : ℝ) * circleNorm y ≤ (b : ℝ) * (1 / (2 * (b : ℝ) ^ (t - 1))) :=
        mul_le_mul_of_nonneg_left hy.2 (Nat.cast_nonneg b)
      _ = 1 / (2 * (b : ℝ) ^ (t - 2)) := by
        rw [show t - 1 = (t - 2) + 1 by omega, pow_succ]
        field_simp

end DigitRestricted
