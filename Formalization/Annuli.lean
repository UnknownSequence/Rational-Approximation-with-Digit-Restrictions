import Formalization.CircleDistance

/-!
# Annulus propagation

This file packages the scale-selection and iteration used in `main-1`.
Every nonzero nearest-integer distance above `1/(2b^m)` lies in one of the
first `m` annuli, and multiplication by `b` carries that annulus down to the
first one.
-/

noncomputable section

namespace DigitRestricted

/-- Select an annulus among the first `m` scales. -/
theorem exists_annulus {b m : ℕ} (_hb : 2 ≤ b) (hm : 1 ≤ m) {y : ℝ}
    (hy : 1 / (2 * (b : ℝ) ^ m) < circleNorm y) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ m ∧ InAnnulus b t y := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hu : circleNorm y ≤ 1 / (2 * (b : ℝ) ^ (m - 1))
      · exact ⟨m, hm, le_rfl, hy, hu⟩
      · have hm2 : 2 ≤ m := by
          by_contra hnot
          have hm1 : m = 1 := by omega
          subst m
          simp only [Nat.reduceSubDiff, pow_zero, mul_one] at hu
          exact hu (circleNorm_le_half y)
        have hmone : 1 ≤ m - 1 := by omega
        have hmlt : m - 1 < m := by omega
        rcases ih (m - 1) hmlt hmone (lt_of_not_ge hu) with ⟨t, ht1, htm, hty⟩
        exact ⟨t, ht1, htm.trans (by omega), hty⟩

/-- Iterating `IntegerDistanceLemma` sends the `t`-th annulus to the first. -/
theorem annulus_to_one {b t : ℕ} (hb : 2 ≤ b) (ht : 1 ≤ t) {y : ℝ}
    (hy : InAnnulus b t y) :
    InAnnulus b 1 ((b : ℝ) ^ (t - 1) * y) := by
  induction t using Nat.strong_induction_on generalizing y with
  | h t ih =>
      by_cases ht1 : t = 1
      · subst t
        simpa using hy
      · have ht2 : 2 ≤ t := by omega
        have hstep : InAnnulus b (t - 1) ((b : ℝ) * y) :=
          integerDistanceLemma hb ht2 hy
        have hrec := ih (t - 1) (by omega) (by omega) hstep
        have heq : (b : ℝ) ^ (t - 1) * y =
            (b : ℝ) ^ (t - 1 - 1) * ((b : ℝ) * y) := by
          rw [show t - 1 - 1 = t - 2 by omega,
            show t - 1 = (t - 2) + 1 by omega, pow_succ]
          ring
        rw [heq]
        exact hrec

/-- A large position reaches the first annulus after at most `m - 1` base
shifts. -/
theorem large_reaches_first_annulus {b m : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m)
    {y : ℝ} (hy : 1 / (2 * (b : ℝ) ^ m) < circleNorm y) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ m ∧
      InAnnulus b 1 ((b : ℝ) ^ (h - 1) * y) := by
  rcases exists_annulus hb hm hy with ⟨h, hh1, hhm, hhy⟩
  exact ⟨h, hh1, hhm, annulus_to_one hb hh1 hhy⟩

end DigitRestricted
