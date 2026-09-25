import Mathlib

/-!
# Rational approximation with digit-restricted denominators

This file formalizes the statement labelled `main1` in the source paper and
the exact reduction from the enlarged digit set used in its proof.

The source documents are treated only as mathematical input. Olson's
Corollary 3.2.1 is the sole external result recorded as an axiom below.
-/

open scoped BigOperators

noncomputable section

namespace DigitRestricted

/-- Distance from a real number to the nearest integer. -/
def circleNorm (x : ℝ) : ℝ := |x - (round x : ℝ)|

/-- Natural numbers whose base-`b` expansion uses only the digits `0` and `1`.

The finite-set presentation is equivalent to the usual digit-expansion
definition when `2 ≤ b`, and is substantially more convenient for sums. -/
def IsDigitRestricted (b n : ℕ) : Prop :=
  ∃ s : Finset ℕ, n = ∑ i ∈ s, b ^ i

/-- The enlarged set `𝔇_b⋆` from the paper. -/
def IsDigitRestrictedStar (b n : ℕ) : Prop :=
  IsDigitRestricted b n ∨ ∃ c d : ℕ, c < d ∧ n = b ^ d - b ^ c

/-- The witness form of the minimum appearing in the paper. -/
def HasApproximation (P : ℕ → Prop) (γ : ℝ) (N : ℕ) (A : ℝ) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ P n ∧ circleNorm (γ * n) ≤ A

/-- A direct formal statement of Theorem `main1`.

`N ≥ 2` is made explicit: the displayed expression in the paper contains
`(log N)⁻²`, which is not meaningful at `N = 1` in ordinary mathematical
notation. -/
def Main1Statement (b : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (N : ℕ), 2 ≤ N →
    HasApproximation (IsDigitRestricted b) γ N (C / (Real.log N) ^ 2)

/-- The intermediate estimate over the enlarged set `𝔇_b⋆`. -/
def StarEstimate (b : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (N : ℕ), 2 ≤ N →
    HasApproximation (IsDigitRestrictedStar b) γ N (C / (Real.log N) ^ 2)

/-! ## The permitted Olson assumption -/

/-- Olson, Corollary 3.2.1, in the zero-sum form used by `Addcomb`.

The inequality `9 * |G| ≤ |S|²` is the squared, natural-number version of
`|S| ≥ 3 * sqrt |G|`. The corollary says that a sufficiently large set of
distinct nonzero elements of a finite additive group has a nonempty subset
whose sum is zero.
-/
axiom olsonCorollary
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (hzero : 0 ∉ S)
    (hlarge : 9 * Fintype.card G ≤ S.card ^ 2) :
    ∃ T : Finset G, T.Nonempty ∧ T ⊆ S ∧ ∑ x ∈ T, x = 0

/-- The specialized zero-sum lemma labelled `Addcomb` in the source paper.

Writing the input as a finset of residues makes distinctness modulo `k`
structural rather than an additional side condition. -/
theorem addcomb (k : ℕ) (hk : 1 ≤ k) (S : Finset (ZMod k))
    (hlarge : 9 * k ≤ S.card ^ 2) :
    ∃ T : Finset (ZMod k), T.Nonempty ∧ T ⊆ S ∧ ∑ x ∈ T, x = 0 := by
  let _ : NeZero k := ⟨by omega⟩
  by_cases hzero : (0 : ZMod k) ∈ S
  · exact ⟨{0}, Finset.singleton_nonempty 0, Finset.singleton_subset_iff.mpr hzero, by simp⟩
  · apply olsonCorollary S hzero
    simpa [ZMod.card] using hlarge

/-! ## Exponential-sum interface supplied by mathlib -/

/-- The standard analytic-number-theory character `e(x) = exp(2πix)`. -/
def e (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

@[simp] theorem e_norm (x : ℝ) : ‖e x‖ = 1 := by
  simpa [e] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

@[simp] theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  rw [e, e, e]
  rw [show ((((2 * Real.pi * (x + y) : ℝ) : ℂ) * Complex.I)) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) +
        (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_add _ _

/-! ## Elementary infrastructure -/

@[simp] theorem circleNorm_nonneg (x : ℝ) : 0 ≤ circleNorm x := by
  simp [circleNorm]

theorem circleNorm_le_abs_sub_int (x : ℝ) (z : ℤ) :
    circleNorm x ≤ |x - (z : ℝ)| := by
  simpa [circleNorm] using (round_le x z)

theorem circleNorm_nat_mul_le (x : ℝ) (k : ℕ) :
    circleNorm (k * x) ≤ k * circleNorm x := by
  calc
    circleNorm (k * x) ≤ |k * x - ((k : ℤ) * round x : ℤ)| :=
      circleNorm_le_abs_sub_int _ _
    _ = k * circleNorm x := by
      push_cast
      rw [show (k : ℝ) * x - (k : ℝ) * (round x : ℝ) =
          (k : ℝ) * (x - (round x : ℝ)) by ring]
      simp [circleNorm, abs_mul]

@[simp] theorem one_isDigitRestricted (b : ℕ) : IsDigitRestricted b 1 := by
  refine ⟨{0}, ?_⟩
  simp

theorem geomBlock_isDigitRestricted (b c d : ℕ) :
    IsDigitRestricted b (∑ i ∈ Finset.Ico c d, b ^ i) := by
  exact ⟨Finset.Ico c d, rfl⟩

theorem geomBlock_pos {b c d : ℕ} (hb : 2 ≤ b) (hcd : c < d) :
    0 < ∑ i ∈ Finset.Ico c d, b ^ i := by
  have hc : c ∈ Finset.Ico c d := by simp [hcd]
  exact Finset.sum_pos (fun _ _ ↦ pow_pos (Nat.zero_lt_of_lt hb) _) ⟨c, hc⟩

theorem geomBlock_mul {b c d : ℕ} (hb : 2 ≤ b) (hcd : c ≤ d) :
    (b - 1) * (∑ i ∈ Finset.Ico c d, b ^ i) = b ^ d - b ^ c := by
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ b)]
  rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega : 0 < b) hcd)]
  simpa [mul_comm] using (geom_sum_Ico_mul (b : ℤ) hcd)

/-! ## Reduction from `𝔇_b⋆` to `𝔇_b` -/

/-- Lemma `Db*` from the paper, specialized to the inverse-square-log bound
needed for `main1`. -/
theorem main1_of_starEstimate {b : ℕ} (hb : 2 ≤ b) (hstar : StarEstimate b) :
    Main1Statement b := by
  rcases hstar with ⟨C, hC, hstar⟩
  have hbsub_nat : 1 ≤ b - 1 := by omega
  have hbsub_pos : 0 < ((b - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < b - 1 by omega)
  refine ⟨((b - 1 : ℕ) : ℝ) * C, mul_pos hbsub_pos hC, ?_⟩
  intro γ N hN
  have hbsub_real : (1 : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := by exact_mod_cast hbsub_nat
  have hbsub_ne : ((b - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hbsub_pos
  have hlog : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hden : 0 < (Real.log (N : ℝ)) ^ 2 := sq_pos_of_pos hlog
  have hA : 0 < C / (Real.log (N : ℝ)) ^ 2 := div_pos hC hden
  rcases hstar (γ / ((b - 1 : ℕ) : ℝ)) N hN with ⟨n, hn1, hnN, hnstar, hn⟩
  rcases hnstar with hnDigit | ⟨c, d, hcd, hnEq⟩
  · refine ⟨n, hn1, hnN, hnDigit, ?_⟩
    have hscale := circleNorm_nat_mul_le
      ((γ / ((b - 1 : ℕ) : ℝ)) * n) (b - 1)
    have hmul : ((b - 1 : ℕ) : ℝ) *
        ((γ / ((b - 1 : ℕ) : ℝ)) * n) = γ * n := by
      field_simp [hbsub_ne]
    rw [hmul] at hscale
    calc
      circleNorm (γ * n) ≤ (b - 1 : ℕ) *
          circleNorm ((γ / ((b - 1 : ℕ) : ℝ)) * n) := hscale
      _ ≤ (b - 1 : ℕ) * (C / (Real.log (N : ℝ)) ^ 2) := by
        gcongr
      _ = (((b - 1 : ℕ) : ℝ) * C) / (Real.log (N : ℝ)) ^ 2 := by ring
  · let q : ℕ := ∑ i ∈ Finset.Ico c d, b ^ i
    have hqDigit : IsDigitRestricted b q := geomBlock_isDigitRestricted b c d
    have hqPos : 0 < q := geomBlock_pos hb hcd
    have hgeom : (b - 1) * q = b ^ d - b ^ c := geomBlock_mul hb hcd.le
    have hnFactor : n = (b - 1) * q := hnEq.trans hgeom.symm
    have hqN : q ≤ N := by
      apply le_trans ?_ hnN
      rw [hnFactor]
      exact Nat.le_mul_of_pos_left q (by omega)
    refine ⟨q, hqPos, hqN, hqDigit, ?_⟩
    have harg : (γ / ((b - 1 : ℕ) : ℝ)) * n = γ * q := by
      rw [hnFactor]
      push_cast
      field_simp [hbsub_ne]
    rw [harg] at hn
    calc
      circleNorm (γ * q) ≤ C / (Real.log (N : ℝ)) ^ 2 := hn
      _ ≤ (b - 1 : ℕ) * (C / (Real.log (N : ℝ)) ^ 2) := by
        nlinarith
      _ = (((b - 1 : ℕ) : ℝ) * C) / (Real.log (N : ℝ)) ^ 2 := by ring

end DigitRestricted
