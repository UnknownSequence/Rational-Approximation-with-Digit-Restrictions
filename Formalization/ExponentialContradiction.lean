import Formalization.AnnulusCounting
import Formalization.BakerLowerBound

/-!
# The finite exponential-sum contradiction

This file joins the two analytic halves of the argument.  The Fejér
certificate gives a lower bound for the total positive-frequency mass, while
the digit product gives an upper bound for every summand.  Keeping this bridge
separate makes the remaining work purely numerical: use the Olson/annulus
count to show that the displayed upper bound is too small when `r` is large.
-/

open scoped BigOperators

noncomputable section

namespace DigitRestricted

/-- The Fourier sum over the nonzero finite digit block is exactly the digit
character sum used by the product estimate. -/
theorem naturalFourierSum_digitBlock (b r k : ℕ) (γ : ℝ) :
    naturalFourierSum ((digitSubsets r).erase ∅)
        (fun s ↦ γ * (digitValue b s : ℝ)) k =
      ∑ s ∈ (digitSubsets r).erase ∅,
        e ((k : ℝ) * (digitValue b s : ℝ) * γ) := by
  apply Finset.sum_congr rfl
  intro s hs
  apply congrArg e
  ring

/-- Baker/Fejér lower bound specialized to the nonzero digit block. -/
theorem digitBlock_fourierMass_lower
    {b r m : ℕ} (hb : 2 ≤ b) (γ : ℝ)
    (havoid : ∀ n : ℕ, IsDigitRestrictedStarUpTo b r n → n ≠ 0 →
      1 / (2 * (b : ℝ) ^ m) < circleNorm (γ * n)) :
    ((2 : ℕ) ^ (r + 1) - 1 : ℕ) /
        (5 * ((2 * b ^ m : ℕ) : ℝ)) ≤
      positiveFrequencyMass ((digitSubsets r).erase ∅)
        (fun s ↦ γ * (digitValue b s : ℝ)) (4 * b ^ m) := by
  let D := (digitSubsets r).erase ∅
  let x : Finset ℕ → ℝ := fun s ↦ γ * (digitValue b s : ℝ)
  let M : ℕ := 2 * b ^ m
  have hM : 1 ≤ M := by
    dsimp [M]
    have : 0 < b ^ m := pow_pos (by omega) m
    omega
  have hx : ∀ s ∈ D, 1 / (M : ℝ) ≤ circleNorm (x s) := by
    intro s hs
    have hserase := Finset.mem_erase.mp hs
    have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hserase.1
    have hnup : IsDigitRestrictedUpTo b r (digitValue b s) :=
      digitValue_mem_upTo hserase.2
    have hnne : digitValue b s ≠ 0 := digitValue_ne_zero (by omega) hsne
    have h := (havoid (digitValue b s) (Or.inl hnup) hnne).le
    simpa [M, x, Nat.cast_mul, Nat.cast_pow] using h
  have hlower := bakerLowerBoundFejer D x hM hx
  have hcard : D.card = 2 ^ (r + 1) - 1 := by
    simpa [D] using digitSubsets_erase_empty_card r
  have hfrequency : 2 * M = 4 * b ^ m := by
    dsimp [M]
    omega
  rw [hfrequency] at hlower
  simpa [D, x, M, hcard, mul_assoc] using hlower

/-- The product estimate, summed over the frequency interval used by the
Fejér lower bound. -/
theorem digitBlock_fourierMass_upper {b r B : ℕ} (hb : 2 ≤ b) (γ : ℝ) :
    positiveFrequencyMass ((digitSubsets r).erase ∅)
        (fun s ↦ γ * (digitValue b s : ℝ)) B ≤
      ∑ k ∈ Finset.Icc 1 B,
        (1 + (2 : ℝ) ^ (r + 1) *
          baseDecay b ^ (firstAnnulusPositions b r k γ).card) := by
  rw [positiveFrequencyMass]
  apply Finset.sum_le_sum
  intro k hk
  rw [naturalFourierSum_digitBlock]
  exact digitCharacterSum_erase_empty_upper hb γ

/-- A uniform version of the upper bound after inserting the Olson/annulus
count.  The auxiliary integer `L` is the number of decay factors retained in
each frequency. -/
theorem digitBlock_fourierMass_upper_uniform
    {b r m L : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (γ : ℝ)
    (havoid : ∀ n : ℕ, IsDigitRestrictedStarUpTo b r n → n ≠ 0 →
      1 / (2 * (b : ℝ) ^ m) < circleNorm (γ * n))
    (hscale : L * m + m + 6 * b ^ ((m + 1) / 2) ≤ r + 1) :
    positiveFrequencyMass ((digitSubsets r).erase ∅)
        (fun s ↦ γ * (digitValue b s : ℝ)) (4 * b ^ m) ≤
      ((4 * b ^ m : ℕ) : ℝ) *
        (1 + (2 : ℝ) ^ (r + 1) * baseDecay b ^ L) := by
  have hupper := digitBlock_fourierMass_upper (r := r) (B := 4 * b ^ m) hb γ
  have hq0 : 0 ≤ baseDecay b := baseDecay_nonneg hb
  have hq1 : baseDecay b ≤ 1 := baseDecay_le_one b
  calc
    positiveFrequencyMass ((digitSubsets r).erase ∅)
        (fun s ↦ γ * (digitValue b s : ℝ)) (4 * b ^ m) ≤
        ∑ k ∈ Finset.Icc 1 (4 * b ^ m),
          (1 + (2 : ℝ) ^ (r + 1) *
            baseDecay b ^ (firstAnnulusPositions b r k γ).card) := hupper
    _ ≤ ∑ _k ∈ Finset.Icc 1 (4 * b ^ m),
          (1 + (2 : ℝ) ^ (r + 1) * baseDecay b ^ L) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkparts := Finset.mem_Icc.mp hk
      have hW : L ≤ (firstAnnulusPositions b r k γ).card :=
        firstAnnulus_card_ge_uniform hb hkparts.1 hkparts.2 hm havoid hscale
      have hpow := pow_le_pow_of_le_one hq0 hq1 hW
      gcongr
    _ = ((4 * b ^ m : ℕ) : ℝ) *
          (1 + (2 : ℝ) ^ (r + 1) * baseDecay b ^ L) := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
      ring

/-- The exact finite inequality that must fail in the large-scale regime.
All analytic and additive-combinatorial inputs are now upstream theorems; the
remaining comparison is an elementary estimate of the annulus exponents. -/
theorem digitBlock_contradiction_inequality
    {b r m : ℕ} (hb : 2 ≤ b) (γ : ℝ)
    (havoid : ∀ n : ℕ, IsDigitRestrictedStarUpTo b r n → n ≠ 0 →
      1 / (2 * (b : ℝ) ^ m) < circleNorm (γ * n)) :
    ((2 : ℕ) ^ (r + 1) - 1 : ℕ) /
        (5 * ((2 * b ^ m : ℕ) : ℝ)) ≤
      ∑ k ∈ Finset.Icc 1 (4 * b ^ m),
        (1 + (2 : ℝ) ^ (r + 1) *
          baseDecay b ^ (firstAnnulusPositions b r k γ).card) := by
  exact (digitBlock_fourierMass_lower hb γ havoid).trans
    (digitBlock_fourierMass_upper hb γ)

/-- Lower and upper bounds combined after a uniform annulus count. -/
theorem digitBlock_uniform_contradiction_inequality
    {b r m L : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (γ : ℝ)
    (havoid : ∀ n : ℕ, IsDigitRestrictedStarUpTo b r n → n ≠ 0 →
      1 / (2 * (b : ℝ) ^ m) < circleNorm (γ * n))
    (hscale : L * m + m + 6 * b ^ ((m + 1) / 2) ≤ r + 1) :
    ((2 : ℕ) ^ (r + 1) - 1 : ℕ) /
        (5 * ((2 * b ^ m : ℕ) : ℝ)) ≤
      ((4 * b ^ m : ℕ) : ℝ) *
        (1 + (2 : ℝ) ^ (r + 1) * baseDecay b ^ L) := by
  exact (digitBlock_fourierMass_lower hb γ havoid).trans
    (digitBlock_fourierMass_upper_uniform hb hm γ havoid hscale)

/-- Once the remaining elementary numerical comparison is supplied, the
finite approximation asserted by the paper follows immediately. -/
theorem exists_starUpTo_approximation_of_gap
    {b r m L : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (γ : ℝ)
    (hscale : L * m + m + 6 * b ^ ((m + 1) / 2) ≤ r + 1)
    (hgap : ((4 * b ^ m : ℕ) : ℝ) *
        (1 + (2 : ℝ) ^ (r + 1) * baseDecay b ^ L) <
      ((2 : ℕ) ^ (r + 1) - 1 : ℕ) /
        (5 * ((2 * b ^ m : ℕ) : ℝ))) :
    ∃ n : ℕ, IsDigitRestrictedStarUpTo b r n ∧ n ≠ 0 ∧
      circleNorm (γ * n) ≤ 1 / (2 * (b : ℝ) ^ m) := by
  by_contra hnone
  push_neg at hnone
  have havoid : ∀ n : ℕ, IsDigitRestrictedStarUpTo b r n → n ≠ 0 →
      1 / (2 * (b : ℝ) ^ m) < circleNorm (γ * n) := by
    intro n hnstar hnne
    exact hnone n hnstar hnne
  have himpossible := digitBlock_uniform_contradiction_inequality
    hb hm γ havoid hscale
  exact (not_lt_of_ge himpossible) hgap

end DigitRestricted
