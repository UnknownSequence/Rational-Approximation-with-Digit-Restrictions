import Formalization.Annuli
import Formalization.ExponentialProduct
import Formalization.SmallFrequencies

/-!
# Upper bounds for the binary digit exponential sum

This module isolates the analytic consequence of having many positions in the
first annulus.  The remaining combinatorial task for `main-1` is to turn the
large-position count from `SmallFrequencies` into a lower bound for this first
annulus count.
-/

open scoped BigOperators

noncomputable section

namespace DigitRestricted

/-- Positions up to `r` which lie in the first base-`b` annulus. -/
def firstAnnulusPositions (b r k : ℕ) (γ : ℝ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (r + 1)).filter
      (fun d ↦ InAnnulus b 1 ((k : ℝ) * (b : ℝ) ^ d * γ))

@[simp] theorem mem_firstAnnulusPositions {b r k d : ℕ} {γ : ℝ} :
    d ∈ firstAnnulusPositions b r k γ ↔
      d ≤ r ∧ InAnnulus b 1 ((k : ℝ) * (b : ℝ) ^ d * γ) := by
  simp [firstAnnulusPositions]

/-- A fixed decay factor; our cosine inequality gives this slightly simpler
constant in place of the paper's `1 - π/(4b²)`. -/
def baseDecay (b : ℕ) : ℝ :=
  1 - 1 / (2 * (b : ℝ) ^ 2)

theorem baseDecay_nonneg {b : ℕ} (hb : 2 ≤ b) : 0 ≤ baseDecay b := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by positivity
  rw [baseDecay]
  rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < 2 * (b : ℝ) ^ 2)]
  nlinarith [sq_nonneg (b : ℝ)]

theorem baseDecay_le_one (b : ℕ) : baseDecay b ≤ 1 := by
  rw [baseDecay]
  have : 0 ≤ 1 / (2 * (b : ℝ) ^ 2) := by positivity
  linarith

/-- Each first-annulus position contributes one fixed factor of decay to the
product in `Prodbound`; all other factors are at most one. -/
theorem product_circleNorm_le_baseDecay_pow
    {b r k : ℕ} (hb : 2 ≤ b) (γ : ℝ) :
    (∏ d ∈ Finset.range (r + 1),
        (1 - 2 * circleNorm ((k : ℝ) * (b : ℝ) ^ d * γ) ^ 2)) ≤
      baseDecay b ^ (firstAnnulusPositions b r k γ).card := by
  let W := firstAnnulusPositions b r k γ
  let q := baseDecay b
  have hpoint : ∀ d ∈ Finset.range (r + 1),
      1 - 2 * circleNorm ((k : ℝ) * (b : ℝ) ^ d * γ) ^ 2 ≤
        if d ∈ W then q else 1 := by
    intro d hd
    by_cases hdW : d ∈ W
    · rw [if_pos hdW]
      have hann := (mem_firstAnnulusPositions.mp hdW).2
      have hlower := hann.1
      have hbpos : (0 : ℝ) < b := by positivity
      dsimp [q, baseDecay]
      have hnorm0 := circleNorm_nonneg ((k : ℝ) * (b : ℝ) ^ d * γ)
      have hthreshold : (0 : ℝ) < 1 / (2 * (b : ℝ)) := by positivity
      have hsquare : (1 / (2 * (b : ℝ))) ^ 2 <
          circleNorm ((k : ℝ) * (b : ℝ) ^ d * γ) ^ 2 :=
        (sq_lt_sq₀ hthreshold.le hnorm0).2 (by simpa using hlower)
      field_simp at hsquare ⊢
      nlinarith
    · rw [if_neg hdW]
      nlinarith [sq_nonneg (circleNorm ((k : ℝ) * (b : ℝ) ^ d * γ))]
  calc
    (∏ d ∈ Finset.range (r + 1),
        (1 - 2 * circleNorm ((k : ℝ) * (b : ℝ) ^ d * γ) ^ 2)) ≤
        ∏ d ∈ Finset.range (r + 1), (if d ∈ W then q else 1) := by
      apply Finset.prod_le_prod₀
      · intro d hd
        exact one_sub_two_circleNorm_sq_nonneg _
      · exact hpoint
    _ = q ^ W.card := by
      have hfilter : (Finset.range (r + 1)).filter (fun d ↦ d ∈ W) = W := by
        apply Finset.Subset.antisymm
        · intro d hd
          exact (Finset.mem_filter.mp hd).2
        · intro d hdW
          have hdW' : d ∈ firstAnnulusPositions b r k γ := by simpa [W] using hdW
          exact Finset.mem_filter.mpr ⟨by simpa using (mem_firstAnnulusPositions.mp hdW').1,
            hdW⟩
      rw [Finset.prod_ite]
      simp [hfilter]
    _ = baseDecay b ^ (firstAnnulusPositions b r k γ).card := rfl

/-- Product-bound form of the paper's `main-1`, parameterized by the number
of first-annulus positions. -/
theorem digitCharacterSum_upper
    {b r k : ℕ} (hb : 2 ≤ b) (γ : ℝ) :
    ‖∑ s ∈ digitSubsets r,
        e ((k : ℝ) * (digitValue b s : ℝ) * γ)‖ ≤
      (2 : ℝ) ^ (r + 1) *
        baseDecay b ^ (firstAnnulusPositions b r k γ).card := by
  exact (productBound b r k γ).trans
    (mul_le_mul_of_nonneg_left (product_circleNorm_le_baseDecay_pow hb γ) (by positivity))

/-- Removing the zero digit sum costs at most one. -/
theorem digitCharacterSum_erase_empty_upper
    {b r k : ℕ} (hb : 2 ≤ b) (γ : ℝ) :
    ‖∑ s ∈ (digitSubsets r).erase ∅,
        e ((k : ℝ) * (digitValue b s : ℝ) * γ)‖ ≤
      1 + (2 : ℝ) ^ (r + 1) *
        baseDecay b ^ (firstAnnulusPositions b r k γ).card := by
  let F : Finset ℕ → ℂ :=
    fun s ↦ e ((k : ℝ) * (digitValue b s : ℝ) * γ)
  have hdecomp : (∑ s ∈ (digitSubsets r).erase ∅, F s) =
      (∑ s ∈ digitSubsets r, F s) - 1 := by
    have hsum := Finset.sum_erase_add (s := digitSubsets r) F (empty_mem_digitSubsets r)
    rw [show F ∅ = 1 by simp [F]] at hsum
    linear_combination hsum
  rw [hdecomp]
  calc
    ‖(∑ s ∈ digitSubsets r, F s) - 1‖ ≤
        ‖∑ s ∈ digitSubsets r, F s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ ((2 : ℝ) ^ (r + 1) *
          baseDecay b ^ (firstAnnulusPositions b r k γ).card) + 1 := by
      have hmain := digitCharacterSum_upper (r := r) (k := k) hb γ
      simpa [F] using add_le_add hmain (by norm_num : ‖(1 : ℂ)‖ ≤ (1 : ℝ))
    _ = 1 + (2 : ℝ) ^ (r + 1) *
          baseDecay b ^ (firstAnnulusPositions b r k γ).card := by ring

end DigitRestricted
