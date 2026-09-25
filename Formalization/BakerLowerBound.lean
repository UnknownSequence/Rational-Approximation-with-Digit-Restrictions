import Formalization.ExponentialProduct

/-!
# The Baker lower-bound certificate

The paper cites Baker's Theorem 2.2.  To keep Olson as the only axiom, we use
an explicit Fejér-kernel certificate instead.  Its degree is `2M - 2` rather
than `M`; this changes only a harmless base-dependent constant downstream.

This file establishes the pointwise part of that argument: outside the arc
`‖x‖ < 1/M`, the geometric character sum has norm at most `M/2`, so the
polynomial `4F² - M²F` is nonpositive for `F = ‖∑_{j<M} e(jx)‖²`.
-/

open scoped BigOperators

noncomputable section

namespace DigitRestricted

/-- A length-`M` geometric character sum. -/
def geometricCharacterSum (M : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range M, e ((j : ℝ) * x)

theorem e_nat_mul (j : ℕ) (x : ℝ) : e ((j : ℝ) * x) = e x ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.cast_succ, add_mul, e_add, ih, pow_succ]
      simp

theorem geometricCharacterSum_eq_geom (M : ℕ) (x : ℝ) :
    geometricCharacterSum M x = ∑ j ∈ Finset.range M, e x ^ j := by
  apply Finset.sum_congr rfl
  intro j hj
  exact e_nat_mul j x

/-- Chord length on the unit circle. -/
theorem norm_e_sub_one (x : ℝ) :
    ‖e x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x)
  rw [show Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) by ring] at h
  rw [e]
  convert h using 1 <;> norm_num <;> ring

/-- Absolute sine depends only on distance to the nearest integer. -/
theorem abs_sin_pi_eq_sin_circleNorm (x : ℝ) :
    |Real.sin (Real.pi * x)| = Real.sin (Real.pi * circleNorm x) := by
  let δ : ℝ := x - (round x : ℝ)
  have hδ : |δ| = circleNorm x := by rfl
  have hperiodic : |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * δ)| := by
    have h := Real.sin_sub_int_mul_pi (Real.pi * x) (round x)
    have harg : Real.pi * x - (round x : ℝ) * Real.pi = Real.pi * δ := by
      dsimp [δ]
      ring
    rw [harg] at h
    rw [h]
    simp
  rw [hperiodic]
  have hδhalf : |δ| ≤ 1 / 2 := by simpa [hδ] using circleNorm_le_half x
  have hcn0 : 0 ≤ circleNorm x := circleNorm_nonneg x
  have hcnhalf : circleNorm x ≤ 1 / 2 := circleNorm_le_half x
  rcases le_total 0 δ with hδ0 | hδ0
  · have hδeq : δ = circleNorm x := by
      rw [← hδ, abs_of_nonneg hδ0]
    rw [hδeq, abs_of_nonneg]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos, Real.pi_gt_three])
  · have hδeq : -δ = circleNorm x := by
      rw [← hδ, abs_of_nonpos hδ0]
    rw [show Real.pi * δ = -(Real.pi * circleNorm x) by rw [← hδeq]; ring,
      Real.sin_neg, abs_neg, abs_of_nonneg]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos, Real.pi_gt_three])

/-- Jordan's inequality in nearest-integer notation. -/
theorem two_mul_circleNorm_le_abs_sin_pi (x : ℝ) :
    2 * circleNorm x ≤ |Real.sin (Real.pi * x)| := by
  rw [abs_sin_pi_eq_sin_circleNorm]
  have hcn0 : 0 ≤ circleNorm x := circleNorm_nonneg x
  have hcnhalf : circleNorm x ≤ 1 / 2 := circleNorm_le_half x
  have hangle : |Real.pi * circleNorm x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hcn0]
    nlinarith [Real.pi_pos]
  have hj := Real.mul_abs_le_abs_sin hangle
  have hsin0 : 0 ≤ Real.sin (Real.pi * circleNorm x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos, Real.pi_gt_three])
  rw [abs_of_nonneg hsin0] at hj
  calc
    2 * circleNorm x = 2 / Real.pi * |Real.pi * circleNorm x| := by
      rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hcn0)]
      field_simp [Real.pi_ne_zero]
    _ ≤ Real.sin (Real.pi * circleNorm x) := hj

/-- The geometric sum is small outside the central arc. -/
theorem geometricCharacterSum_norm_le_half
    {M : ℕ} (hM : 1 ≤ M) {x : ℝ}
    (hx : 1 / (M : ℝ) ≤ circleNorm x) :
    ‖geometricCharacterSum M x‖ ≤ (M : ℝ) / 2 := by
  have hMreal : (0 : ℝ) < M := by positivity
  have hden : 4 / (M : ℝ) ≤ ‖e x - 1‖ := by
    rw [norm_e_sub_one]
    have hsin := two_mul_circleNorm_le_abs_sin_pi x
    have : 2 / (M : ℝ) ≤ |Real.sin (Real.pi * x)| := by
      calc
        2 / (M : ℝ) = 2 * (1 / (M : ℝ)) := by ring
        _ ≤ 2 * circleNorm x := by gcongr
        _ ≤ |Real.sin (Real.pi * x)| := hsin
    calc
      4 / (M : ℝ) = 2 * (2 / (M : ℝ)) := by ring
      _ ≤ 2 * |Real.sin (Real.pi * x)| :=
        mul_le_mul_of_nonneg_left this (by norm_num)
  have hgeom : geometricCharacterSum M x * (e x - 1) = e x ^ M - 1 := by
    rw [geometricCharacterSum_eq_geom]
    exact geom_sum_mul (e x) M
  have hnum : ‖e x ^ M - 1‖ ≤ 2 := by
    calc
      ‖e x ^ M - 1‖ ≤ ‖e x ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [norm_pow, e_norm, one_pow, norm_one]
        norm_num
  have hprod : ‖geometricCharacterSum M x‖ * ‖e x - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    exact hnum
  have hnorm0 : 0 ≤ ‖geometricCharacterSum M x‖ := norm_nonneg _
  calc
    ‖geometricCharacterSum M x‖ ≤ 2 / ‖e x - 1‖ := by
      apply (le_div_iff₀ (lt_of_lt_of_le (by positivity : 0 < 4 / (M : ℝ)) hden)).2
      simpa [mul_comm] using hprod
    _ ≤ (M : ℝ) / 2 := by
      apply (div_le_iff₀ (lt_of_lt_of_le (by positivity : 0 < 4 / (M : ℝ)) hden)).2
      have := mul_le_mul_of_nonneg_left hden (show (0 : ℝ) ≤ M / 2 by positivity)
      field_simp at this ⊢
      nlinarith

/-- The pointwise Fejér certificate used to replace the cited Baker theorem. -/
theorem bakerCertificate_nonpos
    {M : ℕ} (hM : 1 ≤ M) {x : ℝ}
    (hx : 1 / (M : ℝ) ≤ circleNorm x) :
    let F := ‖geometricCharacterSum M x‖ ^ 2
    4 * F ^ 2 - (M : ℝ) ^ 2 * F ≤ 0 := by
  dsimp
  have hnorm := geometricCharacterSum_norm_le_half hM hx
  have hnorm0 := norm_nonneg (geometricCharacterSum M x)
  have hsq : ‖geometricCharacterSum M x‖ ^ 2 ≤ (M : ℝ) ^ 2 / 4 := by
    nlinarith [sq_nonneg (‖geometricCharacterSum M x‖ - (M : ℝ) / 2)]
  have hF0 : 0 ≤ ‖geometricCharacterSum M x‖ ^ 2 := sq_nonneg _
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hF0 (by nlinarith :
    4 * ‖geometricCharacterSum M x‖ ^ 2 - (M : ℝ) ^ 2 ≤ 0)]

/-! ## Constant coefficient of the certificate -/

/-- Ordered pairs of indices in a length-`M` geometric sum. -/
def pairIndices (M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range M).product (Finset.range M)

/-- A nonnegative encoding of the signed difference `a - b`. -/
def pairCode (M : ℕ) (p : ℕ × ℕ) : ℕ :=
  p.1 + M - p.2

/-- The additive energy of the interval of `M` consecutive integers. -/
def intervalDifferenceEnergy (M : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (2 * M),
    ((pairIndices M).filter (fun p ↦ pairCode M p = t)).card ^ 2

theorem pairCode_lt_two_mul {M : ℕ} (_hM : 1 ≤ M) {p : ℕ × ℕ}
    (hp : p ∈ pairIndices M) : pairCode M p < 2 * M := by
  rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
  simp only [Finset.mem_range] at ha hb
  dsimp [pairCode]
  omega

/-- The difference fibers partition all `M²` ordered pairs. -/
theorem sum_pairCode_fibers {M : ℕ} (hM : 1 ≤ M) :
    ∑ t ∈ Finset.range (2 * M),
        ((pairIndices M).filter (fun p ↦ pairCode M p = t)).card = M ^ 2 := by
  have hmaps : Set.MapsTo (pairCode M) (pairIndices M : Set (ℕ × ℕ))
      (Finset.range (2 * M) : Set ℕ) := by
    intro p hp
    simpa using pairCode_lt_two_mul hM hp
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  rw [show (pairIndices M).card = M ^ 2 by
    simp [pairIndices, Finset.card_product, pow_two]] at hpartition
  exact hpartition.symm

/-- Cauchy--Schwarz gives the lower bound needed for the constant Fourier
coefficient of the Fejér certificate. -/
theorem intervalDifferenceEnergy_lower {M : ℕ} (hM : 1 ≤ M) :
    (M : ℝ) ^ 3 / 2 ≤ intervalDifferenceEnergy M := by
  let c : ℕ → ℝ := fun t ↦
    (((pairIndices M).filter (fun p ↦ pairCode M p = t)).card : ℝ)
  have hsumNat := sum_pairCode_fibers hM
  have hsum : ∑ t ∈ Finset.range (2 * M), c t = (M : ℝ) ^ 2 := by
    dsimp [c]
    rw [← Nat.cast_sum]
    norm_cast
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.range (2 * M)) (f := c)
  rw [hsum, Finset.card_range] at hcs
  have henergy : ∑ t ∈ Finset.range (2 * M), c t ^ 2 =
      intervalDifferenceEnergy M := by
    dsimp [c, intervalDifferenceEnergy]
  rw [henergy] at hcs
  have hMreal : (0 : ℝ) < M := by positivity
  norm_num [Nat.cast_mul] at hcs ⊢
  nlinarith [show 0 ≤ intervalDifferenceEnergy M by
    exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)]

/-! ## Finite Fourier expansion -/

def pairFrequency (p : ℕ × ℕ) : ℝ :=
  (p.1 : ℝ) - (p.2 : ℝ)

@[simp] theorem conj_e (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  rw [e, e, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal]
  simp

/-- The Fejér kernel as a finite character sum over differences. -/
theorem geometricNormSq_expansion (M : ℕ) (x : ℝ) :
    ((‖geometricCharacterSum M x‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ pairIndices M, e (pairFrequency p * x) := by
  have hconj : (starRingEnd ℂ) (geometricCharacterSum M x) =
      ∑ j ∈ Finset.range M, e (-((j : ℝ) * x)) := by
    rw [geometricCharacterSum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [conj_e]
  calc
    ((‖geometricCharacterSum M x‖ ^ 2 : ℝ) : ℂ) =
        geometricCharacterSum M x * (starRingEnd ℂ) (geometricCharacterSum M x) := by
      simpa using (Complex.mul_conj' (geometricCharacterSum M x)).symm
    _ = geometricCharacterSum M x *
        ∑ j ∈ Finset.range M, e (-((j : ℝ) * x)) := by rw [hconj]
    _ = (∑ i ∈ Finset.range M, e ((i : ℝ) * x)) *
        ∑ j ∈ Finset.range M, e (-((j : ℝ) * x)) := by
      rw [geometricCharacterSum]
    _ = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        e ((i : ℝ) * x) * e (-((j : ℝ) * x)) :=
      Finset.sum_mul_sum _ _ _ _
    _ = ∑ p ∈ (Finset.range M).product (Finset.range M),
        e ((p.1 : ℝ) * x) * e (-((p.2 : ℝ) * x)) := by
      exact (Finset.sum_product (Finset.range M) (Finset.range M)
        (fun p : ℕ × ℕ ↦ e ((p.1 : ℝ) * x) * e (-((p.2 : ℝ) * x)))).symm
    _ = ∑ p ∈ pairIndices M, e (pairFrequency p * x) := by
      rw [pairIndices]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← e_add]
      congr 2
      dsimp [pairFrequency]
      ring

/-- The square of the Fejér kernel as a character sum over two pairs. -/
theorem geometricNormFourth_expansion (M : ℕ) (x : ℝ) :
    ((‖geometricCharacterSum M x‖ ^ 4 : ℝ) : ℂ) =
      ∑ q ∈ (pairIndices M).product (pairIndices M),
        e ((pairFrequency q.1 + pairFrequency q.2) * x) := by
  have hs := geometricNormSq_expansion M x
  calc
    ((‖geometricCharacterSum M x‖ ^ 4 : ℝ) : ℂ) =
        ((‖geometricCharacterSum M x‖ ^ 2 : ℝ) : ℂ) *
          ((‖geometricCharacterSum M x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    _ = (∑ p ∈ pairIndices M, e (pairFrequency p * x)) *
          ∑ q ∈ pairIndices M, e (pairFrequency q * x) := by rw [hs]
    _ = ∑ p ∈ pairIndices M, ∑ q ∈ pairIndices M,
          e (pairFrequency p * x) * e (pairFrequency q * x) :=
      Finset.sum_mul_sum _ _ _ _
    _ = ∑ q ∈ (pairIndices M).product (pairIndices M),
        e (pairFrequency q.1 * x) * e (pairFrequency q.2 * x) := by
      exact (Finset.sum_product (pairIndices M) (pairIndices M)
        (fun q : (ℕ × ℕ) × (ℕ × ℕ) ↦
          e (pairFrequency q.1 * x) * e (pairFrequency q.2 * x))).symm
    _ = ∑ q ∈ (pairIndices M).product (pairIndices M),
        e ((pairFrequency q.1 + pairFrequency q.2) * x) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← e_add]
      congr 2
      ring

/-- A conjugate form of the fourth-power expansion, whose zero-frequency
quadruples are counted by `intervalDifferenceEnergy`. -/
theorem geometricNormFourth_difference_expansion (M : ℕ) (x : ℝ) :
    ((‖geometricCharacterSum M x‖ ^ 4 : ℝ) : ℂ) =
      ∑ q ∈ (pairIndices M).product (pairIndices M),
        e ((pairFrequency q.1 - pairFrequency q.2) * x) := by
  have hs := geometricNormSq_expansion M x
  have hsneg : ((‖geometricCharacterSum M x‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ pairIndices M, e (-(pairFrequency p * x)) := by
    have hc := congrArg (starRingEnd ℂ) hs
    simp only [map_sum, conj_e, Complex.conj_ofReal] at hc
    simpa using hc
  calc
    ((‖geometricCharacterSum M x‖ ^ 4 : ℝ) : ℂ) =
        ((‖geometricCharacterSum M x‖ ^ 2 : ℝ) : ℂ) *
          ((‖geometricCharacterSum M x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    _ = (∑ p ∈ pairIndices M, e (pairFrequency p * x)) *
          ∑ q ∈ pairIndices M, e (-(pairFrequency q * x)) := by
      exact congrArg₂ (· * ·) hs hsneg
    _ = ∑ p ∈ pairIndices M, ∑ q ∈ pairIndices M,
          e (pairFrequency p * x) * e (-(pairFrequency q * x)) :=
      Finset.sum_mul_sum _ _ _ _
    _ = ∑ q ∈ (pairIndices M).product (pairIndices M),
        e (pairFrequency q.1 * x) * e (-(pairFrequency q.2 * x)) := by
      exact (Finset.sum_product (pairIndices M) (pairIndices M)
        (fun q : (ℕ × ℕ) × (ℕ × ℕ) ↦
          e (pairFrequency q.1 * x) * e (-(pairFrequency q.2 * x)))).symm
    _ = ∑ q ∈ (pairIndices M).product (pairIndices M),
        e ((pairFrequency q.1 - pairFrequency q.2) * x) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← e_add]
      congr 2
      ring

/-- Zero-frequency quadruples for the difference expansion. -/
def zeroFrequencyQuadruples (M : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((pairIndices M).product (pairIndices M)).filter
    (fun q ↦ pairCode M q.1 = pairCode M q.2)

theorem intervalDifferenceEnergy_eq_zeroFrequency_card
    {M : ℕ} (hM : 1 ≤ M) :
    intervalDifferenceEnergy M = (zeroFrequencyQuadruples M).card := by
  let P := pairIndices M
  let Z := zeroFrequencyQuadruples M
  let c : ℕ → Finset (ℕ × ℕ) := fun t ↦
    P.filter (fun p ↦ pairCode M p = t)
  have hmaps : Set.MapsTo (fun q : (ℕ × ℕ) × (ℕ × ℕ) ↦ pairCode M q.1)
      (Z : Set ((ℕ × ℕ) × (ℕ × ℕ))) (Finset.range (2 * M) : Set ℕ) := by
    intro q hq
    have hq' : q ∈ zeroFrequencyQuadruples M := by simpa [Z] using hq
    have hqprod' := (Finset.mem_filter.mp hq').1
    have hqprod : q ∈ P.product P := by simpa [P] using hqprod'
    exact Finset.mem_range.mpr (pairCode_lt_two_mul hM (Finset.mem_product.mp hqprod).1)
  have hfiber (t : ℕ) :
      Z.filter (fun q ↦ pairCode M q.1 = t) = (c t).product (c t) := by
    ext q
    constructor
    · intro hq
      have hqZ : q ∈ Z := (Finset.mem_filter.mp hq).1
      have ht : pairCode M q.1 = t := (Finset.mem_filter.mp hq).2
      have hqZ' : q ∈ zeroFrequencyQuadruples M := by simpa [Z] using hqZ
      have hqprod := (Finset.mem_filter.mp hqZ').1
      have heq := (Finset.mem_filter.mp hqZ').2
      rcases Finset.mem_product.mp hqprod with ⟨hq₁, hq₂⟩
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_filter.mpr ⟨by simpa [P] using hq₁, ht⟩
      · exact Finset.mem_filter.mpr ⟨by simpa [P] using hq₂, heq.symm.trans ht⟩
    · intro hq
      rcases Finset.mem_product.mp hq with ⟨hq₁, hq₂⟩
      have hp₁ := Finset.mem_filter.mp hq₁
      have hp₂ := Finset.mem_filter.mp hq₂
      apply Finset.mem_filter.mpr
      constructor
      · have hz : q ∈ zeroFrequencyQuadruples M := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr ⟨by simpa [P] using hp₁.1,
            by simpa [P] using hp₂.1⟩, hp₁.2.trans hp₂.2.symm⟩
        simpa [Z] using hz
      · exact hp₁.2
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    intervalDifferenceEnergy M =
        ∑ t ∈ Finset.range (2 * M), ((c t).card : ℝ) ^ 2 := by
      simp [intervalDifferenceEnergy, c, P]
    _ = ∑ t ∈ Finset.range (2 * M),
        ((Z.filter (fun q ↦ pairCode M q.1 = t)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      norm_cast
      rw [hfiber]
      simpa [pow_two] using (Finset.card_product (c t) (c t)).symm
    _ = Z.card := by exact_mod_cast hpartition.symm
    _ = (zeroFrequencyQuadruples M).card := rfl

/-! ## Positive-frequency mass -/

def naturalFourierSum {ι : Type*} (s : Finset ι) (x : ι → ℝ) (v : ℕ) : ℂ :=
  ∑ i ∈ s, e ((v : ℝ) * x i)

def integerFourierSum {ι : Type*} (s : Finset ι) (x : ι → ℝ) (v : ℤ) : ℂ :=
  ∑ i ∈ s, e ((v : ℝ) * x i)

def positiveFrequencyMass {ι : Type*} (s : Finset ι) (x : ι → ℝ) (B : ℕ) : ℝ :=
  ∑ v ∈ Finset.Icc 1 B, ‖naturalFourierSum s x v‖

theorem integerFourierSum_norm_eq_natAbs {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (v : ℤ) :
    ‖integerFourierSum s x v‖ = ‖naturalFourierSum s x v.natAbs‖ := by
  cases v with
  | ofNat n => simp [integerFourierSum, naturalFourierSum]
  | negSucc n =>
      have hconj : (starRingEnd ℂ) (naturalFourierSum s x (n + 1)) =
          integerFourierSum s x (.negSucc n) := by
        rw [naturalFourierSum, integerFourierSum, map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [conj_e]
        congr 2
        push_cast
        ring
      rw [← hconj, Complex.norm_conj]
      rfl

theorem integerFourierSum_norm_le_mass {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) {B : ℕ} {v : ℤ} (hv0 : v ≠ 0) (hvB : v.natAbs ≤ B) :
    ‖integerFourierSum s x v‖ ≤ positiveFrequencyMass s x B := by
  rw [integerFourierSum_norm_eq_natAbs]
  rw [positiveFrequencyMass]
  exact Finset.single_le_sum
    (s := Finset.Icc 1 B) (f := fun w ↦ ‖naturalFourierSum s x w‖)
    (fun w hw ↦ norm_nonneg _)
    (Finset.mem_Icc.mpr ⟨(Int.natAbs_pos.mpr hv0), hvB⟩)

def pairFrequencyInt (p : ℕ × ℕ) : ℤ :=
  (p.1 : ℤ) - (p.2 : ℤ)

def quadrupleFrequencyInt (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  ((q.1.1 + q.2.2 : ℕ) : ℤ) - ((q.1.2 + q.2.1 : ℕ) : ℤ)

theorem pairFrequencyInt_cast (p : ℕ × ℕ) :
    (pairFrequencyInt p : ℝ) = pairFrequency p := by
  simp [pairFrequencyInt, pairFrequency]

theorem quadrupleFrequencyInt_cast (q : (ℕ × ℕ) × (ℕ × ℕ)) :
    (quadrupleFrequencyInt q : ℝ) = pairFrequency q.1 - pairFrequency q.2 := by
  simp [quadrupleFrequencyInt, pairFrequency]
  ring

theorem pairFrequencyInt_natAbs_lt {M : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ pairIndices M) : (pairFrequencyInt p).natAbs < M := by
  rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
  simp only [Finset.mem_range] at ha hb
  exact Int.natAbs_coe_sub_coe_lt_of_lt ha hb

theorem quadrupleFrequencyInt_natAbs_lt {M : ℕ}
    {q : (ℕ × ℕ) × (ℕ × ℕ)}
    (hq : q ∈ (pairIndices M).product (pairIndices M)) :
    (quadrupleFrequencyInt q).natAbs < 2 * M := by
  rcases Finset.mem_product.mp hq with ⟨hq₁, hq₂⟩
  rcases Finset.mem_product.mp hq₁ with ⟨ha, hb⟩
  rcases Finset.mem_product.mp hq₂ with ⟨hc, hd⟩
  simp only [Finset.mem_range] at ha hb hc hd
  apply Int.natAbs_coe_sub_coe_lt_of_lt <;> omega

theorem pairCode_eq_iff_frequency_eq {M : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ pairIndices M) (hq : q ∈ pairIndices M) :
    pairCode M p = pairCode M q ↔ pairFrequencyInt p = pairFrequencyInt q := by
  rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
  rcases Finset.mem_product.mp hq with ⟨hc, hd⟩
  simp only [Finset.mem_range] at ha hb hc hd
  dsimp [pairCode, pairFrequencyInt]
  omega

theorem mem_zeroFrequencyQuadruples_iff_frequency_zero
    {M : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)} :
    q ∈ zeroFrequencyQuadruples M ↔
      q ∈ (pairIndices M).product (pairIndices M) ∧ quadrupleFrequencyInt q = 0 := by
  constructor
  · intro hq
    have hparts := Finset.mem_filter.mp hq
    have hp := (Finset.mem_product.mp hparts.1).1
    have hr := (Finset.mem_product.mp hparts.1).2
    have hfreq := (pairCode_eq_iff_frequency_eq hp hr).mp hparts.2
    constructor
    · exact hparts.1
    · dsimp [quadrupleFrequencyInt, pairFrequencyInt] at hfreq ⊢
      omega
  · rintro ⟨hq, hzero⟩
    apply Finset.mem_filter.mpr
    refine ⟨hq, ?_⟩
    have hp := (Finset.mem_product.mp hq).1
    have hr := (Finset.mem_product.mp hq).2
    apply (pairCode_eq_iff_frequency_eq hp hr).mpr
    dsimp [quadrupleFrequencyInt, pairFrequencyInt] at hzero ⊢
    omega

/-! ## Summed Fourier expansions -/

/-- Sum the quadratic Fejér expansion over a finite set of points. -/
theorem sum_geometricNormSq_expansion {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (M : ℕ) :
    (((∑ i ∈ s, ‖geometricCharacterSum M (x i)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ p ∈ pairIndices M, integerFourierSum s x (pairFrequencyInt p) := by
  push_cast
  calc
    (∑ i ∈ s, (‖geometricCharacterSum M (x i)‖ : ℂ) ^ 2) =
        ∑ i ∈ s, ∑ p ∈ pairIndices M, e (pairFrequency p * x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa using geometricNormSq_expansion M (x i)
    _ = ∑ p ∈ pairIndices M, ∑ i ∈ s, e (pairFrequency p * x i) := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ pairIndices M, integerFourierSum s x (pairFrequencyInt p) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro i hi
      rw [pairFrequencyInt_cast]

/-- Sum the fourth-power Fejér expansion over a finite set of points. -/
theorem sum_geometricNormFourth_expansion {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (M : ℕ) :
    (((∑ i ∈ s, ‖geometricCharacterSum M (x i)‖ ^ 4 : ℝ)) : ℂ) =
      ∑ q ∈ (pairIndices M).product (pairIndices M),
        integerFourierSum s x (quadrupleFrequencyInt q) := by
  push_cast
  calc
    (∑ i ∈ s, (‖geometricCharacterSum M (x i)‖ : ℂ) ^ 4) =
        ∑ i ∈ s, ∑ q ∈ (pairIndices M).product (pairIndices M),
          e ((pairFrequency q.1 - pairFrequency q.2) * x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa using geometricNormFourth_difference_expansion M (x i)
    _ = ∑ q ∈ (pairIndices M).product (pairIndices M),
        ∑ i ∈ s, e ((pairFrequency q.1 - pairFrequency q.2) * x i) := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ (pairIndices M).product (pairIndices M),
        integerFourierSum s x (quadrupleFrequencyInt q) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro i hi
      rw [quadrupleFrequencyInt_cast]

/-! ## Separating zero and nonzero frequencies -/

def zeroFrequencyPairs (M : ℕ) : Finset (ℕ × ℕ) :=
  (pairIndices M).filter (fun p ↦ pairFrequencyInt p = 0)

theorem zeroFrequencyPairs_eq_diagonal (M : ℕ) :
    zeroFrequencyPairs M = (Finset.range M).image (fun j ↦ (j, j)) := by
  classical
  ext p
  constructor
  · intro hp
    have hfilter := Finset.mem_filter.mp hp
    have hprod := Finset.mem_product.mp hfilter.1
    have hp₁ : p.1 < M := Finset.mem_range.mp hprod.1
    have hp₂ : p.2 < M := Finset.mem_range.mp hprod.2
    have hfreq := hfilter.2
    have heq : p.1 = p.2 := by
      dsimp [pairFrequencyInt] at hfreq
      omega
    apply Finset.mem_image.mpr
    exact ⟨p.1, Finset.mem_range.mpr hp₁, by ext <;> simp [heq]⟩
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨hj, hj⟩
    · simp [pairFrequencyInt]

theorem zeroFrequencyPairs_card (M : ℕ) : (zeroFrequencyPairs M).card = M := by
  classical
  rw [zeroFrequencyPairs_eq_diagonal, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact congrArg Prod.fst hab

@[simp] theorem pairIndices_card (M : ℕ) : (pairIndices M).card = M ^ 2 := by
  simp [pairIndices, pow_two]

@[simp] theorem pairIndices_product_card (M : ℕ) :
    ((pairIndices M).product (pairIndices M)).card = M ^ 4 := by
  simp [pow_succ, mul_assoc]

theorem positiveFrequencyMass_nonneg {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (B : ℕ) : 0 ≤ positiveFrequencyMass s x B := by
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

@[simp] theorem integerFourierSum_zero {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) : integerFourierSum s x 0 = s.card := by
  simp [integerFourierSum]

/-- The quadratic expansion has only `M` zero-frequency terms; all other
terms are controlled by the positive-frequency mass. -/
theorem pairFourierRealSum_upper {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) {M : ℕ} (hM : 1 ≤ M) :
    (∑ p ∈ pairIndices M,
        integerFourierSum s x (pairFrequencyInt p)).re ≤
      (M : ℝ) * s.card + (M : ℝ) ^ 2 * positiveFrequencyMass s x (2 * M) := by
  classical
  let P := pairIndices M
  let Z := zeroFrequencyPairs M
  let T := positiveFrequencyMass s x (2 * M)
  let f : ℕ × ℕ → ℝ := fun p ↦ (integerFourierSum s x (pairFrequencyInt p)).re
  have hT : 0 ≤ T := positiveFrequencyMass_nonneg s x (2 * M)
  have hzero : ∀ p ∈ Z, f p = (s.card : ℝ) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    simp [f, hp']
  have hnonzero : ∀ p ∈ P.filter (fun p ↦ ¬ pairFrequencyInt p = 0), f p ≤ T := by
    intro p hp
    have hpfilter := Finset.mem_filter.mp hp
    have hpP : p ∈ pairIndices M := by simpa [P] using hpfilter.1
    have hnorm : ‖integerFourierSum s x (pairFrequencyInt p)‖ ≤ T := by
      apply integerFourierSum_norm_le_mass s x hpfilter.2
      have hlt := pairFrequencyInt_natAbs_lt hpP
      omega
    exact (Complex.re_le_norm _).trans hnorm
  have hsplit := Finset.sum_filter_add_sum_filter_not P
    (fun p ↦ pairFrequencyInt p = 0) f
  have hZ : P.filter (fun p ↦ pairFrequencyInt p = 0) = Z := by
    rfl
  have hcardNot :
      ((P.filter (fun p ↦ ¬ pairFrequencyInt p = 0)).card : ℝ) ≤ P.card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hbound : (∑ p ∈ P, f p) ≤
      (Z.card : ℝ) * s.card + (P.card : ℝ) * T := by
    rw [← hsplit, hZ]
    calc
      (∑ p ∈ Z, f p) + ∑ p ∈ P.filter (fun p ↦ ¬ pairFrequencyInt p = 0), f p ≤
          (∑ _p ∈ Z, (s.card : ℝ)) +
            ∑ _p ∈ P.filter (fun p ↦ ¬ pairFrequencyInt p = 0), T := by
        exact add_le_add
          (Finset.sum_le_sum fun p hp ↦ (hzero p hp).le)
          (Finset.sum_le_sum hnonzero)
      _ = (Z.card : ℝ) * s.card +
          ((P.filter (fun p ↦ ¬ pairFrequencyInt p = 0)).card : ℝ) * T := by
        simp [nsmul_eq_mul]
      _ ≤ (Z.card : ℝ) * s.card + (P.card : ℝ) * T := by
        gcongr
  simpa [P, Z, T, f, zeroFrequencyPairs_card, pairIndices_card, map_sum,
    pow_two] using hbound

/-- The fourth-power expansion receives a large positive contribution from
its zero frequencies; every remaining term can lose at most the total
positive-frequency mass. -/
theorem quadrupleFourierRealSum_lower {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) {M : ℕ} (hM : 1 ≤ M) :
    (zeroFrequencyQuadruples M).card * (s.card : ℝ) -
        (M : ℝ) ^ 4 * positiveFrequencyMass s x (2 * M) ≤
      (∑ q ∈ (pairIndices M).product (pairIndices M),
        integerFourierSum s x (quadrupleFrequencyInt q)).re := by
  classical
  let Q := (pairIndices M).product (pairIndices M)
  let Z := zeroFrequencyQuadruples M
  let T := positiveFrequencyMass s x (2 * M)
  let f : (ℕ × ℕ) × (ℕ × ℕ) → ℝ := fun q ↦
    (integerFourierSum s x (quadrupleFrequencyInt q)).re
  let pred : (ℕ × ℕ) × (ℕ × ℕ) → Prop := fun q ↦
    pairCode M q.1 = pairCode M q.2
  have hT : 0 ≤ T := positiveFrequencyMass_nonneg s x (2 * M)
  have hzero : ∀ q ∈ Z, (s.card : ℝ) ≤ f q := by
    intro q hq
    have hfreq := (mem_zeroFrequencyQuadruples_iff_frequency_zero.mp
      (by simpa [Z] using hq)).2
    simp [f, hfreq]
  have hnonzero : ∀ q ∈ Q.filter (fun q ↦ ¬ pred q), -T ≤ f q := by
    intro q hq
    have hqfilter := Finset.mem_filter.mp hq
    have hqQ : q ∈ (pairIndices M).product (pairIndices M) := by
      simpa [Q] using hqfilter.1
    have hfreq : quadrupleFrequencyInt q ≠ 0 := by
      intro hz
      apply hqfilter.2
      dsimp [pred]
      exact (mem_zeroFrequencyQuadruples_iff_frequency_zero.mpr ⟨hqQ, hz⟩ |>
        Finset.mem_filter.mp).2
    have hnorm : ‖integerFourierSum s x (quadrupleFrequencyInt q)‖ ≤ T := by
      apply integerFourierSum_norm_le_mass s x hfreq
      have hlt := quadrupleFrequencyInt_natAbs_lt hqQ
      omega
    have habs := Complex.abs_re_le_norm
      (integerFourierSum s x (quadrupleFrequencyInt q))
    dsimp [f]
    linarith [neg_le_abs (integerFourierSum s x (quadrupleFrequencyInt q)).re]
  have hsplit := Finset.sum_filter_add_sum_filter_not Q pred f
  have hZ : Q.filter pred = Z := by rfl
  have hcardNot :
      ((Q.filter (fun q ↦ ¬ pred q)).card : ℝ) ≤ Q.card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hbound : (Z.card : ℝ) * s.card - (Q.card : ℝ) * T ≤ ∑ q ∈ Q, f q := by
    rw [← hsplit, hZ]
    calc
      (Z.card : ℝ) * s.card - (Q.card : ℝ) * T ≤
          (Z.card : ℝ) * s.card -
            ((Q.filter (fun q ↦ ¬ pred q)).card : ℝ) * T := by
        gcongr
      _ = (∑ _q ∈ Z, (s.card : ℝ)) +
          ∑ _q ∈ Q.filter (fun q ↦ ¬ pred q), -T := by
        simp [nsmul_eq_mul]
        ring
      _ ≤ (∑ q ∈ Z, f q) +
          ∑ q ∈ Q.filter (fun q ↦ ¬ pred q), f q := by
        exact add_le_add (Finset.sum_le_sum hzero) (Finset.sum_le_sum hnonzero)
  have hQcard : (Q.card : ℝ) = (M : ℝ) ^ 4 := by
    exact_mod_cast pairIndices_product_card M
  rw [hQcard] at hbound
  simpa [Q, Z, T, f, map_sum] using hbound

/-! ## The finite Baker-type lower bound -/

/-- A finite, explicit replacement for the lower bound cited from Baker.

If all points avoid the central arc of radius `1/M`, their Fourier mass in
the positive frequencies up to `2M` is at least `|s|/(5M)`.  The constants
are intentionally inessential; what matters downstream is the reciprocal
linear dependence on `M`. -/
theorem bakerLowerBoundFejer {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {M : ℕ} (hM : 1 ≤ M)
    (hx : ∀ i ∈ s, 1 / (M : ℝ) ≤ circleNorm (x i)) :
    (s.card : ℝ) / (5 * M) ≤ positiveFrequencyMass s x (2 * M) := by
  let A : ℝ := ∑ i ∈ s, ‖geometricCharacterSum M (x i)‖ ^ 4
  let B : ℝ := ∑ i ∈ s, ‖geometricCharacterSum M (x i)‖ ^ 2
  let T : ℝ := positiveFrequencyMass s x (2 * M)
  have hMpos : (0 : ℝ) < M := by positivity
  have hT : 0 ≤ T := positiveFrequencyMass_nonneg s x (2 * M)
  have hcertTerms :
      ∑ i ∈ s, (4 * (‖geometricCharacterSum M (x i)‖ ^ 2) ^ 2 -
        (M : ℝ) ^ 2 * ‖geometricCharacterSum M (x i)‖ ^ 2) ≤ 0 := by
    exact Finset.sum_nonpos fun i hi ↦ bakerCertificate_nonpos hM (hx i hi)
  have hcert : 4 * A - (M : ℝ) ^ 2 * B ≤ 0 := by
    calc
      4 * A - (M : ℝ) ^ 2 * B =
          ∑ i ∈ s, (4 * (‖geometricCharacterSum M (x i)‖ ^ 2) ^ 2 -
            (M : ℝ) ^ 2 * ‖geometricCharacterSum M (x i)‖ ^ 2) := by
        dsimp [A, B]
        simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ 0 := hcertTerms
  have hAeq : A =
      (∑ q ∈ (pairIndices M).product (pairIndices M),
        integerFourierSum s x (quadrupleFrequencyInt q)).re := by
    have h := congrArg Complex.re (sum_geometricNormFourth_expansion s x M)
    change ((A : ℂ).re) =
      (∑ q ∈ (pairIndices M).product (pairIndices M),
        integerFourierSum s x (quadrupleFrequencyInt q)).re at h
    simpa only [Complex.ofReal_re] using h
  have hBeq : B =
      (∑ p ∈ pairIndices M,
        integerFourierSum s x (pairFrequencyInt p)).re := by
    have h := congrArg Complex.re (sum_geometricNormSq_expansion s x M)
    change ((B : ℂ).re) =
      (∑ p ∈ pairIndices M,
        integerFourierSum s x (pairFrequencyInt p)).re at h
    simpa only [Complex.ofReal_re] using h
  have hAlower :
      (zeroFrequencyQuadruples M).card * (s.card : ℝ) - (M : ℝ) ^ 4 * T ≤ A := by
    rw [hAeq]
    exact quadrupleFourierRealSum_lower s x hM
  have hBupper : B ≤
      (M : ℝ) * s.card + (M : ℝ) ^ 2 * T := by
    rw [hBeq]
    exact pairFourierRealSum_upper s x hM
  have henergy := intervalDifferenceEnergy_lower hM
  rw [intervalDifferenceEnergy_eq_zeroFrequency_card hM] at henergy
  have hcardNonneg : (0 : ℝ) ≤ s.card := by positivity
  have hzeroContribution :
      (M : ℝ) ^ 3 / 2 * s.card ≤
        (zeroFrequencyQuadruples M).card * (s.card : ℝ) :=
    mul_le_mul_of_nonneg_right henergy hcardNonneg
  have hAlower' :
      (M : ℝ) ^ 3 / 2 * s.card - (M : ℝ) ^ 4 * T ≤ A := by
    exact le_trans (sub_le_sub_right hzeroContribution _) hAlower
  have h4A := mul_le_mul_of_nonneg_left hAlower' (by norm_num : (0 : ℝ) ≤ 4)
  have hM2B := mul_le_mul_of_nonneg_left hBupper (sq_nonneg (M : ℝ))
  have hmaster :
      (M : ℝ) ^ 3 * s.card - 5 * (M : ℝ) ^ 4 * T ≤
        4 * A - (M : ℝ) ^ 2 * B := by
    calc
      (M : ℝ) ^ 3 * s.card - 5 * (M : ℝ) ^ 4 * T =
          4 * ((M : ℝ) ^ 3 / 2 * s.card - (M : ℝ) ^ 4 * T) -
            (M : ℝ) ^ 2 * ((M : ℝ) * s.card + (M : ℝ) ^ 2 * T) := by ring
      _ ≤ 4 * A - (M : ℝ) ^ 2 * B := sub_le_sub h4A hM2B
  have hmass : (M : ℝ) ^ 3 * s.card ≤ 5 * (M : ℝ) ^ 4 * T := by
    linarith
  have hcancel : (s.card : ℝ) ≤ 5 * (M : ℝ) * T := by
    apply le_of_mul_le_mul_left _ (pow_pos hMpos 3)
    calc
      (M : ℝ) ^ 3 * s.card ≤ 5 * (M : ℝ) ^ 4 * T := hmass
      _ = (M : ℝ) ^ 3 * (5 * (M : ℝ) * T) := by ring
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * M)).2
  simpa [T, mul_comm, mul_left_comm] using hcancel

end DigitRestricted
