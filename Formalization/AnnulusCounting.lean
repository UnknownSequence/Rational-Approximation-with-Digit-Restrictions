import Formalization.Annuli
import Formalization.DigitSumUpper

/-!
# Counting first-annulus positions

This is the combinatorial bridge in the proof of `main-1`.  Each position
above the scale `1/(2b^m)` reaches the first annulus in fewer than `m` shifts.
Encoding a position by its destination and shift shows that at most `m`
interior positions feed any first-annulus destination; at most `m` positions
are lost at the right boundary.
-/

noncomputable section

namespace DigitRestricted

/-- Positions whose nearest-integer distance is above the `m`-th threshold. -/
def largePositions (b r k m : ℕ) (γ : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (r + 1)).filter
    (fun d ↦ 1 / (2 * (b : ℝ) ^ m) <
      circleNorm ((k : ℝ) * (b : ℝ) ^ d * γ))

@[simp] theorem mem_largePositions {b r k m d : ℕ} {γ : ℝ} :
    d ∈ largePositions b r k m γ ↔
      d ≤ r ∧ 1 / (2 * (b : ℝ) ^ m) <
        circleNorm ((k : ℝ) * (b : ℝ) ^ d * γ) := by
  simp [largePositions]

/-- Large and small positions partition `0, …, r`. -/
theorem largePositions_eq_sdiff_smallPositions (b r k m : ℕ) (γ : ℝ) :
    largePositions b r k m γ =
      Finset.range (r + 1) \ smallPositions b r k γ (1 / (2 * (b : ℝ) ^ m)) := by
  ext d
  simp only [largePositions, smallPositions, Finset.mem_filter, Finset.mem_range,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨hdr, hlarge⟩
    exact ⟨hdr, fun hs ↦ (not_le_of_gt hlarge) hs.2⟩
  · rintro ⟨hdr, hsmall⟩
    exact ⟨hdr, lt_of_not_ge (fun h ↦ hsmall ⟨hdr, h⟩)⟩

/-- The key counting inequality. -/
theorem largePositions_card_le_firstAnnulus
    {b r k m : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (γ : ℝ) :
    (largePositions b r k m γ).card ≤
      (firstAnnulusPositions b r k γ).card * m + m := by
  classical
  let L := largePositions b r k m γ
  let W := firstAnnulusPositions b r k γ
  let IsLarge : ℕ → Prop := fun v ↦
    1 / (2 * (b : ℝ) ^ m) < circleNorm ((k : ℝ) * (b : ℝ) ^ v * γ)
  have hex (v : ℕ) (hv : IsLarge v) :
      ∃ h : ℕ, 1 ≤ h ∧ h ≤ m ∧
        InAnnulus b 1 ((b : ℝ) ^ (h - 1) *
          ((k : ℝ) * (b : ℝ) ^ v * γ)) :=
    large_reaches_first_annulus hb hm hv
  let shift : ℕ → ℕ := fun v ↦ if hv : IsLarge v then (hex v hv).choose else 1
  have hshift (v : ℕ) (hv : IsLarge v) :
      1 ≤ shift v ∧ shift v ≤ m ∧
        InAnnulus b 1 ((b : ℝ) ^ (shift v - 1) *
          ((k : ℝ) * (b : ℝ) ^ v * γ)) := by
    dsimp [shift]
    rw [dif_pos hv]
    exact (hex v hv).choose_spec
  let target : ℕ → ℕ := fun v ↦ v + shift v - 1
  let L₀ : Finset ℕ := L.filter (fun v ↦ v + m - 1 ≤ r)
  have htarget (v : ℕ) (hvL₀ : v ∈ L₀) : target v ∈ W := by
    have hvL : v ∈ L := (Finset.mem_filter.mp hvL₀).1
    have hvLarge : IsLarge v := by
      exact (mem_largePositions.mp (by simpa [L] using hvL)).2
    have hs := hshift v hvLarge
    have hvbound : v + m - 1 ≤ r := (Finset.mem_filter.mp hvL₀).2
    have htbound : target v ≤ r := by
      dsimp [target]
      omega
    have harg : (k : ℝ) * (b : ℝ) ^ (target v) * γ =
        (b : ℝ) ^ (shift v - 1) *
          ((k : ℝ) * (b : ℝ) ^ v * γ) := by
      have ht : target v = v + (shift v - 1) := by
        dsimp [target]
        omega
      rw [ht, pow_add]
      ring
    have hann : InAnnulus b 1 ((k : ℝ) * (b : ℝ) ^ (target v) * γ) := by
      rw [harg]
      exact hs.2.2
    have : target v ∈ firstAnnulusPositions b r k γ :=
      mem_firstAnnulusPositions.mpr ⟨htbound, hann⟩
    simpa [W] using this
  let code : ℕ → ℕ × ℕ := fun v ↦ (target v, target v - v)
  have hcode_maps : Set.MapsTo code (L₀ : Set ℕ)
      (W.product (Finset.range m) : Set (ℕ × ℕ)) := by
    intro v hv
    have hvL : v ∈ L := (Finset.mem_filter.mp hv).1
    have hvLarge : IsLarge v :=
      (mem_largePositions.mp (by simpa [L] using hvL)).2
    have hs := hshift v hvLarge
    have hvtarget : v ≤ target v := by dsimp [target]; omega
    have hoffset : target v - v < m := by dsimp [target]; omega
    exact Finset.mem_product.mpr ⟨htarget v hv, by simpa using hoffset⟩
  have hcode_inj : Set.InjOn code (L₀ : Set ℕ) := by
    intro u hu v hv huv
    have huL : u ∈ L := (Finset.mem_filter.mp hu).1
    have hvL : v ∈ L := (Finset.mem_filter.mp hv).1
    have huLarge : IsLarge u :=
      (mem_largePositions.mp (by simpa [L] using huL)).2
    have hvLarge : IsLarge v :=
      (mem_largePositions.mp (by simpa [L] using hvL)).2
    have hus := hshift u huLarge
    have hvs := hshift v hvLarge
    have hut : u ≤ target u := by dsimp [target]; omega
    have hvt : v ≤ target v := by dsimp [target]; omega
    have h₁ : target u = target v := congrArg Prod.fst huv
    have h₂ : target u - u = target v - v := congrArg Prod.snd huv
    omega
  have hL₀card : L₀.card ≤ W.card * m := by
    simpa using Finset.card_le_card_of_injOn code hcode_maps hcode_inj
  let Tail : Finset ℕ := L \ L₀
  let tailCode : ℕ → ℕ := fun v ↦ r - v
  have htail_maps : Set.MapsTo tailCode (Tail : Set ℕ) (Finset.range m : Set ℕ) := by
    intro v hvTail
    have hvparts := Finset.mem_sdiff.mp hvTail
    have hvL : v ∈ L := hvparts.1
    have hvle : v ≤ r :=
      (mem_largePositions.mp (by simpa [L] using hvL)).1
    have hvnot : ¬v + m - 1 ≤ r := by
      intro h
      exact hvparts.2 (Finset.mem_filter.mpr ⟨hvL, h⟩)
    have : r - v < m := by omega
    simpa [tailCode] using this
  have htail_inj : Set.InjOn tailCode (Tail : Set ℕ) := by
    intro u hu v hv huv
    have hule : u ≤ r :=
      (mem_largePositions.mp (by
        simpa [L] using (Finset.mem_sdiff.mp hu).1)).1
    have hvle : v ≤ r :=
      (mem_largePositions.mp (by
        simpa [L] using (Finset.mem_sdiff.mp hv).1)).1
    dsimp [tailCode] at huv
    omega
  have htailcard : Tail.card ≤ m := by
    simpa using Finset.card_le_card_of_injOn tailCode htail_maps htail_inj
  have hL₀sub : L₀ ⊆ L := Finset.filter_subset _ _
  have hpartition : Tail.card + L₀.card = L.card := by
    simpa [Tail] using Finset.card_sdiff_add_card_eq_card hL₀sub
  dsimp [L, W] at hL₀card htailcard hpartition ⊢
  omega

/-- Combined with the Olson-dependent small-position estimate, this is the
integer-cardinality core of `main-1`. -/
theorem range_card_le_firstAnnulus_add_small
    {b r k m : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (γ : ℝ) :
    r + 1 ≤ (firstAnnulusPositions b r k γ).card * m + m +
      (smallPositions b r k γ (1 / (2 * (b : ℝ) ^ m))).card := by
  let L := largePositions b r k m γ
  let S := smallPositions b r k γ (1 / (2 * (b : ℝ) ^ m))
  have hSsub : S ⊆ Finset.range (r + 1) := by
    intro d hd
    have hd' : d ∈ smallPositions b r k γ (1 / (2 * (b : ℝ) ^ m)) := by
      simpa [S] using hd
    simpa using (mem_smallPositions.mp hd').1
  have hScard : S.card ≤ r + 1 := by
    simpa using Finset.card_le_card hSsub
  have hcardL : L.card = r + 1 - S.card := by
    rw [show L = Finset.range (r + 1) \ S by
      simpa [L, S] using largePositions_eq_sdiff_smallPositions b r k m γ]
    rw [Finset.card_sdiff_of_subset hSsub, Finset.card_range]
  have hL := largePositions_card_le_firstAnnulus (r := r) (k := k) hb hm γ
  change r + 1 ≤ (firstAnnulusPositions b r k γ).card * m + m + S.card
  change L.card ≤ (firstAnnulusPositions b r k γ).card * m + m at hL
  omega

/-- Olson plus annulus propagation, in the exact integer form consumed by the
exponential-sum upper bound. -/
theorem firstAnnulus_count_core
    {b r k m : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (hm : 1 ≤ m) {γ : ℝ}
    (havoid : ∀ n : ℕ, IsDigitRestrictedStarUpTo b r n → n ≠ 0 →
      1 / (2 * (b : ℝ) ^ m) < circleNorm (γ * n)) :
    let S := smallPositions b r k γ (1 / (2 * (b : ℝ) ^ m))
    S.card ^ 2 < 9 * k ∧
      r + 1 ≤ (firstAnnulusPositions b r k γ).card * m + m + S.card := by
  dsimp
  constructor
  · apply smallPositions_card_sq_lt hb hk
    · positivity
    · exact havoid
  · exact range_card_le_firstAnnulus_add_small hb hm γ

/-- A convenient square-root form of the annulus count.  This is merely the
integer reformulation of `S.card ^ 2 < 9 * k`; it introduces no real square
roots into the proof. -/
theorem firstAnnulus_count_sqrt
    {b r k m : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (hm : 1 ≤ m) {γ : ℝ}
    (havoid : ∀ n : ℕ, IsDigitRestrictedStarUpTo b r n → n ≠ 0 →
      1 / (2 * (b : ℝ) ^ m) < circleNorm (γ * n)) :
    r + 1 ≤ (firstAnnulusPositions b r k γ).card * m + m + Nat.sqrt (9 * k) := by
  have hcore := firstAnnulus_count_core hb hk hm havoid
  dsimp only at hcore
  have hsmall :
      (smallPositions b r k γ (1 / (2 * (b : ℝ) ^ m))).card ≤ Nat.sqrt (9 * k) := by
    rw [Nat.le_sqrt']
    exact hcore.1.le
  exact le_trans hcore.2 (by gcongr)

/-- Uniformize the square-root error over the frequency interval
`1 ≤ k ≤ 4 b^m`. -/
theorem firstAnnulus_count_frequencyRange
    {b r k m : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (hkm : k ≤ 4 * b ^ m)
    (hm : 1 ≤ m) {γ : ℝ}
    (havoid : ∀ n : ℕ, IsDigitRestrictedStarUpTo b r n → n ≠ 0 →
      1 / (2 * (b : ℝ) ^ m) < circleNorm (γ * n)) :
    r + 1 ≤ (firstAnnulusPositions b r k γ).card * m + m +
      6 * b ^ ((m + 1) / 2) := by
  have hsqrt := firstAnnulus_count_sqrt hb hk hm havoid
  have hexp : m ≤ ((m + 1) / 2) * 2 := by omega
  have hbpow : b ^ m ≤ (b ^ ((m + 1) / 2)) ^ 2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) hexp
  have hradicand : 9 * k ≤ (6 * b ^ ((m + 1) / 2)) ^ 2 := by
    calc
      9 * k ≤ 9 * (4 * b ^ m) := Nat.mul_le_mul_left 9 hkm
      _ ≤ 36 * (b ^ ((m + 1) / 2)) ^ 2 := by omega
      _ = (6 * b ^ ((m + 1) / 2)) ^ 2 := by ring
  have hsqrtBound : Nat.sqrt (9 * k) ≤ 6 * b ^ ((m + 1) / 2) := by
    rw [← Nat.sqrt_eq' (6 * b ^ ((m + 1) / 2))]
    exact Nat.sqrt_le_sqrt hradicand
  exact le_trans hsqrt (by gcongr)

/-- A scale hypothesis turns the preceding count into a uniform lower bound
for the number of decaying product factors. -/
theorem firstAnnulus_card_ge_uniform
    {b r k m L : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (hkm : k ≤ 4 * b ^ m)
    (hm : 1 ≤ m) {γ : ℝ}
    (havoid : ∀ n : ℕ, IsDigitRestrictedStarUpTo b r n → n ≠ 0 →
      1 / (2 * (b : ℝ) ^ m) < circleNorm (γ * n))
    (hscale : L * m + m + 6 * b ^ ((m + 1) / 2) ≤ r + 1) :
    L ≤ (firstAnnulusPositions b r k γ).card := by
  have hcount := firstAnnulus_count_frequencyRange hb hk hkm hm havoid
  have hmul : L * m ≤ (firstAnnulusPositions b r k γ).card * m := by omega
  exact Nat.le_of_mul_le_mul_right hmul (by omega)

end DigitRestricted
