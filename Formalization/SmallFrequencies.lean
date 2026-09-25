import Formalization.BoundedDigits
import Formalization.CircleDistance

/-!
# Few small frequencies

This is a squared-cardinality version of the paper's lemma `Addcomb2`.
Writing the conclusion as `card² < 9k` avoids introducing real square roots;
it is exactly the form needed to invoke the permitted Olson corollary.
-/

open scoped BigOperators

noncomputable section

namespace DigitRestricted

/-- Positions `d ≤ r` for which `k b^d γ` is unusually close to an integer. -/
def smallPositions (b r k : ℕ) (γ β : ℝ) : Finset ℕ :=
  (Finset.range (r + 1)).filter
    (fun d ↦ circleNorm ((k : ℝ) * (b : ℝ) ^ d * γ) ≤ β)

/-- The nearest integer, reduced modulo `k`. -/
def nearestResidue (b k d : ℕ) (γ : ℝ) : ZMod k :=
  (round ((k : ℝ) * (b : ℝ) ^ d * γ) : ZMod k)

@[simp] theorem mem_smallPositions {b r k d : ℕ} {γ β : ℝ} :
    d ∈ smallPositions b r k γ β ↔
      d ≤ r ∧ circleNorm ((k : ℝ) * (b : ℝ) ^ d * γ) ≤ β := by
  simp [smallPositions]

/-- Distinct small positions give distinct nearest-integer residues. -/
theorem nearestResidue_injective_on_smallPositions
    {b r k : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) {γ β : ℝ} (hβ : 0 < β)
    (havoid : ∀ n : ℕ, IsDigitRestrictedStarUpTo b r n → n ≠ 0 →
      β < circleNorm (γ * n)) :
    Set.InjOn (fun d ↦ nearestResidue b k d γ)
      (smallPositions b r k γ β : Set ℕ) := by
  have ordered_collision : ∀ {d₁ d₂ : ℕ},
      d₁ ∈ smallPositions b r k γ β → d₂ ∈ smallPositions b r k γ β →
      d₁ < d₂ → nearestResidue b k d₁ γ = nearestResidue b k d₂ γ → False := by
    intro d₁ d₂ hd₁ hd₂ hlt heq
    have hd₁' := (mem_smallPositions.mp hd₁)
    have hd₂' := (mem_smallPositions.mp hd₂)
    let a₁ : ℤ := round ((k : ℝ) * (b : ℝ) ^ d₁ * γ)
    let a₂ : ℤ := round ((k : ℝ) * (b : ℝ) ^ d₂ * γ)
    have hzero : (((a₂ - a₁ : ℤ) : ZMod k)) = 0 := by
      rw [Int.cast_sub]
      change nearestResidue b k d₂ γ - nearestResidue b k d₁ γ = 0
      rw [heq, sub_self]
    have hdvd : (k : ℤ) ∣ a₂ - a₁ :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
    rcases hdvd with ⟨z, hz⟩
    have hbpos : 0 < b := by omega
    have hpows : b ^ d₁ ≤ b ^ d₂ := Nat.pow_le_pow_right hbpos hlt.le
    have hpowlt : b ^ d₁ < b ^ d₂ := Nat.pow_lt_pow_right hb hlt
    let n : ℕ := b ^ d₂ - b ^ d₁
    have hnstar : IsDigitRestrictedStarUpTo b r n := by
      exact powerDifference_mem_starUpTo hd₁'.1 hd₂'.1 hlt
    have hnne : n ≠ 0 := by dsimp [n]; omega
    have hzreal : (a₂ : ℝ) - (a₁ : ℝ) = (k : ℝ) * (z : ℝ) := by
      exact_mod_cast hz
    have harg : (k : ℝ) * (γ * (n : ℝ) - (z : ℝ)) =
        ((k : ℝ) * (b : ℝ) ^ d₂ * γ - (a₂ : ℝ)) -
          ((k : ℝ) * (b : ℝ) ^ d₁ * γ - (a₁ : ℝ)) := by
      dsimp [n]
      rw [Nat.cast_sub hpows]
      calc
        (k : ℝ) * (γ * ((b ^ d₂ : ℕ) - (b ^ d₁ : ℕ)) - (z : ℝ)) =
            (k : ℝ) * (b : ℝ) ^ d₂ * γ -
              (k : ℝ) * (b : ℝ) ^ d₁ * γ - (k : ℝ) * (z : ℝ) := by
          push_cast
          ring
        _ = ((k : ℝ) * (b : ℝ) ^ d₂ * γ - (a₂ : ℝ)) -
            ((k : ℝ) * (b : ℝ) ^ d₁ * γ - (a₁ : ℝ)) := by
          rw [← hzreal]
          ring
    have herr : |(k : ℝ) * (γ * (n : ℝ) - (z : ℝ))| ≤ 2 * β := by
      rw [harg]
      calc
        |((k : ℝ) * (b : ℝ) ^ d₂ * γ - (a₂ : ℝ)) -
            ((k : ℝ) * (b : ℝ) ^ d₁ * γ - (a₁ : ℝ))| ≤
            |(k : ℝ) * (b : ℝ) ^ d₂ * γ - (a₂ : ℝ)| +
              |(k : ℝ) * (b : ℝ) ^ d₁ * γ - (a₁ : ℝ)| := abs_sub _ _
        _ = circleNorm ((k : ℝ) * (b : ℝ) ^ d₂ * γ) +
            circleNorm ((k : ℝ) * (b : ℝ) ^ d₁ * γ) := by rfl
        _ ≤ 2 * β := by linarith
    have hkreal : (0 : ℝ) < k := by positivity
    have hdist : |γ * (n : ℝ) - (z : ℝ)| ≤ β := by
      rw [abs_mul, abs_of_pos hkreal] at herr
      have htwo : (2 : ℝ) ≤ k := by exact_mod_cast hk
      calc
        |γ * (n : ℝ) - (z : ℝ)| ≤ 2 * β / (k : ℝ) :=
          (le_div_iff₀ hkreal).2 (by simpa [mul_comm] using herr)
        _ ≤ β := by
          rw [div_le_iff₀ hkreal]
          nlinarith
    have hcircle : circleNorm (γ * n) ≤ β :=
      (circleNorm_le_abs_sub_int (γ * n) z).trans (by simpa using hdist)
    exact (not_lt_of_ge hcircle) (havoid n hnstar hnne)
  intro d₁ hd₁ d₂ hd₂ heq
  rcases lt_trichotomy d₁ d₂ with hlt | heq' | hgt
  · exact (ordered_collision hd₁ hd₂ hlt heq).elim
  · exact heq'
  · exact (ordered_collision hd₂ hd₁ hgt heq.symm).elim

/-- `Addcomb2` in the natural-number form used by Olson's corollary. -/
theorem smallPositions_card_sq_lt
    {b r k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) {γ β : ℝ} (hβ : 0 < β)
    (havoid : ∀ n : ℕ, IsDigitRestrictedStarUpTo b r n → n ≠ 0 →
      β < circleNorm (γ * n)) :
    (smallPositions b r k γ β).card ^ 2 < 9 * k := by
  by_cases hkone : k = 1
  · subst k
    have hempty : smallPositions b r 1 γ β = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      have hd' := mem_smallPositions.mp hd
      let n : ℕ := b ^ d
      have hnup : IsDigitRestrictedUpTo b r n := by
        refine ⟨{d}, ?_, ?_⟩
        · simp [digitSubsets, hd'.1]
        · simp [n, digitValue]
      have hnstar : IsDigitRestrictedStarUpTo b r n := Or.inl hnup
      have hnne : n ≠ 0 := by dsimp [n]; positivity
      have := havoid n hnstar hnne
      norm_num at hd'
      exact (not_lt_of_ge hd'.2) (by simpa [n, mul_comm, mul_left_comm] using this)
    simp [hempty]
  · have hk2 : 2 ≤ k := by omega
    let V := smallPositions b r k γ β
    let ρ : ℕ → ZMod k := fun d ↦ nearestResidue b k d γ
    let S : Finset (ZMod k) := V.image ρ
    have hρinj : Set.InjOn ρ (V : Set ℕ) := by
      exact nearestResidue_injective_on_smallPositions hb hk2 hβ havoid
    let _ : NeZero k := ⟨by omega⟩
    have hcardS : S.card = V.card := Finset.card_image_iff.mpr hρinj
    by_contra hnot
    have hlargeV : 9 * k ≤ V.card ^ 2 := by
      dsimp [V]
      omega
    have hlargeS : 9 * k ≤ S.card ^ 2 := by simpa [hcardS] using hlargeV
    rcases addcomb k hk S hlargeS with ⟨T, hTne, hTS, hTsum⟩
    let U : Finset ℕ := V.filter (fun d ↦ ρ d ∈ T)
    have hUne : U.Nonempty := by
      rcases hTne with ⟨x, hxT⟩
      have hxS := hTS hxT
      rcases Finset.mem_image.mp hxS with ⟨d, hdV, rfl⟩
      exact ⟨d, by simp [U, hdV, hxT]⟩
    have hUV : U ⊆ V := Finset.filter_subset _ _
    have himage : U.image ρ = T := by
      apply Finset.Subset.antisymm
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨d, hdU, rfl⟩
        exact (Finset.mem_filter.mp hdU).2
      · intro x hxT
        have hxS := hTS hxT
        rcases Finset.mem_image.mp hxS with ⟨d, hdV, rfl⟩
        exact Finset.mem_image.mpr ⟨d, by simp [U, hdV, hxT], rfl⟩
    have hUsum : ∑ d ∈ U, ρ d = 0 := by
      calc
        ∑ d ∈ U, ρ d = ∑ x ∈ U.image ρ, x := by
          exact (Finset.sum_image (f := fun x : ZMod k ↦ x) (hρinj.mono hUV)).symm
        _ = ∑ x ∈ T, x := by rw [himage]
        _ = 0 := hTsum
    let A : ℤ := ∑ d ∈ U, round ((k : ℝ) * (b : ℝ) ^ d * γ)
    have hAcast : ((A : ℤ) : ZMod k) = 0 := by
      dsimp [A, ρ, nearestResidue] at hUsum ⊢
      push_cast at hUsum ⊢
      exact hUsum
    have hAdvd : (k : ℤ) ∣ A :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAcast
    rcases hAdvd with ⟨z, hz⟩
    let n : ℕ := digitValue b U
    have hUrange : U ⊆ Finset.range (r + 1) := by
      intro d hdU
      have hdV := hUV hdU
      exact (Finset.mem_filter.mp hdV).1
    have hnup : IsDigitRestrictedUpTo b r n :=
      ⟨U, mem_digitSubsets.mpr hUrange, rfl⟩
    have hnstar : IsDigitRestrictedStarUpTo b r n := Or.inl hnup
    have hnne : n ≠ 0 := digitValue_ne_zero (by omega : 0 < b) hUne
    have hncast : (n : ℝ) = ∑ d ∈ U, (b : ℝ) ^ d := by
      simp [n, digitValue]
    have hzreal : (A : ℝ) = (k : ℝ) * (z : ℝ) := by exact_mod_cast hz
    have harg : (k : ℝ) * (γ * (n : ℝ) - (z : ℝ)) =
        ∑ d ∈ U,
          ((k : ℝ) * (b : ℝ) ^ d * γ -
            (round ((k : ℝ) * (b : ℝ) ^ d * γ) : ℝ)) := by
      rw [hncast, mul_sub, ← mul_assoc, Finset.mul_sum]
      rw [Finset.sum_sub_distrib]
      have hfirst :
          ∑ x ∈ U, (k : ℝ) * γ * (b : ℝ) ^ x =
            ∑ x ∈ U, (k : ℝ) * (b : ℝ) ^ x * γ := by
        apply Finset.sum_congr rfl
        intro d hd
        ring
      rw [hfirst]
      have hround :
          ∑ x ∈ U, (round ((k : ℝ) * (b : ℝ) ^ x * γ) : ℝ) = (A : ℝ) := by
        simp [A]
      rw [hround, hzreal]
    have herr : |(k : ℝ) * (γ * (n : ℝ) - (z : ℝ))| ≤ (U.card : ℝ) * β := by
      rw [harg]
      calc
        |∑ d ∈ U, ((k : ℝ) * (b : ℝ) ^ d * γ -
            (round ((k : ℝ) * (b : ℝ) ^ d * γ) : ℝ))| ≤
            ∑ d ∈ U, |((k : ℝ) * (b : ℝ) ^ d * γ -
              (round ((k : ℝ) * (b : ℝ) ^ d * γ) : ℝ))| := by
          simpa [Real.norm_eq_abs] using norm_sum_le U
            (fun d ↦ ((k : ℝ) * (b : ℝ) ^ d * γ -
              (round ((k : ℝ) * (b : ℝ) ^ d * γ) : ℝ)))
        _ ≤ ∑ _d ∈ U, β := by
          apply Finset.sum_le_sum
          intro d hdU
          change circleNorm ((k : ℝ) * (b : ℝ) ^ d * γ) ≤ β
          exact (mem_smallPositions.mp (hUV hdU)).2
        _ = (U.card : ℝ) * β := by simp
    have hUcard : U.card ≤ k := by
      calc
        U.card = T.card := by
          rw [← himage, Finset.card_image_iff.mpr (hρinj.mono hUV)]
        _ ≤ Fintype.card (ZMod k) := Finset.card_le_univ T
        _ = k := ZMod.card k
    have hkreal : (0 : ℝ) < k := by positivity
    have hdist : |γ * (n : ℝ) - (z : ℝ)| ≤ β := by
      rw [abs_mul, abs_of_pos hkreal] at herr
      have hcardreal : (U.card : ℝ) ≤ k := by exact_mod_cast hUcard
      have hβnonneg : 0 ≤ β := hβ.le
      calc
        |γ * (n : ℝ) - (z : ℝ)| ≤ (U.card : ℝ) * β / (k : ℝ) :=
          (le_div_iff₀ hkreal).2 (by simpa [mul_comm] using herr)
        _ ≤ β := by
          rw [div_le_iff₀ hkreal]
          simpa [mul_comm] using mul_le_mul_of_nonneg_right hcardreal hβnonneg
    have hcircle : circleNorm (γ * n) ≤ β :=
      (circleNorm_le_abs_sub_int (γ * n) z).trans (by simpa using hdist)
    exact (not_lt_of_ge hcircle) (havoid n hnstar hnne)

end DigitRestricted
