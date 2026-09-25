import Formalization.Core

/-!
# Finite digit blocks

This file gives the finite-set model of the paper's sets
`\mathfrak D_b(r)` and `\mathfrak D_b^*(r)`.  We index a digit sum by the
subset of positions where the digit is one.  Keeping the subset as the index
is useful for exponential sums: the product expansion is then literal and
does not require repeatedly proving uniqueness of base-`b` expansions.
-/

open scoped BigOperators

noncomputable section

namespace DigitRestricted

/-- The value represented by putting a digit `1` in each position in `s`. -/
def digitValue (b : ℕ) (s : Finset ℕ) : ℕ :=
  ∑ d ∈ s, b ^ d

/-- All subsets of the positions `0, …, r`. -/
def digitSubsets (r : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (r + 1)).powerset

/-- Membership in the truncated set `𝔇_b(r)`. -/
def IsDigitRestrictedUpTo (b r n : ℕ) : Prop :=
  ∃ s ∈ digitSubsets r, n = digitValue b s

/-- Membership in the truncated enlarged set `𝔇_b^*(r)`. -/
def IsDigitRestrictedStarUpTo (b r n : ℕ) : Prop :=
  IsDigitRestrictedUpTo b r n ∨
    ∃ c d : ℕ, c ≤ r ∧ d ≤ r ∧ c < d ∧ n = b ^ d - b ^ c

@[simp] theorem digitValue_empty (b : ℕ) : digitValue b ∅ = 0 := by
  simp [digitValue]

theorem digitValue_insert {b d : ℕ} {s : Finset ℕ} (hd : d ∉ s) :
    digitValue b (insert d s) = b ^ d + digitValue b s := by
  simp [digitValue, hd]

@[simp] theorem mem_digitSubsets {r : ℕ} {s : Finset ℕ} :
    s ∈ digitSubsets r ↔ s ⊆ Finset.range (r + 1) := by
  simp [digitSubsets]

theorem mem_range_of_mem_digitSubsets {r d : ℕ} {s : Finset ℕ}
    (hs : s ∈ digitSubsets r) (hd : d ∈ s) : d ≤ r := by
  have := (mem_digitSubsets.mp hs) hd
  simpa using this

theorem digitValue_isDigitRestricted (b : ℕ) (s : Finset ℕ) :
    IsDigitRestricted b (digitValue b s) := by
  exact ⟨s, rfl⟩

theorem IsDigitRestrictedUpTo.isDigitRestricted {b r n : ℕ}
    (h : IsDigitRestrictedUpTo b r n) : IsDigitRestricted b n := by
  rcases h with ⟨s, -, rfl⟩
  exact digitValue_isDigitRestricted b s

theorem IsDigitRestrictedStarUpTo.isDigitRestrictedStar {b r n : ℕ}
    (h : IsDigitRestrictedStarUpTo b r n) : IsDigitRestrictedStar b n := by
  rcases h with h | ⟨c, d, -, -, hcd, rfl⟩
  · exact Or.inl h.isDigitRestricted
  · exact Or.inr ⟨c, d, hcd, rfl⟩

theorem digitValue_pos {b : ℕ} (hb : 0 < b) {s : Finset ℕ} (hs : s.Nonempty) :
    0 < digitValue b s := by
  rw [digitValue]
  exact Finset.sum_pos (fun _ _ ↦ pow_pos hb _) hs

theorem digitValue_ne_zero {b : ℕ} (hb : 0 < b) {s : Finset ℕ} (hs : s.Nonempty) :
    digitValue b s ≠ 0 := (digitValue_pos hb hs).ne'

theorem digitValue_mono {b : ℕ} {s t : Finset ℕ} (hst : s ⊆ t) :
    digitValue b s ≤ digitValue b t := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ ↦ Nat.zero_le _)

theorem digitValue_le_fullBlock {b r : ℕ} {s : Finset ℕ}
    (hs : s ∈ digitSubsets r) :
    digitValue b s ≤ digitValue b (Finset.range (r + 1)) :=
  digitValue_mono (mem_digitSubsets.mp hs)

@[simp] theorem card_digitSubsets (r : ℕ) :
    (digitSubsets r).card = 2 ^ (r + 1) := by
  simp [digitSubsets]

@[simp] theorem empty_mem_digitSubsets (r : ℕ) : ∅ ∈ digitSubsets r := by
  simp [digitSubsets]

theorem digitSubsets_erase_empty_card (r : ℕ) :
    ((digitSubsets r).erase ∅).card = 2 ^ (r + 1) - 1 := by
  rw [Finset.card_erase_of_mem (empty_mem_digitSubsets r), card_digitSubsets]

theorem digitValue_mem_upTo {b r : ℕ} {s : Finset ℕ}
    (hs : s ∈ digitSubsets r) :
    IsDigitRestrictedUpTo b r (digitValue b s) :=
  ⟨s, hs, rfl⟩

theorem powerDifference_mem_starUpTo {b r c d : ℕ}
    (hc : c ≤ r) (hd : d ≤ r) (hcd : c < d) :
    IsDigitRestrictedStarUpTo b r (b ^ d - b ^ c) := by
  exact Or.inr ⟨c, d, hc, hd, hcd, rfl⟩

/-- Every member of the truncated enlarged digit set is below the next power
of the base. -/
theorem IsDigitRestrictedStarUpTo.le_pow_succ
    {b r n : ℕ} (hb : 2 ≤ b) (h : IsDigitRestrictedStarUpTo b r n) :
    n ≤ b ^ (r + 1) := by
  rcases h with ⟨s, hs, rfl⟩ | ⟨c, d, hc, hd, hcd, rfl⟩
  · have hmono := digitValue_le_fullBlock (b := b) hs
    have hgeom := geomBlock_mul (c := 0) (d := r + 1) hb (by omega)
    have hfull : digitValue b (Finset.range (r + 1)) =
        ∑ i ∈ Finset.Ico 0 (r + 1), b ^ i := by
      simp [digitValue]
    rw [hfull] at hmono
    have hsum : (∑ i ∈ Finset.Ico 0 (r + 1), b ^ i) ≤ b ^ (r + 1) := by
      calc
        (∑ i ∈ Finset.Ico 0 (r + 1), b ^ i) ≤
            (b - 1) * ∑ i ∈ Finset.Ico 0 (r + 1), b ^ i :=
          Nat.le_mul_of_pos_left _ (by omega)
        _ = b ^ (r + 1) - b ^ 0 := hgeom
        _ ≤ b ^ (r + 1) := Nat.sub_le _ _
    exact hmono.trans hsum
  · have hbpos : 0 < b := by omega
    have hpow : b ^ d ≤ b ^ (r + 1) :=
      Nat.pow_le_pow_right hbpos (by omega)
    omega

end DigitRestricted
