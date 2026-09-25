# Rational Approximation with Digit Restrictions

This is a Lean 4 + mathlib project for the theorem labelled `main1` in
*Rational Approximation with digit-restricted denominators*.

## Assumption

We only assume Olson's Corollary 3.2.1. It is declared as
`DigitRestricted.olsonCorollary` and is the sole project-specific axiom. The
paper's cited Baker lower bound is not assumed: it is replaced by the proved
finite Fejér-kernel argument in `Formalization/BakerLowerBound.lean`.

- `Formalization/Core.lean` contains the formal statement, the permitted Olson
  Corollary 3.2.1 axiom, the `Addcomb` specialization, the exponential
  character, and the checked reduction from `𝔇_b^*` to `𝔇_b`.
- `Formalization/BoundedDigits.lean` models the finite digit blocks.
- `Formalization/CircleDistance.lean` and `Formalization/Annuli.lean` prove the
  nearest-integer and annulus propagation lemmas.
- `Formalization/SmallFrequencies.lean` proves `Addcomb2` from Olson.
- `Formalization/ExponentialProduct.lean`, `Formalization/DigitSumUpper.lean`,
  and `Formalization/AnnulusCounting.lean` prove the product factorization and
  the Olson-to-decay upper-bound chain.
- `Formalization/BakerLowerBound.lean` develops an explicit Fejér-kernel
  replacement for the paper's cited Baker theorem, including the geometric-sum
  estimate, finite Fourier expansion, energy calculation, and positive-frequency
  mass lower bound.
- `Formalization/ExponentialContradiction.lean` joins that lower bound to the
  digit-product upper bound. `Formalization/NumericalEstimates.lean` proves the
  remaining square-root-scale numerical estimates and the finite approximation
  theorem.
- `Formalization/GlobalScale.lean` converts the finite digit scale into an
  inverse-square bound. `Formalization/StarEstimate.lean` proves the enlarged-set
  estimate, and `Formalization/MainTheorem.lean` proves `DigitRestricted.main1`.
- Mathlib is pinned to `v4.34.0`, matching the local Lean toolchain.
- Run `lake build` to compile the project.

The project contains no `sorry` and no additional project-specific axiom.
`DigitRestricted.main1` depends on Olson's corollary together with Lean's
standard logical infrastructure (`propext`, `Classical.choice`, and
`Quot.sound`).
