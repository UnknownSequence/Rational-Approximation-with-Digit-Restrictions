import Formalization.StarEstimate

/-!
# Theorem `main1`

The final theorem will be closed here by combining the analytic theorem
`starEstimate` from `Formalization.StarEstimate` with the already checked
`main1_of_starEstimate` reduction from `Formalization.Core`.
-/

namespace DigitRestricted

/-- The theorem labelled `main1` in the paper. -/
theorem main1 {b : ℕ} (hb : 2 ≤ b) : Main1Statement b :=
  main1_of_starEstimate hb (starEstimate hb)

end DigitRestricted
