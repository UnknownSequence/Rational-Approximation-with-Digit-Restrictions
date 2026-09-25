import Lake
open Lake DSL

package «Rational-Approximation-with-Digit-Restrictions» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

lean_lib Formalization

@[default_target]
lean_exe «Rational-Approximation-with-Digit-Restrictions» where
  root := `Main
