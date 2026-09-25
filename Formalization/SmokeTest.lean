namespace Formalization

/-- A tiny theorem used to confirm that the local Lean compiler works. -/
theorem smokeTest (p : Prop) (hp : p) : p := by
  exact hp

end Formalization
