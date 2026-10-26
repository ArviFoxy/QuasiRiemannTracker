import Mathlib
open MulChar
example (F : Type) [Field F] [Fintype F] (χ : MulChar F ℂ) (u : Fˣ) : ((equivToUnitHom χ u : ℂˣ) : ℂ) = χ u := by
  exact?
example (u : ℂ) (x : ℂ) (hu : u ≠ 0) : (Equiv.mulLeft₀ u hu) x = u * x := by
  exact?
