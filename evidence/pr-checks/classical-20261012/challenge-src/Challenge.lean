import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace QRH

theorem canonical_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1 / 1 : ℝ) < s.re) (_hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  sorry

theorem zeta_bound {s : ℂ} (hs : (1 / 1 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  sorry

end QRH
