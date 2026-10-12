import Mathlib.NumberTheory.LSeries.DirichletContinuation
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge

namespace SinglePrime2933

theorem allDirichlet {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (29 / 33 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  sorry

theorem zeta {s : ℂ} (hs : (29 / 33 : ℝ) < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  sorry

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : (29 / 33 : ℝ) < s.re) (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  sorry

end SinglePrime2933
