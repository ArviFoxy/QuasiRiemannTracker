/-
Copyright (c) 2026 QuasiRiemannTracker contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Independently stated theta-one targets for a separate Comparator challenge
environment. Mathlib proves these targets directly.
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace QRH

theorem canonical_bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1 / 1 : ℝ) < s.re) (_hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  have hs' : (1 : ℝ) < s.re := by simpa only [div_one] using hs
  exact (DirichletCharacter.LFunction_eq_LSeries χ hs').symm ▸
    DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs'

theorem zeta_bound {s : ℂ} (hs : (1 / 1 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  exact riemannZeta_ne_zero_of_one_lt_re (by simpa only [div_one] using hs)

end QRH

#print axioms QRH.canonical_bound
#print axioms QRH.zeta_bound
