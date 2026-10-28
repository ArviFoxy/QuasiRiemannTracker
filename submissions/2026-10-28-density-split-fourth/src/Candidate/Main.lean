/- Copyright (c) 2026 Rohan Arun. Apache-2.0.
The candidate bound 873981/1000000 = 0.873981 for all Dirichlet L-functions, with the
principal pole excluded. The proof is `QRH.DensitySplitThird.dirichlet_nonvanishing`
(Submissions/density_split_fourth/Theorem.lean), a modification of Sil's PR83
(sil-density-split-20261026, Apache-2.0) with a fourth density-split transition. -/
import Submissions.density_split_fourth.Theorem

set_option autoImplicit false

namespace Candidate

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (873981 / 1000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.DensitySplitThird.dirichlet_nonvanishing χ hs hpole

end Candidate
