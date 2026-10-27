/- Copyright (c) 2026 Sil. Apache-2.0.
The candidate bound 174799/200000 = 0.873995 for all Dirichlet L-functions, with the
principal pole excluded. The proof is `QRH.SilDensitySplit.dirichlet_nonvanishing`
(Submissions/sil_density_split_20261026/Theorem.lean). -/
import Submissions.sil_density_split_20261026.Theorem

set_option autoImplicit false

namespace Candidate

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (174799 / 200000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.SilDensitySplit.dirichlet_nonvanishing χ hs hpole

end Candidate
