/- Copyright (c) 2026 Sil (layout, Apache-2.0); 46-step density-split chain, 27 Oct 2026.
The candidate bound 4369779/5000000 = 0.8739558 for all Dirichlet L-functions, with the principal pole excluded.
The proof is `QRH.SilDensitySplit.K15.dirichlet_nonvanishing` (Submissions/density_split_fine_chain/Theorem.lean). -/
import Submissions.density_split_fine_chain.Theorem

set_option autoImplicit false

namespace Candidate

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4369779 / 5000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.SilDensitySplit.K15.dirichlet_nonvanishing χ hs hpole

end Candidate
