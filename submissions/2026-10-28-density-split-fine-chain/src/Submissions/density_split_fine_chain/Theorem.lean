/- Copyright (c) 2026 Sil (layout, Apache-2.0); 46-step density-split chain, 27 Oct 2026.
Unconditional Dirichlet nonvanishing for Re s > 4369779/5000000 = 0.8739558, with the principal pole excluded:
the k15 source chain (`Source/ChainK15.lean`, Sil's generic steps with new step instances) closed by Sil's
all-shift return at retuned constants (`Return/`, a copy of Sil's with regenerated rows). -/
import Submissions.density_split_fine_chain.Source.ChainK15
import Submissions.density_split_fine_chain.Return.Endpoint

set_option autoImplicit false
namespace QRH.SilDensitySplit.K15

theorem dirichlet_nonvanishing {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4369779 / 5000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.SilDensitySplit.Return.dirichlet_of_source (fun hβ => QRH.SilDensitySplit.K15.final_source hβ) χ hs hpole

end QRH.SilDensitySplit.K15
