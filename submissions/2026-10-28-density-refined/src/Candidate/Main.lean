/- Wider density range, exact bound 8739461/10000000 = 0.8739461.
AI-assisted (OpenAI Codex), 2026-10-28; Apache-2.0. -/
import Submissions.density_refined.Theorem
set_option autoImplicit false
namespace Candidate
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (8739461 / 10000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.DensityRefined.dirichlet_nonvanishing χ hs hpole
end Candidate
