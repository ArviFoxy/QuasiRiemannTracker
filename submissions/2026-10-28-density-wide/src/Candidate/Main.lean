/- Wider density range, exact bound 1747893/2000000 = 0.8739465.
AI-assisted (OpenAI Codex), 2026-10-28; Apache-2.0. -/
import Submissions.density_wide.Theorem
set_option autoImplicit false
namespace Candidate
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1747893 / 2000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.DensityWide.dirichlet_nonvanishing χ hs hpole
end Candidate
