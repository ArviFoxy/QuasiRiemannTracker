/- Wider density range, exact bound 2731076077/3125000000 = 0.87394434464.
AI-assisted (OpenAI Codex), 2026-10-28; Apache-2.0. -/
import Submissions.density_ten.Theorem
set_option autoImplicit false
namespace Candidate
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (2731076077/3125000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.DensityTen.dirichlet_nonvanishing χ hs hpole
end Candidate
