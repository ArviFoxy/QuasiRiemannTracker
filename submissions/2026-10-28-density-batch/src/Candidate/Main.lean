/- Wider density range, exact bound 436972583/500000000 = 0.873945166.
AI-assisted (OpenAI Codex), 2026-10-28; Apache-2.0. -/
import Submissions.density_batch.Theorem
set_option autoImplicit false
namespace Candidate
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (436972583 / 500000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.DensityBatch.dirichlet_nonvanishing χ hs hpole
end Candidate
