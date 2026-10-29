/- Wider density range with separate physical and count sources.
Builds on OpenAI, Hailey Collet, Sil, ArviFoxy and Jacob Sussman (Apache-2.0).
AI-assisted (OpenAI Codex), 2026-10-28. Uses the preprint's 7/8 theorem. -/
import Submissions.density_wide.Source.Chain
import Submissions.density_wide.Source.Physical
import Submissions.density_wide.Return.Endpoint
set_option autoImplicit false
namespace QRH.DensityWide
theorem dirichlet_nonvanishing {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1747893 / 2000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  Return.dirichlet_of_sources final_source physical_source χ hs hpole
end QRH.DensityWide
