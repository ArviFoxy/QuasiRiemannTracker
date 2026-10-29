/- All-moduli Dirichlet nonvanishing for Re(s) > 43693617/50000000 = 0.87387234 (principal pole excluded):
the floor-1/2 marked density chain (repeated-mark HIGH leaf) and the five-branch return. -/
import Submissions.arvi_density.FinalF50
set_option autoImplicit false
namespace Candidate
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (43693617 / 50000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.ArviDensity.dirichlet_nonvanishing_f50 χ hs hpole
end Candidate
