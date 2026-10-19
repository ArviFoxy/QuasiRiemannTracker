/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0.
All-moduli Dirichlet export from the two-stage endpoint theorem. -/
import Candidate.Uneven.EndpointRecord

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Final
noncomputable section
open scoped _root_.DirichletCharacter

theorem hecke_nonzero (χ : HeckeFamily.Character) (s : ℂ)
    (hs : (874828524351/1000000000000:ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    (RecordEndpoint.beta_le_rational.trans_lt hs) hpole

theorem allDirichlet {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (874828524351/1000000000000:ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Cycle25.dirichlet_of_hecke (by norm_num) hecke_nonzero χ s hs hpole

end
end OAI.SevenEighths.UnevenEndpoint.Final
#print axioms OAI.SevenEighths.UnevenEndpoint.Final.allDirichlet
