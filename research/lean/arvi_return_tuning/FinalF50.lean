/- All-moduli Dirichlet nonvanishing for `Re s > 43693617/50000000 = 0.87387234`, as in
`Submissions.arvi_density.FinalF50`, with the return certified reflectively: five windows checked by one
kernel computation (`Windows.lean`) and the four conductor edges by kernel-computed covers
(`EdgeCertificates.lean`), in place of `Rows/Admission01..31`, `Rows/Edge_*` and the cover trees.
Count source: the end of the floor-1/2 marked density chain (`ChainF50`); physical source: its step 64. -/
import Submissions.arvi_density.ChainF50.Chain
import Submissions.arvi_return_tuning.Endpoint

set_option autoImplicit false
namespace QRH.ArviReturnTuning
noncomputable section

theorem dirichlet_nonvanishing_f50 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (43693617 / 50000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.ArviDensity.Return.Tuning.dirichlet_of_sources (fun hβ => QRH.ArviDensity.ChainF50.final_source hβ)
    (fun hβ => QRH.ArviDensity.ChainF50.source_64 hβ) χ (by norm_num at hs ⊢; linarith) hpole

end
end QRH.ArviReturnTuning

#print axioms QRH.ArviReturnTuning.dirichlet_nonvanishing_f50
