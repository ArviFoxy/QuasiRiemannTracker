/- All-moduli Dirichlet nonvanishing for `Re s > 87387234/100000000 = 0.87387234`.
Count source: the end `G(96232839/100000000, 3853/2000, 1/10)` of the floor-1/2 marked density chain
(`ChainF50`, 129 steps from PR 86's boot face); physical source: its step 64,
`G(49283557/50000000, 4503/2000, 1/10)`; return: the five-branch return of `Return`. -/
import Submissions.arvi_density.ChainF50.Chain
import Submissions.arvi_density.Return.Endpoint

set_option autoImplicit false
namespace QRH.ArviDensity
noncomputable section

theorem dirichlet_nonvanishing_f50 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (87387234 / 100000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  Return.dirichlet_of_sources (fun hβ => ChainF50.final_source hβ) (fun hβ => ChainF50.source_64 hβ) χ
    (by norm_num at hs ⊢; linarith) hpole

end
end QRH.ArviDensity

#print axioms QRH.ArviDensity.dirichlet_nonvanishing_f50
