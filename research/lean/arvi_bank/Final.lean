/-
Research bank (2026-10-30): the engineering limit of the selected-leaf architecture.

The selected-leaf line of `Submissions.arvi_selected_leaf` is continued from `401/200` down to `20001/10000`
(`Submissions.arvi_bank.Curve`: deletion cut `K = 500001/1000000`, the bottom of R1's range, selected fraction
`a = 1/100000`). Its end face `G(99999/100000, 20001/10000, 33571/250000)` supplies both the count windows and the
capped physical windows of the return, retuned at `h = 8097/10000` (`Tuning/`, three windows). The return reads the
forked transport (`ReturnD/`), whose coarse box `BoundsN` allows `h < 81/100` and whose floor margin is `1/1000`.
-/
import Submissions.arvi_selected_leaf.Notices
import Submissions.arvi_bank.Curve
import Submissions.arvi_selected_leaf.R1.Cap
import Submissions.arvi_bank.Tuning.Endpoint

set_option autoImplicit false
namespace QRH.ArviBank
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source QRH.ArviSelectedLeaf

/-- R1 at the cut `K = 500001/1000000` of the continued line. -/
theorem selectedRootEnergy_sK : SelectedRootEnergy sK :=
  selectedRootEnergy sK (by unfold sK; norm_num) (by unfold sK; norm_num)

/-- The end face of the continued line with its cap as the literal `33571/250000`. -/
theorem e5_end_cap (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999/100000) (20001/10000) (33571/250000) := by
  have e : (1/10 + 3/50 * (5143/2000 - 20001/10000) : ℝ) = 33571/250000 := by norm_num
  have h := e5_end hR1 hβ
  rwa [e] at h

/-- **The endpoint bound**: `β ≤ θ = 43669114/50000000 = 0.87338228`. -/
theorem beta_le_theta : HeckeZeroSupremum.beta ≤ (43669114/50000000 : ℝ) :=
  QRH.ArviDensity.Return.Tuning.beta_le_theta_of_sources (fun hβ => e5_end_cap selectedRootEnergy_sK hβ)
    (fun hβ => e5_end_cap selectedRootEnergy_sK hβ)

/-- **All-moduli Dirichlet nonvanishing** for `Re s > 43669114/50000000 = 0.87338228`. -/
theorem dirichlet_nonvanishing_bank {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (43669114 / 50000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.ArviDensity.Return.Tuning.dirichlet_of_sources (fun hβ => e5_end_cap selectedRootEnergy_sK hβ)
    (fun hβ => e5_end_cap selectedRootEnergy_sK hβ) χ hs hpole

end
end QRH.ArviBank

#print axioms QRH.ArviBank.beta_le_theta
#print axioms QRH.ArviBank.dirichlet_nonvanishing_bank
