/- The marked density-split leaf of this package at the floor `qf = 3/5`.

`Density.density_priced_source_marked` is `Density.density_priced_source` with PR 76's
repeated-mark HIGH count: the price is `Density.markedDensityPrice`, whose HIGH term is the unmarked
`highTerm` reduced by the gain `gainC ν B₀ L₀ c₀ s M`; the parent face is restricted to
`22/23 ≤ B₀ ≤ 1`, `1 < L₀`, `0 ≤ c₀ < 1` (the range of the pivot
`actual_dictionary_regular_raw_max_uniform_tau_rm`). This file instantiates it at `qf = 3/5`
(real parts `a ≥ 4/5`) and checks the axioms of the new theorems. -/
import Submissions.arvi_density.Density.LeafMarked

set_option autoImplicit false
namespace QRH.ArviDensity
noncomputable section
open OAI OAI.SevenEighths
open QRH.SilDensitySplit.CubeFree

/-- **Marked density Seam A at the floor `qf = 3/5`.** -/
theorem density_priced_source_marked_three_fifths (B₀ L₀ c₀ L A D s₀ Mmin Mmax Lplain : ℝ)
    (hL : 1 < L₀) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hface : 22/23 ≤ B₀ ∧ B₀ ≤ 1 ∧ 0 ≤ c₀ ∧ c₀ < 1) (h0 : 0 < Mmin) (h1 : Mmin ≤ Mmax)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    PricedPackedSource
      (Density.markedDensityPrice (3/5) B₀ L₀ c₀ L A D s₀ hL hface (by norm_num) (by norm_num))
      Mmin Mmax Lplain :=
  Density.density_priced_source_marked (3/5) B₀ L₀ c₀ L A D s₀ Mmin Mmax Lplain hL (by norm_num)
    (by norm_num) hβ hface h0 h1 hparent

end
end QRH.ArviDensity

#print axioms QRH.ArviDensity.Density.high_class_sum_marked
#print axioms QRH.ArviDensity.Density.high_exceptional_count
#print axioms QRH.ArviDensity.Density.high_row_plain_factor
#print axioms QRH.ArviDensity.Density.high_slot_bound
#print axioms QRH.ArviDensity.Density.energy_le_class_sums
#print axioms QRH.ArviDensity.Density.markedDensityPrice
#print axioms QRH.ArviDensity.Density.markedDensityPrice_le
#print axioms QRH.ArviDensity.Density.high_branch_marked
#print axioms QRH.ArviDensity.Density.density_priced_source_marked
#print axioms QRH.ArviDensity.density_priced_source_marked_three_fifths
