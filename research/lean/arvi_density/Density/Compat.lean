/- The floor `qf = 13/20` as a special case of the floor-`qf` density step.

PR 83's certified gates `QRH.SilDensitySplit.HybridGates` (floor `13/20`, the 46 certificates of PR 86
included) are `QRH.ArviDensity.HybridGates (13/20)`: the two structures have the same fields, the
floor gate being `dens - 13/20` in both, and the scalar definitions (`cross`, `dens`, `sel`, …) of the
two `Hybrid` namespaces unfold to the same terms. Hence the fork recovers Sil's step gates, step data
and density price at `qf = 13/20`:

* `HybridGates.mono_floor`: lowering the floor only weakens the floor gate;
* `HybridGates.ofSil`, `HybridGates.ofSil_of_le`: Sil's gates are the fork's gates at `qf = 13/20`,
  and at every floor `qf ≤ 13/20` (in particular `3/5`);
* `densityPrice_thirteen_twentieths`, `dsData_thirteen_twentieths`: the fork's price and step data
  at `qf = 13/20` are Sil's (by `rfl`), and `density_priced_source_thirteen_twentieths` is PR 83's
  `density_priced_source` (obtained from the fork's leaf at `qf = 13/20`);
* `dsGates_first_of_floor`, `dsGates_second_of_floor`: the fork's `dsGates` applied to Sil's two
  exact certificates gives `StepGates` of the two PR 83 transitions. -/
import Submissions.arvi_density.Density.StepGates
import Submissions.arvi_density.Density.Leaf
import Submissions.sil_density_split_20261026.Source.HybridCertificates
import Submissions.sil_density_split_20261026.Density.StepGates

set_option autoImplicit false
namespace QRH.ArviDensity
noncomputable section

/-- Lowering the floor only weakens the floor gate: `HybridGates qf` gives `HybridGates qf'`
for `qf' ≤ qf`. -/
theorem HybridGates.mono_floor {qf qf' B0 L0 c0 B L c A D : ℝ} (hqf : qf' ≤ qf)
    (h : HybridGates qf B0 L0 c0 B L c A D) : HybridGates qf' B0 L0 c0 B L c A D :=
  { h with
    q_floor := by
      obtain ⟨r, hr, hfl⟩ := h.q_floor
      refine ⟨r, hr, fun v h0 h1 => ?_⟩
      have := hfl v h0 h1
      unfold Hybrid.gQFloor at this ⊢
      linarith }

/-- Sil's `HybridGates` (floor `13/20`) is the fork's `HybridGates (13/20)`. -/
theorem HybridGates.ofSil {B0 L0 c0 B L c A D : ℝ}
    (h : QRH.SilDensitySplit.HybridGates B0 L0 c0 B L c A D) :
    HybridGates (13/20) B0 L0 c0 B L c A D where
  width_pos := h.width_pos
  sel_den_pos := h.sel_den_pos
  dens_den_pos := h.dens_den_pos
  q_lower := h.q_lower
  q_upper := h.q_upper
  q_floor := h.q_floor
  H_lower := h.H_lower
  retained_cap := h.retained_cap
  retained_width := h.retained_width
  low_identity := h.low_identity
  low_div_eq := h.low_div_eq
  low_per_excess_width := h.low_per_excess_width
  high_at_q := h.high_at_q
  high_density_derivative := h.high_density_derivative
  principal_reference := h.principal_reference
  second_reference := h.second_reference
  second_diagonal := h.second_diagonal
  reference_upper_positive := h.reference_upper_positive
  sel_hasDerivAt := h.sel_hasDerivAt
  selection_monotonicity := h.selection_monotonicity

/-- Sil's `HybridGates` (floor `13/20`) are the fork's `HybridGates qf` for every floor
`qf ≤ 13/20`, in particular for `qf = 3/5`. -/
theorem HybridGates.ofSil_of_le {qf B0 L0 c0 B L c A D : ℝ} (hqf : qf ≤ 13/20)
    (h : QRH.SilDensitySplit.HybridGates B0 L0 c0 B L c A D) :
    HybridGates qf B0 L0 c0 B L c A D :=
  (HybridGates.ofSil h).mono_floor hqf

namespace Density

/-- At `qf = 13/20` the fork's density price is Sil's. -/
theorem densityPrice_thirteen_twentieths (B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 0 < L₀) :
    densityPrice (13/20) B₀ L₀ c₀ L A D s₀ hL (by norm_num) (by norm_num) =
      QRH.SilDensitySplit.Density.densityPrice B₀ L₀ c₀ L A D s₀ hL := rfl

/-- PR 83's `density_priced_source` (floor `13/20`, Cycle61 count) as the fork's leaf at
`qf = 13/20`. -/
theorem density_priced_source_thirteen_twentieths (B₀ L₀ c₀ L A D s₀ Mmin Mmax Lplain : ℝ)
    (hL : 0 < L₀) (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hface : 0 < B₀ ∧ B₀ ≤ 1 ∧ 0 < c₀) (h0 : 0 < Mmin) (h1 : Mmin ≤ Mmax)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    QRH.SilDensitySplit.CubeFree.PricedPackedSource
      (QRH.SilDensitySplit.Density.densityPrice B₀ L₀ c₀ L A D s₀ hL) Mmin Mmax Lplain :=
  density_priced_source (13/20) B₀ L₀ c₀ L A D s₀ Mmin Mmax Lplain hL (by norm_num)
    (by norm_num) hβ hface h0 h1 hparent

/-- At `qf = 13/20` the fork's step data are Sil's. -/
theorem dsData_thirteen_twentieths (B₀ L₀ c₀ B L c A D : ℝ) (hL : 0 < L₀) :
    dsData (13/20) B₀ L₀ c₀ B L c A D hL (by norm_num) (by norm_num) =
      QRH.SilDensitySplit.Density.dsData B₀ L₀ c₀ B L c A D hL := rfl

/-- The fork's `dsGates` applied to Sil's first certificate (floor `13/20`). -/
theorem dsGates_first_of_floor :
    QRH.SilDensitySplit.CubeFree.StepGates
      (dsData (13/20) (9999/10000) (129/50) (3/25) (9959/10000) (5/2) (1/10) (6/5) 140
        (by norm_num) (by norm_num) (by norm_num)) :=
  dsGates (HybridGates.ofSil QRH.SilDensitySplit.hybridGates_first)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ _ _ _

/-- The fork's `dsGates` applied to Sil's second certificate (floor `13/20`). -/
theorem dsGates_second_of_floor :
    QRH.SilDensitySplit.CubeFree.StepGates
      (dsData (13/20) (9959/10000) (5/2) (1/10) (4967/5000) (49/20) (1/10) (7/10) 70
        (by norm_num) (by norm_num) (by norm_num)) :=
  dsGates (HybridGates.ofSil QRH.SilDensitySplit.hybridGates_second)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ _ _ _

end Density

end
end QRH.ArviDensity
