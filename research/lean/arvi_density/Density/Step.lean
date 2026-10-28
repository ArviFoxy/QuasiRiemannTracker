/- The density-split step with the floor `qf`, accepted by Sil's generic cube-free engine.

For a density transition `G(B₀,L₀,c₀) → G(B,L,c)` certified by this package's `HybridGates qf …`
(floor `qf ∈ [1/2, 3/4]`):

* `dsGates` (`Density/StepGates`) shows that the step data `dsData qf …` satisfy the generic
  `StepGates` of the engine;
* `density_priced_source` (`Density/Leaf`) is the Seam A leaf with the price `densityPrice qf …`;
  `density_leaf` states it at the envelope `[Hmin, Hmax + 1] = [9/10, 4]` of `dsData`;
* the engine's `cubefree_step`, with the root chain's raw-side provider and the diagonal supplier
  `diag_supply` (both for an arbitrary `StepGates`, as in `Assembly.Closed`), then gives the source
  `G(B,L,c)` from the parent source `G(B₀,L₀,c₀)`: `density_step`.

Only the floor-bearing modules are forked; the engine (`CubeFree`) is Sil's. -/
import Submissions.arvi_density.Density.Leaf
import Submissions.arvi_density.Density.StepGates
import Submissions.sil_density_split_20261026.CubeFree.Assembly.Provider
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeoSupply
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9

set_option autoImplicit false
namespace QRH.ArviDensity.Density
noncomputable section
open OAI OAI.SevenEighths
open QRH.SilDensitySplit.CubeFree

/-- **The density leaf of a step at the floor `qf`:** the Seam A leaf with the price of `dsData qf …`
at its envelope `[Hmin, Hmax + 1]`. -/
theorem density_leaf (qf B₀ L₀ c₀ B L c A D Lplain : ℝ) (hL : 0 < L₀) (hqf : 1/2 ≤ qf)
    (hqf' : qf ≤ 3/4) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hface : 0 < B₀ ∧ B₀ ≤ 1 ∧ 0 < c₀)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    PricedPackedSource (dsData qf B₀ L₀ c₀ B L c A D hL (by linarith) hqf').price
      (dsData qf B₀ L₀ c₀ B L c A D hL (by linarith) hqf').Hmin
      ((dsData qf B₀ L₀ c₀ B L c A D hL (by linarith) hqf').Hmax + 1) Lplain :=
  density_priced_source qf B₀ L₀ c₀ L A D _ _ _ Lplain hL hqf hqf' hβ hface
    (by norm_num [dsData]) (by norm_num [dsData]) hparent

/-- **The density-split step at the floor `qf ∈ [1/2, 3/4]`.** If the transition
`G(B₀,L₀,c₀) → G(B,L,c)` with selection `A`, `D` is certified by `HybridGates qf …` (and the face
facts `DSFace`, `0 < B₀`), the generic cube-free engine turns the parent source into the child
source, under the contrary hypothesis `51/100 ≤ β`. -/
theorem density_step (qf B₀ L₀ c₀ B L c A D : ℝ) (hL : 0 < L₀) (hqf : 1/2 ≤ qf)
    (hqf' : qf ≤ 3/4) (hB₀ : 0 < B₀) (h : HybridGates qf B₀ L₀ c₀ B L c A D)
    (hF : DSFace B₀ L₀ c₀ B L c) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    QRH.Record1252270103Source.GlobalSource B L c := by
  have hq0 : 0 ≤ qf := by linarith
  have G := dsGates h hF hL hq0 hqf'
  have hc₀ : 0 < c₀ := lt_of_le_of_lt hF.cross_nonneg h.dsCross_lt_c₀
  have hleaf := density_leaf qf B₀ L₀ c₀ B L c A D 4 hL hqf hqf' hβ ⟨hB₀, hF.B₀_lt.le, hc₀⟩
    hparent
  exact cubefree_step (dsData qf B₀ L₀ c₀ B L c A D hL hq0 hqf') G 4
    (Assembly.step_inputs_of_provider _ G 4 fun _ hl =>
      Second.Provider.contrary_raw_side_provider G 4 le_rfl hl
        (Second.ProviderDiag.diag_supply G)) hβ hparent hleaf

end
end QRH.ArviDensity.Density
