/- The marked density-split step with the floor `qf`, accepted by Sil's generic cube-free engine.

For a density transition `G(B₀,L₀,c₀) → G(B,L,c)` certified by this package's `HybridGatesM qf …`
(floor `qf ∈ [1/2, 3/4]`, parent face `22/23 ≤ B₀`):

* `dsGatesM` (`Density/StepGatesMarked`) shows that the step data `dsDataM qf …` (the data of
  `dsData` with the price `markedDensityPrice`, whose HIGH term is reduced by PR 76's repeated-mark
  gain) satisfy the generic `StepGates` of the engine;
* `density_priced_source_marked` (`Density/LeafMarked`) is the Seam A leaf with that price;
  `density_leaf_marked` states it at the envelope `[Hmin, Hmax + 1] = [9/10, 4]` of `dsDataM`;
* the engine's `cubefree_step`, with the root chain's raw-side provider and the diagonal supplier
  `diag_supply` (both for an arbitrary `StepGates`, as in `Density/Step`), then gives the source
  `G(B,L,c)` from the parent source `G(B₀,L₀,c₀)`: `density_step_marked`.

The face facts `1 < L₀`, `0 ≤ c₀ < 1` of the marked price follow from `DSFace` and the gates; the
only additional hypothesis on the parent is `22/23 ≤ B₀`. Every `HybridGates` is a `HybridGatesM`
(`HybridGatesM.ofHybridGates`), so each certified unmarked step is also a marked step
(`density_step_marked_of_hybridGates`). -/
import Submissions.arvi_density.Density.LeafMarked
import Submissions.arvi_density.Density.StepGatesMarked
import Submissions.sil_density_split_20261026.CubeFree.Assembly.Provider
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeoSupply
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9

set_option autoImplicit false
namespace QRH.ArviDensity.Density
noncomputable section
open OAI OAI.SevenEighths
open QRH.SilDensitySplit.CubeFree

/-- **The marked density leaf of a step at the floor `qf`:** the Seam A leaf with the price of
`dsDataM qf …` at its envelope `[Hmin, Hmax + 1]`. -/
theorem density_leaf_marked (qf B₀ L₀ c₀ B L c A D Lplain : ℝ) (hL : 1 < L₀) (hqf : 1/2 ≤ qf)
    (hqf' : qf ≤ 3/4) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hface : 22/23 ≤ B₀ ∧ B₀ ≤ 1 ∧ 0 ≤ c₀ ∧ c₀ < 1)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    PricedPackedSource (dsDataM qf B₀ L₀ c₀ B L c A D hL hface hqf hqf').price
      (dsDataM qf B₀ L₀ c₀ B L c A D hL hface hqf hqf').Hmin
      ((dsDataM qf B₀ L₀ c₀ B L c A D hL hface hqf hqf').Hmax + 1) Lplain :=
  density_priced_source_marked qf B₀ L₀ c₀ L A D _ _ _ Lplain hL hqf hqf' hβ hface
    (by norm_num [dsDataM]) (by norm_num [dsDataM]) hparent

/-- **The marked density-split step at the floor `qf ∈ [1/2, 3/4]`.** If the transition
`G(B₀,L₀,c₀) → G(B,L,c)` with selection `A`, `D` is certified by `HybridGatesM qf …` (with the face
facts `DSFace` and `22/23 ≤ B₀`), the generic cube-free engine turns the parent source into the
child source, under the contrary hypothesis `51/100 ≤ β`. -/
theorem density_step_marked (qf B₀ L₀ c₀ B L c A D : ℝ) (hqf : 1/2 ≤ qf) (hqf' : qf ≤ 3/4)
    (hB₀ : 22/23 ≤ B₀) (h : HybridGatesM qf B₀ L₀ c₀ B L c A D)
    (hF : DSFace B₀ L₀ c₀ B L c) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    QRH.Record1252270103Source.GlobalSource B L c := by
  have hL : 1 < L₀ := lt_trans hF.one_lt_L hF.L_lt
  have hc₀ : 0 ≤ c₀ := (lt_of_le_of_lt hF.cross_nonneg h.dsCross_lt_c₀).le
  have hface : 22/23 ≤ B₀ ∧ B₀ ≤ 1 ∧ 0 ≤ c₀ ∧ c₀ < 1 :=
    ⟨hB₀, hF.B₀_lt.le, hc₀, by linarith [hF.c₀_lt]⟩
  have G := dsGatesM h hF hL hface hqf hqf'
  have hleaf := density_leaf_marked qf B₀ L₀ c₀ B L c A D 4 hL hqf hqf' hβ hface hparent
  exact cubefree_step (dsDataM qf B₀ L₀ c₀ B L c A D hL hface hqf hqf') G 4
    (Assembly.step_inputs_of_provider _ G 4 fun _ hl =>
      Second.Provider.contrary_raw_side_provider G 4 le_rfl hl
        (Second.ProviderDiag.diag_supply G)) hβ hparent hleaf

/-- Every unmarked certificate gives a marked step (the gain is nonnegative). -/
theorem density_step_marked_of_hybridGates (qf B₀ L₀ c₀ B L c A D : ℝ) (hqf : 1/2 ≤ qf)
    (hqf' : qf ≤ 3/4) (hB₀ : 22/23 ≤ B₀) (h : HybridGates qf B₀ L₀ c₀ B L c A D)
    (hF : DSFace B₀ L₀ c₀ B L c) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    QRH.Record1252270103Source.GlobalSource B L c :=
  density_step_marked qf B₀ L₀ c₀ B L c A D hqf hqf' hB₀ (HybridGatesM.ofHybridGates h) hF hβ hparent

end
end QRH.ArviDensity.Density
