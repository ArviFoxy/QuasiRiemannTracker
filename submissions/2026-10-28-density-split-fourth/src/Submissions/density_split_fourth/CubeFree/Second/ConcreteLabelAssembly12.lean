/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M2, label assembly, part 12: the final per-split label bound with the box and the
multiplicity absorbed (`split_label_bound_final`):

  `splitLabel(t) ≤ C·(vol/c_low)·gAmp(rs)·Z^{A - c + q_C + 2ε}·(1+|t|)^{2J}`

for a box radius `M ≤ c_b log₂ Z + 2` (`box_of_scales`) and multiplicity `Mm ≤ Z^{ε/2}`
(`mult_subpower` with `δ < ε/2`). -/
import Submissions.density_split_fourth.CubeFree.Second.ConcreteLabelAssembly11

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace QRH.DensitySplitThird.CubeFree.Second.ConcreteLabelAssembly
open QRH.DensitySplitThird.CubeFree.Second.Concrete QRH.DensitySplitThird.CubeFree.Packet.Grouped
open QRH.DensitySplitThird.CubeFree.Second.ConcreteFrame QRH.DensitySplitThird.CubeFree.Second.ConcreteGroup
open QRH.DensitySplitThird.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.DensitySplitThird.CubeFree QRH.DensitySplitThird.CubeFree.Second

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource RayFourExpansion
open CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- **The label part of one residual split, final form.** -/
theorem split_label_bound_final (D : StepData) (G : StepGates D) (L : ℝ) (hL : 0 ≤ L)
    (hlarge : PricedPackedSource D.price D.Hmin (D.Hmax + 1) (L + 1))
    (hsmall : PricedPackedSource (nativePrice (3/4) (by norm_num)) D.Hmin (D.Hmax + 1) (L + 1))
    (cb : ℝ) (hcb : 0 ≤ cb) :
    ∀ ε : ℝ, 0 < ε → ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, 0 < mesh → mesh ≤ meshMax →
    ∀ (θ : GData L) (η : Character),
    ∃ J : ℕ, ∃ control : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ (P : SidePack η) (ξ : RayCharacter) (Q : Id) (m : O) (χ₀ : RayCharacter)
      (s : Source (Fin θ.N) θ.a θ.b) (ha : 0 < θ.a) (rs : GSrc θ mesh Z) (Kc R H : ℝ) (M : ℤ)
      (Mm : ℕ) (clow : ℝ) (hR : RootLabelData P Q m s ha rs Kc R H M Mm clow)
      (hM : 0 ≤ M ∧ (M:ℝ) ≤ cb * Real.logb 2 Z + 2) (hMm : (Mm : ℝ) ≤ Z^(ε/2)) (A c qC : ℝ)
      (hb : BranchData D G (gFrame L θ mesh η Z) ε mesh rs A c qC (commonH rs))
      (hHr : D.Hmin ≤ commonH rs ∧ commonH rs ≤ D.Hmax) (t : ℝ),
      splitLabel (S0 s ha) (sourceCoefficient s ha 1) (childCharacter P.base ξ) χ₀ Q m t Kc R H ≤
        (C * (rs.vol / clow) * gAmp L θ mesh η Z rs J control * Z^(A - c + qC + 2*ε)) *
          (1 + ‖t‖)^(2*J) := by
  intro ε hε
  obtain ⟨meshMax, hmM, h1⟩ := split_label_bound D G L hL hlarge hsmall ε hε
  refine ⟨meshMax, hmM, fun mesh hmesh hmm θ η => ?_⟩
  obtain ⟨J, control, C, hC, hZ⟩ := h1 mesh hmesh hmm θ η
  refine ⟨J, control, C, hC, ?_⟩
  filter_upwards [hZ, box_card_subpower cb (ε/2) hcb (by positivity), eventually_gt_atTop (1:ℝ)]
    with Z hZ hbox hZ1
  intro P ξ Q m χ₀ s ha rs Kc R H M Mm clow hR hM hMm A c qC hb hHr t
  have hZ0 : 0 < Z := by linarith
  have h := hZ P ξ Q m χ₀ s ha rs Kc R H M Mm clow hR A c qC hb hHr t
  refine h.trans ?_
  have hcl := hR.hclow_pos
  have hvol := rs.vol_pos hZ0
  obtain ⟨hnn, -⟩ := gAmp_mono L θ mesh η Z rs
  have hamp := hnn J control
  have hb' := hbox M hM.1 hM.2
  have hZE := Real.rpow_nonneg hZ0.le (A - c + qC + ε)
  have hT : 0 ≤ (1 + ‖t‖)^(2*J) := by positivity
  have hprod : ((box M).card : ℝ) * (Mm : ℝ) ≤ Z^ε := by
    calc ((box M).card : ℝ) * (Mm : ℝ) ≤ Z^(ε/2) * Z^(ε/2) :=
          mul_le_mul hb' hMm (Nat.cast_nonneg _) (by positivity)
      _ = Z^ε := by rw [← Real.rpow_add hZ0]; ring_nf
  have e1 : (C * ((box M).card : ℝ) * (rs.vol / clow) * Mm * gAmp L θ mesh η Z rs J control *
      Z^(A - c + qC + ε)) * (1 + ‖t‖)^(2*J) =
      (((box M).card : ℝ) * (Mm : ℝ)) * (C * (rs.vol / clow) * gAmp L θ mesh η Z rs J control *
        Z^(A - c + qC + ε) * (1 + ‖t‖)^(2*J)) := by ring
  have e2 : (C * (rs.vol / clow) * gAmp L θ mesh η Z rs J control * Z^(A - c + qC + 2*ε)) *
      (1 + ‖t‖)^(2*J) = Z^ε * (C * (rs.vol / clow) * gAmp L θ mesh η Z rs J control *
        Z^(A - c + qC + ε) * (1 + ‖t‖)^(2*J)) := by
    rw [show A - c + qC + 2*ε = ε + (A - c + qC + ε) by ring, Real.rpow_add hZ0]; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hprod (by positivity)

end
end QRH.DensitySplitThird.CubeFree.Second.ConcreteLabelAssembly
