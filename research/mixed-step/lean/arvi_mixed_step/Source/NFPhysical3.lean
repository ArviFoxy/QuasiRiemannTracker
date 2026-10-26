/- Mixed step (N7): the physical layer and the source step from the truncated layer, for a mixed
step. Fork of Collet's `nf_physical_of_truncated` (Core/InitialTruncatedCallbacks.lean) and of the
final part of `nf_step_of_physical` (Low/HeightAnchorCallbacks.lean), through PR 76's `nf_physical2`
and `nf_step2` (`Source/NFStep2.lean`).

Changes: the step certificate is `SourceValid3` (no Collet `SourceValid`, no PR 76 `SourceValidC`),
so the width grid is not `nfWidthDelta_rm`. Any width delta `δw > 0` works here: the reference
cells come from the mixed scalar gate 9 (`0 < 49/100 - (9/2)·b` on the whole cell) through Collet's
`finite_reference_cells_from_margin`, with the margin `49/100 - (9/2)·cap`. The truncated layer is
the hypothesis `MixedTruncatedAt n low δw` (the analogue of Collet's `NFTruncatedInlet` at one
width delta); `Source/NFStep3.lean` proves it from the regular supplier. -/
import Submissions.arvi_mixed_step.Ledger.Geometry
import Submissions.arvi_mixed_step.Graph.Chain3
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialTruncatedCallbacks

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.MixedStep.Source
noncomputable section
open OAI.SevenEighths Record1252270103Finite QRH.Record1252270103Graph
open QRH.Record1252270103Low QRH.Record1252270103Restoration
open QRH.Record1252270103Source QRH.Record1252270103Source.InitialTruncated
open QRH.Record1252270103Source.FixedWidthPhysical
open QRH.MixedStep.Finite QRH.MixedStep.Ledger

/-- Scalar gate 9 of `SourceValid3` on the whole cell, at its weakest point `b = cap`. -/
theorem reference_margin3 (n low h : Source) (hv : SourceValidC3 n low h) :
    0 < 49/100 - (9/2:ℝ)*(n.cap:ℝ) ∧
      ∀ b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
        49/100 - (9/2:ℝ)*(n.cap:ℝ) ≤ 49/100 - (9/2:ℝ)*b := by
  have hcc : (crossing n low:ℝ) ≤ (n.cap:ℝ) := by exact_mod_cast hv.2.2.2.2.2.2.2.2.2.1
  have hg := (scalar3_full_width n low h hv (b := (n.cap:ℝ)) ⟨hcc, le_rfl⟩).1 9
  simp only [scalarGate3Real] at hg
  norm_num at hg
  refine ⟨by linarith, fun b hb => by linarith [hb.2]⟩

/-- The reference cells of any positive width delta. -/
theorem reference_cells3 (n low h : Source) (hv : SourceValidC3 n low h) (δ : ℝ) (hδ : 0 < δ) :
    FiniteReferenceCells (crossing n low) n.cap QRH.RepeatedMarks.natK δ
      (upperWidthCell (crossing n low) n.cap δ) := by
  obtain ⟨hm, hr⟩ := reference_margin3 n low h hv
  apply finite_reference_cells_from_margin _ _ _ (49/100 - (9/2:ℝ)*(n.cap:ℝ)) δ hm hδ
  intro b hb
  simpa only [QRH.RepeatedMarks.natK] using hr b hb

/-- The truncated layer of a mixed step at the width delta `δw` (Collet's `NFTruncatedInlet`,
at one width delta, with `K = natK = 9/2`). -/
def MixedTruncatedAt (n low : Source) (δw : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ b ∈ activeWidthGrid (crossing n low) n.cap δw,
    ∃ m x : ℝ, 0 < m ∧ 0 < x ∧ ∀ mesh ξ : ℝ, 0 < mesh → mesh ≤ m → 0 < ξ → ξ ≤ x →
      InitialTruncated.FixedSubsetTruncatedSupplier n.B n.L n.cap (crossing n low)
        QRH.RepeatedMarks.natK mesh ξ ε b δw

/-- The marked physical supplier on the width cells (PR 76's `nf_physical2`, mixed). -/
theorem nf_physical3_of (n low h : Source) (hv : SourceValid3 n low h) (δw : ℝ) (hδ : 0 < δw)
    (htr : MixedTruncatedAt n low δw) :
    ∀ ε : ℝ, 0 < ε → ∃ mesh ξ : ℝ, 0 < mesh ∧ 0 < ξ ∧
      HeightAnchor.InitialMarkedPhysicalSupplier n.B n.L n.cap (crossing n low)
        QRH.RepeatedMarks.natK mesh ξ ε (upperWidthCell (crossing n low) n.cap δw) := by
  have hc := reference_cells3 n low h hv.1 δw hδ
  intro ε hε
  apply physical_supplier_of_truncated_widths n.B n.L n.cap (crossing n low) QRH.RepeatedMarks.natK ε
    δw (by exact_mod_cast hv.1.2.1) (by exact_mod_cast hv.1.2.2.1.le)
    (by exact_mod_cast hv.1.2.2.2.2.1.le) hε hδ
  · intro b hb
    have hr := (hc.radius_pos b (activeWidthGrid_bounds _ _ _ b hb)).le
    have he := upperWidthCell_fixed_on_grid (crossing n low) n.cap _ b hδ hb
    simpa only [he] using hr
  · exact htr ε hε

/-- **The mixed source step from its truncated layer** (PR 76's `nf_step2`, mixed): a mixed step
whose truncated layer holds at some width delta is a global source. -/
theorem nf_step3_of_truncated (n low h : Source) (hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hK : 6*(2*HeckeZeroSupremum.beta-1) ≤ QRH.RepeatedMarks.natK)
    (hv : SourceValid3 n low h) (hlow : ParentGood low) (hp : P low)
    (δw : ℝ) (hδ : 0 < δw) (htr : MixedTruncatedAt n low δw) : P n := by
  have hphys := nf_physical3_of n low h hv δw hδ htr
  have hfields := hv.1
  obtain ⟨hBn, hBn1, hLn, _, _, _, _, hL, _, _, hcrosslow, _⟩ := hfields
  have hn0 : 0 ≤ (n.B:ℝ) := by exact_mod_cast hBn.le
  have hn1 : (n.B:ℝ) ≤ 1 := by exact_mod_cast hBn1
  have hLn' : 1 ≤ (n.L:ℝ) := by exact_mod_cast hLn.le
  have hL' : (n.L:ℝ) ≤ (low.L:ℝ) := by exact_mod_cast hL.le
  have hcross : (crossing n low:ℝ) ≤ (low.cap:ℝ) := by exact_mod_cast hcrosslow
  have hbudget : (n.B:ℝ) - (low.B:ℝ) + ((low.L:ℝ) - (n.L:ℝ))*(crossing n low:ℝ) ≤ 0 :=
    (crossing_real_identity n low hL).le
  have hcells : ReferenceWidthCells (crossing n low) n.cap QRH.RepeatedMarks.natK
      (upperWidthCell (crossing n low) n.cap δw) :=
    (reference_cells3 n low h hv.1 δw hδ).reference
  change GlobalSource n.B n.L n.cap
  apply globalSource_of_squarefree n.B n.L n.cap hn0 (by linarith)
  apply QRH.Record1252270103Low.HeightAnchor.uniform_squarefree_source_step n.B n.L n.cap low.B
    low.L low.cap (crossing n low)
    QRH.RepeatedMarks.natK (QRH.RepeatedMarks.natK/6) (upperWidthCell (crossing n low) n.cap δw) hn0 hn1
    (by exact_mod_cast hlow.2.1) hLn' hL' hcross hbudget
  · norm_num [QRH.RepeatedMarks.natK]
  · norm_num [QRH.RepeatedMarks.natK]
  · linarith only [hK]
  · ring_nf
    exact le_rfl
  · exact hb
  · exact hcells
  · exact hp
  · exact hphys

end
end QRH.MixedStep.Source
#print axioms QRH.MixedStep.Source.reference_margin3
#print axioms QRH.MixedStep.Source.reference_cells3
#print axioms QRH.MixedStep.Source.nf_physical3_of
#print axioms QRH.MixedStep.Source.nf_step3_of_truncated
