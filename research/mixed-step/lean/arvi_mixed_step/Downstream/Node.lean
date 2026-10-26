/- Mixed step (L4/L5): the node facts assumed by the forked LOW/HIGH spines.

The forked spines run at an abstract node `n` (for the transfer residual: the ledger's virtual node
`vnode n low b δ` at the width `b - δ`, `Ledger/Nodes.lean`) and never use Collet's `RealGeometry`
or `ParentGood n`. They use exactly the facts collected here:
* five fields of `RealGeometry` (all of them are fields of the ledger's `RealGeometryLow`);
* three of the five conjuncts of `ParentGood n` (`n.B ≤ 1`, `1 < n.L`, `n.cap < 1`); the
  conjunct `0 < n.B` is not used and is not implied by the mixed gates at a virtual node.
`nodeGeometry_of_real` shows that Collet's own hypotheses imply these facts. -/
import Submissions.hailey_collet_1252270103.Record1252270103StepScalar.Geometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.MixedStep.Downstream
noncomputable section
open Record1252270103Finite QRH.Record1252270103Graph QRH.Record1252270103StepScalar

/-- The node facts of the forked LOW/HIGH spines (`L45_DESIGN.md` §3, F3/F4). -/
structure NodeGeometry_mx (n low : Source) (b : ℝ) : Prop where
  lowL_pos : 0 < (low.L:ℝ)
  a_pos : 0 < sourceAReal n low b
  a_small : sourceAReal n low b < 1/75
  a_allowance : 20*(n.allowance:ℝ) < sourceAReal n low b
  parent_budget_room : sourceTReal n b + b + 4*(n.allowance:ℝ) < (low.B:ℝ)*sourceFReal n low b
  B_le_one : n.B ≤ 1
  L_gt_one : 1 < n.L
  cap_lt_one : n.cap < 1

theorem nodeGeometry_of_real (K : ℚ) (n low : Source) (b : ℝ) (hg : RealGeometry K n low b)
    (hn : ParentGood n) : NodeGeometry_mx n low b :=
  ⟨hg.lowL_pos, hg.a_pos, hg.a_small, hg.a_allowance, hg.parent_budget_room,
    hn.2.1, hn.2.2.1, hn.2.2.2.2⟩

end
end QRH.MixedStep.Downstream
#print axioms QRH.MixedStep.Downstream.nodeGeometry_of_real
