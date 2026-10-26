/- Mixed step (L4/L5, N6): new in this submission; uses Collet's definitions, the forked
two-parent regular chain (`regular_canonical_joint_mx`, `regular_point_supplier_rm_mx`) and the node
lemmas of `Downstream/Supplier3` by import.

`regular_supplier3_at`: the residual regular inlet `RegularJointSupplier3At` at one node `δ` of the grid
and one block `J`. It is Collet's `regular_supplier_of_points` for the two-parent family of the
residual `Initial'.restrict i₀ J` of the initial datum `i₀` at the virtual node
`vnode2 n low b δ θ`, with the actual pool at `r = n.lowFee`:
* the residual family is `regularMainFamily_mx` of `allocatedRegularFamily_mx` on the column
  `seedColumn (rayShift (column l) ray) (seed l)` (the label, rays and seed of the contract; the
  scalar, `extra` and the frozen coefficient depend on the label only), allocation `allocRestrict`;
* the δ-shift is `2·mesh` (`residual_shift`), the frozen margins are `frozen_margin_restrict`;
* the transport from the anchor's `K = Z^1` to `K = Z` is Collet's `positive_radius_transport`. -/
import Submissions.arvi_mixed_step.Downstream.Supplier3
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularSuppliers
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularCanonicalNorm
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Contraction.SelectedMainExceptionalIdentity
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularSeedColumn
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.MixedStep.Downstream
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentSourceMass CenteredMomentSectorLocalization
open CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentLogDyadic
open Cycle61InitialMass RayFourExpansion Record1252270103Finite
open Record1252270103Second
open QRH.Record1252270103Low QRH.Record1252270103Source
open QRH.Record1252270103Source.High.CoupledFirst QRH.Record1252270103Source.High.GlobalPhysical
open QRH.Record1252270103Source.Admission.FirstFamily
open OAI.SevenEighths.Record1252270103Source.Collision
open QRH.Record1252270103Source.Low.SelectedExceptionalNormalized
open QRH.Record1252270103Source.InitialRegularToTruncated QRH.Record1252270103Source.InitialTruncated
open QRH.Record1252270103Source.ExceptionalPrice QRH.MixedStep.Residual
open QRH.Record1252270103Graph QRH.Record1252270103Source.PhysicalAnalytic
local notation "O" => HeckeFamily.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource
local instance supplier3AtDecidable {α:Type*}:DecidableEq α:=Classical.decEq _
open QRH.Record1252270103Source.Admission QRH.Record1252270103Source.Admission.SelectedRegularSourceData
open QRH.Record1252270103Source.Admission.SelectedRegularLowPoint
open QRH.Record1252270103Source.Contraction.SelectedMainExceptional
open QRH.MixedStep.Ledger QRH.MixedStep.SeedColumn

/-- **The residual regular inlet at one node and one block.** -/
theorem regular_supplier3_at (K:ℚ)(n low high:Source)(b:ℚ)(reserve θ mesh ξ width:ℝ)(G:NodeGrid)
    (φ:ℚ→ℝ)(δ:ℚ)
    (hf:FixedBudget reserve 100 100 1 θ)(hm:0≤mesh)(hmesh:100*mesh≤θ)(hξ:0<ξ)(hξθ:ξ≤θ)
    (hr:reserve≤(n.allowance:ℝ))(hfee:0≤(n.highFee:ℝ))(ha:0<(n.allowance:ℝ))
    (hq:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
    (hn:ParentGood n)(hlow:ParentGood low)(hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))
    (hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8)
    (hden:sourceDen n low≠0)
    (href:0<49/100-(K:ℝ)*b)(hb1:(b:ℝ)≤1)
    (hr0:0<(n.lowFee:ℝ))(hmeshr:mesh<(n.lowFee:ℝ)/2)
    (hθstep:θ≤PhysicalLowGuard.step n)
    (hwidth0:0≤width)(hwidth:width+G.κ≤θ)
    (hB0:22/23≤(high.B:ℝ))(hB1:(high.B:ℝ)≤1)(hlam:1<(high.L:ℝ))
    (hcap0:0≤(high.cap:ℝ))(hcap1:(high.cap:ℝ)<1)
    (hparent:QRH.Record12518109Existence.UnitFaceSource
      (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ)
    (hδ:δ∈G.nodes)
    (hnode:NodeFacts3 n low high b reserve θ mesh G φ hlow ha hq hq1 hG hf.positive δ) :
    RegularJointSupplier3At K n low b mesh ξ θ width G φ δ := by
  intro α _ _ rayM _ H hH Wslot hW hsW bΦ hbΦ η η₀ Q hQM hQ hQt hQ72 R₀ hR₀ J
  -- the node and its facts
  have hθ0 : (0:ℚ) ≤ G.theta δ := le_max_left _ _
  have hθ0r : (0:ℝ) ≤ (G.theta δ : ℝ) := by exact_mod_cast hθ0
  have hκ0 : (0:ℝ) ≤ (G.κ:ℝ) := G.κ_nonneg_real
  have hδ0 : (0:ℝ) ≤ (δ:ℝ) := by exact_mod_cast G.node_nonneg hδ
  have hdθ : (δ:ℝ) - (G.theta δ:ℝ) ≤ (G.κ:ℝ) := by
    have h : δ - G.theta δ ≤ G.κ := by
      unfold NodeGrid.theta
      rcases le_total 0 (δ - G.κ) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    exact_mod_cast h
  have hsc := scalar_vnode2 n low b δ (G.theta δ) reserve θ mesh ξ width (G.κ:ℝ) hnode.geometry hlow ha hf
    hr hθstep hξ hξθ hm hmesh hwidth0 hκ0 hwidth
  have hbcast : (((b - G.theta δ : ℚ)) : ℝ) = (b:ℝ) - (G.theta δ:ℝ) := by push_cast; ring
  have hbv1 : (((b - G.theta δ : ℚ)) : ℝ) ≤ 1 := by rw [hbcast]; linarith
  have hB₀ : (n.B:ℝ) ≤ 1 := by exact_mod_cast hn.2.1
  have hlam₀ : (1:ℝ) ≤ (n.L:ℝ) := by exact_mod_cast hn.2.2.1.le
  have hcap₀ : (n.cap:ℝ) ≤ 1 := by exact_mod_cast hn.2.2.2.2.le
  have hθsmall := hf.small
  have hξ1 : ξ ≤ 1 := by linarith
  -- the point supplier of the residual (second layer `{i // i ∉ J}`, first layer `α`)
  obtain ⟨degree, controls, h00, Cpoint, τsource, hpoint, hτsource, epoint⟩ :=
    regular_point_supplier_rm_mx (vnode2 n low b δ (G.theta δ)) low high ((b - G.theta δ : ℚ):ℝ)
      (φ δ) reserve θ mesh ξ (width + G.κ) (n.lowFee:ℝ) (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hB₀ hlam₀ hcap₀ hf hsc hr0
      hmesh hwidth hbv1 hr hfee hq hq1 hG hnode.price hnode.low_mesh hβ hβhi hB0 hB1 hlam hcap0 hcap1
      hparent hnode.gaps α {i // i ∉ J} (Fintype.card_subtype_le _) rayM H hH Wslot hW hsW η η₀ Q hQM hQ hQt
      hQ72 R₀ hR₀
  have hnv := hnode.geometry
  have hampv : (n.lowFee:ℝ) + (δ:ℝ) = sourceAReal (vnode2 n low b δ (G.theta δ)) low ((b - G.theta δ : ℚ):ℝ) :=
    ((vnode2_real n low b δ (G.theta δ) hden).2.1).symm
  have hlt : (n.lowFee:ℝ) < 1 := by
    have h := hnv.a_small
    rw [← hampv] at h
    linarith
  obtain ⟨C, hC, enorm⟩ := regular_canonical_joint_mx (α₀ := α) (α := {i // i ∉ J}) rayM H hH Wslot hW hsW η η₀
    R₀ hR₀ Q (vnode2 n low b δ (G.theta δ)) low ((b - G.theta δ : ℚ):ℝ) (φ δ) reserve θ mesh ξ (width + G.κ)
    τsource (n.lowFee:ℝ) (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) Cpoint (Fintype.card α) (cellNewtonDepth (n.lowFee:ℝ))
    degree controls h00 hf hnv hB₀ hlam₀ hcap₀ hr0 hlt.le ((n.lowFee:ℝ) + δ) hampv hξ hξ1 hf.positive.le
    (hθsmall.trans (by norm_num)) hpoint hτsource
  have hrpos : 0 < reserve := by linarith [hf.tiny, hf.positive]
  have hσ : 0 < reserve/8 - 2*mesh := by linarith [hf.tiny, hf.positive, hmesh, hm]
  have hcn := cell_newton_depth (n.lowFee:ℝ) hr0 hlt
  have hpool := QRH.Record1252270103Source.Pool.eventually_fixed_cell_pool rayM H hH fixedBadPrimes (Finset.Subset.refl _) (n.lowFee:ℝ)
    ((n.lowFee:ℝ)/2) mesh θ 10 4 (cellNewtonDepth (n.lowFee:ℝ)) hm hmeshr (by linarith) hf.positive
  refine ⟨degree, controls, h00, C, τsource/4, reserve/8 - 2*mesh, hC, by positivity, hσ, ?_⟩
  filter_upwards [epoint, enorm, hpool] with Z hp hnZ hpoolZ
  refine ⟨hp.1, ?_⟩
  intro hZ θslot w v t ht height hw hwm hh hv hext p X₁ X₂ hX₁ hX₂ hadm hcross hwlo hwhi Y₂ hy₂ hyl hyr Y₁ hY₂
    hY₁ hprod s modifier W N amp P hθJ hJδ hsh sv Label instL reflected bin
  have hext' : 1+|ht|+height ≤ Z^(τsource/4) := by linarith [abs_nonneg t]
  let i₀ : Initial (α:=α) rayM H Z := ⟨θslot,w,v,t,p,X₁,X₂,Y₁,Y₂,hX₁,hX₂,hY₁,hY₂,hprod⟩
  let i : Initial (α:={i // i ∉ J}) rayM H Z := Initial'.restrict i₀ J
  have hi : InitialGeometry i (vnode2 n low b δ (G.theta δ)) ((b - G.theta δ : ℚ):ℝ) (width + G.κ) mesh
      (49/100 - (K:ℝ)*b) :=
    restrict_initialGeometry i₀ n low b δ (G.theta δ) width mesh (49/100 - (K:ℝ)*b) G.κ hw hwm hadm hwlo hwhi
      href.le hyl hyr rfl (by linarith [hlam₀]) J hθJ hJδ hdθ
  let Result (X : ℝ) (hX : 0 < X) : Prop :=
    ∀column:Label→FirstColumnIndex (source s modifier R₀ 1 X Z ξ hX bin),
    ∀_hLive:∀l,column l∈firstLiveColumns (source s modifier R₀ 1 X Z ξ hX bin)
      (fun _=>logAnnulus),
    ∀(seed:Label→Ideal O)(hseed:∀l,Squarefree (seed l)),(∀l,seed l∣(column l).2.1.val)→
      Function.Injective (fun l=>(firstLabel s modifier R₀ 1 X Z ξ hX bin (column l),
        seed l))→
    let common:=fun l=>columnIdeal reflected s modifier R₀ 1 X Z ξ hX bin (column l)
    let scalar:=fun l=>balancedColumnScalar reflected s modifier R₀ 1 X Z ξ 1
      (Real.logb Z (volume s)) hX bin
      (fun q=>normPhase (coordinateBlock s modifier R₀ 1 W X Z ξ q)) (column l)
    let H0:=fun l=>(source s modifier R₀ 1 X Z ξ hX bin (column l).1).H0
    let labels:=fun l=>firstLabel s modifier R₀ 1 X Z ξ hX bin (column l)
    let radius:=fun l=>literalFirstRadius reflected X (volume s) Z ξ θ (labels l)
    ∀(alloc:∀l,actualAllocations s.pools (common l))(hJ:∀l,J⊆liveIndices (alloc l).val),
      (∀l,frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P≠0)→
      (∀l,φ δ≤(∑i,w i)-∑i∈liveIndices (alloc l).val,w i)→
    ∀(ray:RayCharacter)(χ₀:Label→RayCharacter),
    let extra:=fun l=>((bands (H0 l)).card:ℝ)*((actualAllocations s.pools (common l)).card:ℝ)^2/
      (P.card:ℝ)*((radius l+6*amp)/(amp/2))
    let amplitude:=fun l=>‖scalar l‖^2*extra l*‖frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P‖^2
    let chars:=fun l=>columnCharacter reflected s modifier R₀ 1 X Z ξ hX bin
      (rayShift reflected (column l) ray)
    let Hv:=fun l=>firstMainRadius reflected X (volume sv) Z ξ (3*(amp+δ)) θ (labels l)
    let Tsecv:=fun l=>firstMainFourierScale reflected X (volume sv) Z ξ (3*(amp+δ)) θ 2 N (labels l)
    let f:=mainAllocatedFamily sv ballProfile (p.profile 0) (p.profile 1) Z R₀ common
      seed (fun l=>allocRestrict s (common l) (alloc l) J (hJ l)) chars (fun _=>ht)
      P hseed (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
      Hv Tsecv (fun _=>volume sv) amplitude ξ
      (fun l=>first_main_radius_pos reflected X (volume sv) Z ξ (3*(amp+δ)) θ
        (zero_lt_one.trans hZ) (labels l)) χ₀ (fixedBadMask*idealGenerator R₀)
    regularJointNorm f (internalQ Q η₀)≤C*(p.control controls)^2*
      geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
      (1+|ht|+height)^degree*Z^(-(reserve/8-2*mesh))
  have boundK : Result (Z^(1:ℝ)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) := by
    intro column hLive seed hseed hdvd hinj common scalar H0 labels radius alloc hJ hfroz hφ ray χ₀ extra
      amplitude chars Hv Tsecv f
    let a := Initial.anchor_mx i₀ i hH Wslot hW hsW hZ η η₀ R₀ 1 hR₀ (by simp) 1 1 1 1 (fun _=>1) ξ θ bin
      reflected Q
    let col' : Label → a.Column :=
      fun l => seedColumn (rayShift reflected (column l) ray) (seed l) (hdvd l)
    have hLive' : ∀ l, col' l ∈ firstLiveColumns
        (source a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin) (fun _=>logAnnulus) :=
      fun l => seedColumn_live ((rayShift_mem_firstLiveColumns reflected (column l) ray _).mpr (hLive l))
        (hdvd l) (hseed l)
    let alloc' : ∀ l, actualAllocations a.s.pools
        (FirstFamily.columnIdeal a.reflected a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (col' l)) :=
      fun l => allocRestrict s (common l) (alloc l) J (hJ l)
    have hfreeze' : ∀ l, frozenCoefficient (alloc' l).val
        (FirstFamily.columnIdeal a.reflected a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (col' l))
        a.R a.s.ν a.s.W a.s.P ≠ 0 := by
      intro l
      have h := frozenCoefficient_restrict s (common l) R₀ (alloc l) J (hJ l)
      exact h.symm ▸ hfroz l
    have hinj' : Function.Injective (fun l => (a.label (col' l), (col' l).2.1.val)) := hinj
    have hmargin' : ∀ l, φ δ ≤ (∑ j, i.w j) - ∑ j ∈ liveIndices (alloc' l).val, i.w j :=
      fun l => frozen_margin_restrict s (common l) (alloc l) J (hJ l) w (φ δ) (hφ l)
    have hshift' : (n.lowFee:ℝ) + δ - (n.lowFee:ℝ) ≤
        Real.logb Z (volume a.s₀) - Real.logb Z (volume a.s) + 2*mesh := by
      have h := residual_shift n low b δ (G.theta δ) hden s J w Z mesh hZ (fun i => rfl) hsh
      rw [← hampv] at h
      exact h
    have hhbound := hnZ.2 hp.2 hZ i₀ i (49/100 - (K:ℝ)*b) hi rfl hw hadm hy₂ hyl hyr le_rfl
      (Fintype.card_subtype_le _) bin reflected col' hLive' alloc' P ht χ₀ hinj' hfreeze' hpoolZ
      hcn.2.2.1 hcn.2.2.2.1 W height hh (fun j => hv j.val) hext' (2*mesh) (by linarith) hshift' hmargin'
    -- the residual family is `regularMainFamily_mx` of the family on the seed columns
    let rawRadius : Label → ℝ := fun l => literalFirstRadius reflected Z (volume s) Z ξ θ (labels l)
    have hradius : rawRadius = radius := by
      funext l
      exact congrArg (fun X => literalFirstRadius reflected X (volume s) Z ξ θ (labels l)) (Real.rpow_one Z).symm
    let F := allocatedRegularFamily_mx a col' hLive' alloc' P ((n.lowFee:ℝ) + δ) ht N χ₀
    have he := regularMainFamily_joint_norm_mx a col' hLive' alloc' P ((n.lowFee:ℝ) + δ) ht N χ₀
      (p.profile 0) (p.profile 1) W H0 rawRadius ((n.lowFee:ℝ)/2) (fun _ => (n.lowFee:ℝ))
    have hA : amplitude = SelectedRegularAbsolute.amplitude_mx F W (fun _ => P) (fun _ => (n.lowFee:ℝ)) H0
        radius ((n.lowFee:ℝ)/2) := by
      funext l
      have hfr := frozenCoefficient_restrict s (common l) R₀ (alloc l) J (hJ l)
      show ‖scalar l‖^2 * extra l * ‖frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P‖^2 = _
      rw [← hfr]
      rfl
    have hE : regularJointNorm f (internalQ Q η₀) = regularJointNorm
        (regularMainFamily_mx F P (p.profile 0) (p.profile 1) W H0 radius ((n.lowFee:ℝ)/2)
          (fun _ => (n.lowFee:ℝ))) a.Q := by
      simp only [f, regularMainFamily_mx]
      rw [hA]
      rfl
    have hE2 := congrArg (fun r : Label → ℝ => regularJointNorm
      (regularMainFamily_mx F P (p.profile 0) (p.profile 1) W H0 r ((n.lowFee:ℝ)/2)
        (fun _ => (n.lowFee:ℝ))) a.Q) hradius
    have hexp : Z^(2*mesh - reserve/8) = Z^(-(reserve/8 - 2*mesh)) := by congr 1; ring
    calc regularJointNorm f (internalQ Q η₀)
        = regularJointNorm (regularMainFamily_mx F P (p.profile 0) (p.profile 1) W H0 radius
            ((n.lowFee:ℝ)/2) (fun _ => (n.lowFee:ℝ))) a.Q := hE
      _ = regularJointNorm (regularMainFamily_mx F P (p.profile 0) (p.profile 1) W H0 rawRadius
            ((n.lowFee:ℝ)/2) (fun _ => (n.lowFee:ℝ))) a.Q := hE2.symm
      _ ≤ _ := he.le.trans hhbound
      _ = C * (i.p.control controls)^2 *
          geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin *
          (1+|ht|+height)^degree * Z^(-(reserve/8 - 2*mesh)) := by rw [hexp]; ring
  exact ExceptionalPrice.positive_radius_transport Result (Real.rpow_one Z)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) (zero_lt_one.trans hZ) boundK

/-- **`regular_supplier3`**: the residual regular inlet at every node and block of the grid, with one
set of constants. -/
theorem regular_supplier3 (K:ℚ)(n low high:Source)(b:ℚ)(reserve θ mesh ξ width:ℝ)(G:NodeGrid)
    (φ:ℚ→ℝ) : RegularSupplier3Statement K n low high b reserve θ mesh ξ width G φ := by
  intro hf hm hmesh hξ hξθ hr hfee ha hq hq1 hn hlow hG hβ hβhi hden href hb1 hr0 hmeshr hθstep hwidth0
    hwidth hB0 hB1 hlam hcap0 hcap1 hparent hnodes
  exact regular_supplier3_of_at K n low b mesh ξ θ width G φ (fun δ hδ =>
    regular_supplier3_at K n low high b reserve θ mesh ξ width G φ δ hf hm hmesh hξ hξθ hr hfee ha hq hq1 hn
      hlow hG hβ hβhi hden href hb1 hr0 hmeshr hθstep hwidth0 hwidth hB0 hB1 hlam hcap0 hcap1 hparent hδ
      (hnodes δ hδ))

end
end QRH.MixedStep.Downstream
#print axioms QRH.MixedStep.Downstream.regular_supplier3_at
#print axioms QRH.MixedStep.Downstream.regular_supplier3
