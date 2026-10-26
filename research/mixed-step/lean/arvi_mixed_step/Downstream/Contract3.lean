/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, N6 interface): adapted from the statement of Collet's `RegularJointSupplier`
(Record1252270103Source/Core/InitialRegularToTruncatedContract.lean:50); changes: the family is
the residual family of a piece (design §2, §4).

`RegularJointSupplier3 K n low b mesh ξ reserve width G φ`:
- The first layer is Collet's initial input `s` at the actual width `b`, with the same raw data,
  face, cell and reference as in `RegularJointSupplier`.
- The pool is the actual one, `P := primePool … (Z^r)` at the pool width `r = n.lowFee`, and the
  amplitudes are the original ones: scalar at `logb Z (volume s)`, `extra` with
  `actualAllocations s.pools` and the ball factor `(radius+6r)/(r/2)`, frozen coefficient of `s`.
- Child seeds are a per-label `seed` with `seed l ∣ (column l).2.1.val` (squarefree, and `(firstLabel, seed)`
  injective). This covers the no-(S) transfer (labels `(l, L′)`); the plain case is the column divisor.
- For every node `δ ∈ G.nodes`, with `θ = G.theta δ`, and every block `J` with
  `θ ≤ Σ_J w ≤ δ ≤ Σ_J w + 2·mesh` inside the live slots of every label, the residual family is:
  - common parent `s.restrict J`;
  - allocations `allocRestrict`;
  - characters `columnCharacter (rayShift (column l) ray)`;
  - MAIN radius and Fourier scale at `volume (s.restrict J)` and the virtual amplitude `3·(r + δ)`;
  - `T = volume (s.restrict J)`.

  This is N3's `pieceEnergy` family, passed through `eventual_selected_second`. Under the frozen
  margins `φ δ ≤ Σ w − Σ_{live (alloc l)} w`, its full kept norm is `≤ C·…·Z^(-σ)`, with one set of
  constants for all nodes, blocks and rays. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularToTruncatedContract
import Submissions.arvi_mixed_step.Downstream.Grid
import Submissions.arvi_mixed_step.Residual.RayShift
import Submissions.arvi_mixed_step.Residual.Restrict
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularLowParameters
import Submissions.arvi_mixed_step.Downstream.Node
import Submissions.arvi_mixed_step.Ledger.Nodes
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PaymentWrappersK

set_option autoImplicit false
set_option maxHeartbeats 200000
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
local instance contract3Decidable {α:Type*}:DecidableEq α:=Classical.decEq _

/-- **The residual regular inlet** (N6 interface, design §4). Collet's `RegularJointSupplier` read
on the residual family of each piece `(δ, J, ray)`; one set of constants for all of them. -/
def RegularJointSupplier3 (K:ℚ)(n low:Source)(b:ℚ)(mesh ξ reserve width:ℝ)(G:NodeGrid)
    (φ:ℚ→ℝ):Prop :=
  ∀(α:Type)[Fintype α][DecidableEq α],
  ∀(rayM:Ideal O)[NeZero rayM],
  ∀(H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H),
  ∀(Wslot:ℝ→ℂ)(hW:ContDiff ℝ ∞ Wslot)(hsW:Function.support Wslot⊆Set.Icc (1:ℝ) 2),
  ∀(bΦ:ℝ)(hbΦ:2≤bΦ)(η η₀:Character)(Q:Ideal O),
    Q≤rayM→internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
  ∀(R₀:Ideal O),R₀≠0→
  ∃degree:ℕ,∃controls:Finset (ℕ×ℕ),(0,0)∈controls ∧
  ∃C τ σ:ℝ,0<C ∧ 0<τ ∧ 0<σ ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
  ∀(θ:α→RayQuotient.Characters rayM H)(w v:α→ℝ)(t ht height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤mesh)→0≤height→(∀i,|v i|≤height)→
    1+|t|+|ht|+height≤Z^τ→
  ∀p:Profiles (1/4) (9/4),∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z X₁) (length Z X₂) (∑i,w i) 1→
    (crossing n low:ℝ)≤∑i,w i→(b:ℝ)-width≤∑i,w i→(∑i,w i)≤b→
  let Y₂:=Z^(49/100-(K:ℝ)*b)
  1≤Y₂→Y₂≤X₁→Y₂≤X₂→
  let Y₁:=X₁*X₂/Y₂
  let hY₂:0<Y₂:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  let hY₁:0<Y₁:=div_pos (mul_pos hX₁ hX₂) hY₂
  let hprod:Y₁*Y₂=X₁*X₂:=div_mul_cancel₀ _ hY₂.ne'
  let s:=initialInput rayM H hH Wslot hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
  let modifier:=markedSourceModifier 1 1 1 1 (fun _=>1)
  let W:=initialRadialBump bΦ (by linarith)
  let N:=Fintype.card α
  let amp:=(n.lowFee:ℝ)
  let P:=CenteredMomentPrimePool.primePool rayM H fixedBadPrimes (1/2) 1 (Z^amp)
  ∀δ∈G.nodes,∀J:Finset α,
    (G.theta δ:ℝ)≤∑j∈J,w j→∑j∈J,w j≤(δ:ℝ)→(δ:ℝ)-∑j∈J,w j≤2*mesh→
  let sv:=s.restrict J
  ∀{Label:Type}[Fintype Label],∀(reflected:Bool)(bin:ℤ×(Fin 5→ℤ)),
  ∀column:Label→FirstColumnIndex (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin),
  ∀_hLive:∀l,column l∈firstLiveColumns (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin)
    (fun _=>logAnnulus),
  ∀(seed:Label→Ideal O)(hseed:∀l,Squarefree (seed l)),(∀l,seed l∣(column l).2.1.val)→
    Function.Injective (fun l=>(firstLabel s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l),
      seed l))→
  let common:=fun l=>columnIdeal reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
  let scalar:=fun l=>balancedColumnScalar reflected s modifier R₀ 1 Z Z ξ 1
    (Real.logb Z (volume s)) (zero_lt_one.trans hZ) bin
    (fun q=>normPhase (coordinateBlock s modifier R₀ 1 W Z Z ξ q)) (column l)
  let H0:=fun l=>(source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l).1).H0
  let labels:=fun l=>firstLabel s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
  let radius:=fun l=>literalFirstRadius reflected Z (volume s) Z ξ reserve (labels l)
  ∀(alloc:∀l,actualAllocations s.pools (common l))(hJ:∀l,J⊆liveIndices (alloc l).val),
    (∀l,frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P≠0)→
    (∀l,φ δ≤(∑i,w i)-∑i∈liveIndices (alloc l).val,w i)→
  ∀(ray:RayCharacter)(χ₀:Label→RayCharacter),
  let extra:=fun l=>((bands (H0 l)).card:ℝ)*((actualAllocations s.pools (common l)).card:ℝ)^2/
    (P.card:ℝ)*((radius l+6*amp)/(amp/2))
  let amplitude:=fun l=>‖scalar l‖^2*extra l*‖frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P‖^2
  let chars:=fun l=>columnCharacter reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin
    (rayShift reflected (column l) ray)
  let Hv:=fun l=>firstMainRadius reflected Z (volume sv) Z ξ (3*(amp+δ)) reserve (labels l)
  let Tsecv:=fun l=>firstMainFourierScale reflected Z (volume sv) Z ξ (3*(amp+δ)) reserve 2 N (labels l)
  let f:=mainAllocatedFamily sv ballProfile (p.profile 0) (p.profile 1) Z R₀ common
    seed (fun l=>allocRestrict s (common l) (alloc l) J (hJ l)) chars (fun _=>ht)
    P hseed (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
    Hv Tsecv (fun _=>volume sv) amplitude ξ
    (fun l=>first_main_radius_pos reflected Z (volume sv) Z ξ (3*(amp+δ)) reserve
      (zero_lt_one.trans hZ) (labels l)) χ₀ (fixedBadMask*idealGenerator R₀)
  regularJointNorm f (internalQ Q η₀)≤C*(p.control controls)^2*
    geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
    (1+|ht|+height)^degree*Z^(-σ)

/-! ### One node and one block at a time -/

/-- `RegularJointSupplier3` at one node `δ` and one block `J` (fixed before the constants). The
constants may depend on `δ` and `J`; `regular_supplier3_of_at` makes them uniform. -/
def RegularJointSupplier3At (K:ℚ)(n low:Source)(b:ℚ)(mesh ξ reserve width:ℝ)(G:NodeGrid)
    (φ:ℚ→ℝ)(δ:ℚ):Prop :=
  ∀(α:Type)[Fintype α][DecidableEq α],
  ∀(rayM:Ideal O)[NeZero rayM],
  ∀(H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H),
  ∀(Wslot:ℝ→ℂ)(hW:ContDiff ℝ ∞ Wslot)(hsW:Function.support Wslot⊆Set.Icc (1:ℝ) 2),
  ∀(bΦ:ℝ)(hbΦ:2≤bΦ)(η η₀:Character)(Q:Ideal O),
    Q≤rayM→internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
  ∀(R₀:Ideal O),R₀≠0→
  ∀J:Finset α,
  ∃degree:ℕ,∃controls:Finset (ℕ×ℕ),(0,0)∈controls ∧
  ∃C τ σ:ℝ,0<C ∧ 0<τ ∧ 0<σ ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
  ∀(θ:α→RayQuotient.Characters rayM H)(w v:α→ℝ)(t ht height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤mesh)→0≤height→(∀i,|v i|≤height)→
    1+|t|+|ht|+height≤Z^τ→
  ∀p:Profiles (1/4) (9/4),∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z X₁) (length Z X₂) (∑i,w i) 1→
    (crossing n low:ℝ)≤∑i,w i→(b:ℝ)-width≤∑i,w i→(∑i,w i)≤b→
  let Y₂:=Z^(49/100-(K:ℝ)*b)
  1≤Y₂→Y₂≤X₁→Y₂≤X₂→
  let Y₁:=X₁*X₂/Y₂
  let hY₂:0<Y₂:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  let hY₁:0<Y₁:=div_pos (mul_pos hX₁ hX₂) hY₂
  let hprod:Y₁*Y₂=X₁*X₂:=div_mul_cancel₀ _ hY₂.ne'
  let s:=initialInput rayM H hH Wslot hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
  let modifier:=markedSourceModifier 1 1 1 1 (fun _=>1)
  let W:=initialRadialBump bΦ (by linarith)
  let N:=Fintype.card α
  let amp:=(n.lowFee:ℝ)
  let P:=CenteredMomentPrimePool.primePool rayM H fixedBadPrimes (1/2) 1 (Z^amp)
  ∀_hθJ:(G.theta δ:ℝ)≤∑j∈J,w j,∀_hJδ:∑j∈J,w j≤(δ:ℝ),∀_hsh:(δ:ℝ)-∑j∈J,w j≤2*mesh,
  let sv:=s.restrict J
  ∀{Label:Type}[Fintype Label],∀(reflected:Bool)(bin:ℤ×(Fin 5→ℤ)),
  ∀column:Label→FirstColumnIndex (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin),
  ∀_hLive:∀l,column l∈firstLiveColumns (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin)
    (fun _=>logAnnulus),
  ∀(seed:Label→Ideal O)(hseed:∀l,Squarefree (seed l)),(∀l,seed l∣(column l).2.1.val)→
    Function.Injective (fun l=>(firstLabel s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l),
      seed l))→
  let common:=fun l=>columnIdeal reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
  let scalar:=fun l=>balancedColumnScalar reflected s modifier R₀ 1 Z Z ξ 1
    (Real.logb Z (volume s)) (zero_lt_one.trans hZ) bin
    (fun q=>normPhase (coordinateBlock s modifier R₀ 1 W Z Z ξ q)) (column l)
  let H0:=fun l=>(source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l).1).H0
  let labels:=fun l=>firstLabel s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
  let radius:=fun l=>literalFirstRadius reflected Z (volume s) Z ξ reserve (labels l)
  ∀(alloc:∀l,actualAllocations s.pools (common l))(hJ:∀l,J⊆liveIndices (alloc l).val),
    (∀l,frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P≠0)→
    (∀l,φ δ≤(∑i,w i)-∑i∈liveIndices (alloc l).val,w i)→
  ∀(ray:RayCharacter)(χ₀:Label→RayCharacter),
  let extra:=fun l=>((bands (H0 l)).card:ℝ)*((actualAllocations s.pools (common l)).card:ℝ)^2/
    (P.card:ℝ)*((radius l+6*amp)/(amp/2))
  let amplitude:=fun l=>‖scalar l‖^2*extra l*‖frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P‖^2
  let chars:=fun l=>columnCharacter reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin
    (rayShift reflected (column l) ray)
  let Hv:=fun l=>firstMainRadius reflected Z (volume sv) Z ξ (3*(amp+δ)) reserve (labels l)
  let Tsecv:=fun l=>firstMainFourierScale reflected Z (volume sv) Z ξ (3*(amp+δ)) reserve 2 N (labels l)
  let f:=mainAllocatedFamily sv ballProfile (p.profile 0) (p.profile 1) Z R₀ common
    seed (fun l=>allocRestrict s (common l) (alloc l) J (hJ l)) chars (fun _=>ht)
    P hseed (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
    Hv Tsecv (fun _=>volume sv) amplitude ξ
    (fun l=>first_main_radius_pos reflected Z (volume sv) Z ξ (3*(amp+δ)) reserve
      (zero_lt_one.trans hZ) (labels l)) χ₀ (fixedBadMask*idealGenerator R₀)
  regularJointNorm f (internalQ Q η₀)≤C*(p.control controls)^2*
    geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
    (1+|ht|+height)^degree*Z^(-σ)

/-- The ledger facts at the node `δ` of the grid: Collet's `Source` `vnode2 n low b δ (G.theta δ)`
at the width `b − G.theta δ` (LEDGER_INTERFACE v3). The LOW mesh bound is the one of
`regularLowMesh_mx` at that node; `mesh` is then the minimum over the nodes. -/
structure NodeFacts3 (n low high:Source)(b:ℚ)(reserve θ mesh:ℝ)(G:NodeGrid)(φ:ℚ→ℝ)
    (hlow:ParentGood low)(ha:0<(n.allowance:ℝ))(hq:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
    (hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))(hθ:0<θ)(δ:ℚ):Prop where
  price : QRH.MixedStep.Ledger.MixedNodePrice (QRH.MixedStep.Ledger.vnode2 n low b δ (G.theta δ)) low
    ((b-G.theta δ:ℚ):ℝ) (φ δ)
  geometry : NodeGeometry_mx (QRH.MixedStep.Ledger.vnode2 n low b δ (G.theta δ)) low ((b-G.theta δ:ℚ):ℝ)
  gaps : ∀ν∈Set.Icc (n.q:ℝ) (3/4),
    QRH.Record1252270103Source.PhysicalScalar.ActualGaps_rm (QRH.MixedStep.Ledger.vnode2 n low b δ (G.theta δ)) low (some high)
      ((b-G.theta δ:ℚ):ℝ) ν reserve
  low_mesh : mesh≤regularLowMesh_mx (QRH.MixedStep.Ledger.vnode2 n low b δ (G.theta δ)) low
    ((b-G.theta δ:ℚ):ℝ) (φ δ) θ price hlow ha hq hq1 hG hθ

/-- **The statement of `regular_supplier3`** (fork lead, F5/N6): the hypotheses under which the
residual regular inlet holds. They are PR 76's budgets for `regular_supplier_some_rm`, the
first-layer facts at the actual width `b`, the actual pool at `r = n.lowFee`, the HIGH parent, and
the ledger facts at every node of the grid. The conclusion is read with Collet's convention
`reserve := θ` (the HIGH budget). -/
def RegularSupplier3Statement (K:ℚ)(n low high:Source)(b:ℚ)(reserve θ mesh ξ width:ℝ)(G:NodeGrid)
    (φ:ℚ→ℝ):Prop:=
  ∀(hf:FixedBudget reserve 100 100 1 θ)(_hm:0≤mesh)(_hmesh:100*mesh≤θ)(_hξ:0<ξ)(_hξθ:ξ≤θ)
    (_hr:reserve≤(n.allowance:ℝ))(_hfee:0≤(n.highFee:ℝ))(ha:0<(n.allowance:ℝ))
    (hq:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
    (_hn:ParentGood n)(hlow:ParentGood low)(hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))
    (_hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)(_hβhi:HeckeZeroSupremum.beta≤7/8)
    (_hden:sourceDen n low≠0)
    (_href:0<49/100-(K:ℝ)*b)(_hb1:(b:ℝ)≤1)
    (_hr0:0<(n.lowFee:ℝ))(_hmeshr:mesh<(n.lowFee:ℝ)/2)
    (_hθstep:θ≤PhysicalLowGuard.step n)
    (_hwidth0:0≤width)(_hwidth:width+G.κ≤θ)
    (_hB0:22/23≤(high.B:ℝ))(_hB1:(high.B:ℝ)≤1)(_hlam:1<(high.L:ℝ))
    (_hcap0:0≤(high.cap:ℝ))(_hcap1:(high.cap:ℝ)<1)
    (_hparent:QRH.Record12518109Existence.UnitFaceSource
      (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ)
    (_hnodes:∀δ∈G.nodes,NodeFacts3 n low high b reserve θ mesh G φ hlow ha hq hq1 hG hf.positive δ),
  RegularJointSupplier3 K n low b mesh ξ θ width G φ

end
end QRH.MixedStep.Downstream
#print axioms QRH.MixedStep.Downstream.RegularJointSupplier3
#print axioms QRH.MixedStep.Downstream.RegularSupplier3Statement
#print axioms QRH.MixedStep.Downstream.RegularJointSupplier3At
