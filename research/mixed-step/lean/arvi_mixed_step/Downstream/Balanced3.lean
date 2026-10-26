/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, N6): adapted from Record1252270103Source.Core.InitialRegularToTruncatedBalanced
(Collet's `balanced_of_regular`, Apache-2.0); changes: the first MAIN selection is transferred to the
residual families of its pieces (N3, `pieces_transfer_plain`), each family is paid by Collet's
`eventual_selected_second` with the residual regular inlet `RegularJointSupplier3`, the F6 MAIN
twins `eventually_initial_main_joint_saved_mx` (complement) and
`eventual_initial_remainder_sums_one_mx` (zero and tail), and the families are summed before
Collet's `selected_four_payment`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularToTruncatedBalanced
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Core.InitialRegularToTruncatedMainExceptionalSaving
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Core.InitialRegularToTruncatedRemainderOne
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Low.SelectedExceptionalInitialCapsAudit
import Submissions.arvi_mixed_step.Downstream.Contract3
import Submissions.arvi_mixed_step.Downstream.Families
import Submissions.arvi_mixed_step.Downstream.MainGates

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

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
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentEnergyBandMonotonicity
open Cycle61InitialMass RayFourExpansion Record1252270103Finite Record1252270103StepScalar
open Record1252270103Second
open QRH.Record1252270103Low QRH.Record1252270103Source
open QRH.Record1252270103Source.High.CoupledFirst QRH.Record1252270103Source.High.GlobalPhysical
open QRH.Record1252270103Source.Admission.FirstFamily
open OAI.SevenEighths.Record1252270103Source.Collision
open QRH.Record1252270103Source.Low.SelectedExceptionalNormalized
open QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
open QRH.Record1252270103Source.Low.InitialRemainder
open QRH.Record1252270103Source.InitialRegularToTruncated QRH.Record1252270103Source.InitialTruncated
open QRH.Record1252270103Source.InitialPhysical QRH.Record1252270103Source.ExceptionalPrice
open QRH.Record1252270103Source.Pool
open QRH.MixedStep.Residual QRH.MixedStep.Transfer
local notation "O" => HeckeFamily.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

/-- `log_Z c ≤ x` eventually, for every `x > 0`. -/
theorem eventually_logb_le (c x : ℝ) (hx : 0 < x) : ∀ᶠ Z : ℝ in atTop, Real.logb Z c ≤ x := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (|Real.log c| / x + 1)),
    eventually_gt_atTop (1:ℝ)] with Z hlog hZ
  have hlZ : 0 < Real.log Z := Real.log_pos hZ
  rw [Real.logb, div_le_iff₀ hlZ]
  have h1 : x * (|Real.log c| / x + 1) ≤ x * Real.log Z := mul_le_mul_of_nonneg_left hlog hx.le
  have h2 : x * (|Real.log c| / x + 1) = |Real.log c| + x := by field_simp
  have h3 := le_abs_self (Real.log c)
  nlinarith

theorem control_payment_mx (C U V G H X:ℝ)
    (hC:0≤C)(hU:0≤U)(hUV:U≤V)(hG:0≤G)(hH:0≤H)(hX:0≤X) :
    C*U^2*G*H*X≤C*V^2*G*H*X := by
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hU hUV 2) hC) hG) hH) hX

theorem mixed_control_payment_mx (C U V G H J X:ℝ)
    (hC:0≤C)(hU:0≤U)(hUV:U≤V)(hG:0≤G)(hH:0≤H)(hHJ:H≤J)(hX:0≤X) :
    C*U^2*H*G*X≤C*V^2*G*J*X := by
  have h:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hU hUV 2) hC)
      hHJ hH (mul_nonneg hC (sq_nonneg V))) hG) hX
  convert h using 1 <;> ring

/-- The labels of the piece `k`. -/
abbrev PieceLabels {α : Type} [Fintype α] [DecidableEq α] {Label : Type} {s : Input α}
    {C : Label → Ideal O} (alloc : ∀ l, actualAllocations s.pools (C l))
    (trans : Label → Finset α) (k : Finset α × Finset α) : Type :=
  {l : Label // pieceKey alloc trans l = k}

/-- Collet's `actual_first_fourier_child` for a child of another parent `s` (the residual of the
first-layer input `s₀`): only the frozen coefficient and the upper cap of `s` are used. -/
theorem piece_fourier_child {α ι₀ : Type} [Fintype α] [Fintype ι₀] [DecidableEq ι₀]
    (s : Input α) (s₀ : Input ι₀) (modifier : Tuple ι₀ → ℂ) (R seed : Ideal O)
    (Z ξ amp reserve : ℝ) (hZ : 1 < Z) (N : ℕ) (hN : Fintype.card α ≤ N) (hupper : s.upper ≤ 2)
    (reflected : Bool) (bin : ℤ × (Fin 5 → ℤ))
    (j : FirstColumnIndex (source s₀ modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin))
    (B : actualAllocations s.pools
      (columnIdeal reflected s₀ modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j))
    (τ : Character) (t : ℝ)
    (hf : frozenCoefficient B.val
      (columnIdeal reflected s₀ modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j) R s.ν s.W s.P ≠ 0) :
    (volume (child s (columnIdeal reflected s₀ modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j)
        R B τ t)) ^ 2 /
      firstMainRadius reflected Z (volume s) Z ξ (3 * amp) reserve
        (firstLabel s₀ modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j) ≤
      firstMainFourierScale reflected Z (volume s) Z ξ (3 * amp) reserve 2 N
        (firstLabel s₀ modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j) :=
  Cycle61FinalRadius.actual_second_radius_admissible N 2 (by norm_num) s hN hupper _ R B τ t _
    (first_main_radius_pos reflected Z (volume s) Z ξ (3 * amp) reserve (zero_lt_one.trans hZ) _) hf

theorem balanced_of_regular3 (K:ℚ)(n low:Source)(b:ℚ)(mesh ξ reserve width:ℝ)(G:NodeGrid)
    (φ:ℚ→ℝ)(Amix F εf:ℝ)
    (htw:MainTwinFacts K n low (b:ℝ) (n.lowFee:ℝ) Amix F (2*mesh))
    (hAd:(n.lowFee:ℝ)+(G.d:ℝ)≤Amix)(hAsmall:Amix<1/75)
    (hB:(n.B:ℝ)≤1)(hL:1≤(n.L:ℝ))(hc:(n.cap:ℝ)≤1)
    (he:0<(n.allowance:ℝ))(hfee:0≤(n.highFee:ℝ))
    (hm0:0<mesh)(hm:mesh<(n.lowFee:ℝ)/2)
    (hmg:2*mesh≤(G.g:ℝ))(hmκ:2*mesh≤(G.κ:ℝ))(hmd:0<G.d→2*mesh≤(G.d:ℝ))
    (hεf:width+G.g+G.κ≤εf)(hφtop:φ G.d≤0)
    (hφ:∀δ∈G.nodes,δ≠G.d→φ δ≤(b:ℝ)-G.theta δ-εf)
    (hx:0<ξ)(hx1:ξ≤1)(hxstep:ξ≤PhysicalLowGuard.step n)
    (hr0:0≤reserve)(hr1:reserve≤1)(hrstep:reserve≤PhysicalLowGuard.step n)
    (hw:width≤PhysicalLowGuard.step n)
    (htr:PlainTransfer)
    (hreg:RegularJointSupplier3 K n low b mesh ξ reserve width G φ) :
    BalancedInitialSupplier K n low (b:ℝ) mesh ξ width := by
  intro α instα instDec rayM instRay H hH Wslot hW hsW bΦ hbΦ η η₀ Q hQr hQ0 hQtop hQ72 R₀ hR
  let N:=Fintype.card α
  let amp:=(n.lowFee:ℝ)
  let ell:=amp/2
  have ha:0<amp:=htw.a_pos
  have hel:0<ell:=by dsimp only [ell];positivity
  have helamp:ell<amp:=by dsimp only [ell];linarith
  have hL0:0≤(n.L:ℝ):=zero_le_one.trans hL
  obtain ⟨dr,Sr,hSr,Cr,τ,σ,hCr,hτ,hσ,hreg'⟩:=hreg α rayM H hH Wslot hW hsW bΦ hbΦ
    η η₀ Q hQr hQ0 hQtop hQ72 R₀ hR
  -- the losses: `e` with `6e ≤ amp`, `2e ≤ σ`
  obtain ⟨e,he0,heSmall,hePaid,heAmp,heσ,heRem⟩:=choose_losses n (amp/2) (σ/2) ξ he hL0
    (by positivity) (by positivity) hxstep
  obtain ⟨depth,hdepth⟩:=exists_nat_ge ((2:ℝ)/ell)
  let W:=initialRadialBump bΦ (by linarith)
  have hAa:amp≤Amix:=htw.a_le
  have hcomp0:=eventually_initial_main_joint_saved_mx N le_rfl K n (b:ℝ) Amix amp (2*mesh)
    htw.centered htw.kappa_room hB hL hc rayM H hH Wslot hW hsW η η₀ R₀ hR fixedBadPrimes
    (Finset.Subset.refl _) ell mesh e ξ reserve width 32 depth hm0.le
    (by dsimp only [ell,amp]; linarith) helamp he0 hx hx1 hr0 hdepth (by norm_num) he hxstep hrstep hw
    W ballProfile 0 e e e e e e he0 he0 he0 he0 he0 he0 (by linarith only [heSmall]) hfee
    (by linarith only [hePaid,hAa,ha])
  obtain ⟨de,Se,Ce,hCe,hex⟩:=hcomp0 (internalQ Q η₀) hQ0 hQtop hQ72
  obtain ⟨Csel,hCsel,hmain⟩:=eventual_selected_main (α:=α) ξ e hx.le he0
  obtain ⟨S₀,S₁,C₀,C₁,hC₀,hC₁,hsecond⟩:=eventual_selected_second N 3 ξ 1 e (by norm_num) hx he0
  obtain ⟨Cz,Ct,hCz,hCt,hrem⟩:=eventual_initial_remainder_sums_one_mx rayM H hH Wslot hW hsW
    N ell e e e hel he0 he0.le he0
  obtain ⟨Kt,hKt1,htr'⟩:=pieces_transfer_plain htr (e/33) (by positivity) N
  let S:=Sr∪Se∪{(0,0)}
  have hSrS:Sr⊆S:=fun x hx=>Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hSeS:Se⊆S:=fun x hx=>Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hS:(0,0)∈S:=Finset.mem_union_right _ (Finset.mem_singleton_self _)
  let Cz':=C₀*16*S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Cz
  let Ct':=C₁*4*S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Ct
  let Mmax:=initialSlotBound Wslot hW hsW
  let nfam:ℝ:=((4^N*Fintype.card RayCharacter:ℕ):ℝ)
  let Sfac:=Csel*Kt*Mmax^(2*N)*nfam
  let Ctotal:=max 1 (Sfac*(Cz'+Cr+Ce+Ct'))
  have hCz':0≤Cz':=by dsimp only [Cz'];positivity
  have hCt':0≤Ct':=by dsimp only [Ct'];positivity
  refine ⟨max dr de,S,hS,Ctotal,τ,lt_of_lt_of_le zero_lt_one (le_max_left _ _),hτ,?_⟩
  have hcaps:=eventually_initial_caps N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hB hL hc
  have hgeom:=eventually_initial_first_geometry N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) ξ amp reserve
    hB hL hc hx hx1 ha.le (by linarith) hr0 hr1
  have hpool:=eventually_fixed_cell_pool rayM H hH fixedBadPrimes (Finset.Subset.refl _)
    amp ell mesh e 12 2 depth hm0.le (by dsimp only [ell,amp]; linarith) helamp he0
  have hfreq:=eventually_frequency_loss 32 ξ (by norm_num) hx
  have hlog:=eventually_logb_le (2*16^N) (6*mesh) (by positivity)
  filter_upwards [hreg',hex,hmain,hsecond,hrem,hcaps,hgeom,hpool,hfreq,
    eventually_ge_atTop ((2:ℝ)^(2*N)),hlog]
    with Z hzreg hzex hzmain hzsecond hzrem hzcaps hzgeom hzpool hzfreq hNpow hzlog
  refine ⟨hzreg.1,?_⟩
  intro hZ θ w v t ht height hwp hwm hh hv hheight p X₁ X₂ hX₁ hX₂ hadm hcross hwlo hwhi
    Y₂ hy₂ hl₁ hl₂ Y₁ hY₂ hY₁ hprod s modifier Wlocal Nlocal reflected bin
  have hZ0:=zero_lt_one.trans hZ
  have hcaps0:=hzcaps.2 hZ rayM H hH Wslot hW hsW η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod (le_refl _) hwp hadm hy₂ hl₁ hl₂
  have hz₁:s.W₁ 0=0:=initial_plain_zero p (by norm_num) 0
  have hz₂:s.W₂ 0=0:=initial_plain_zero p (by norm_num) 1
  have hscales:∀i,1≤s.P i:=fun i=>Real.one_le_rpow hZ.le (hwp i)
  have hhi2:∀i,s.hi i=2:=fun _=>rfl
  have hchildcap (j:FirstColumnIndex (source s modifier R₀ 1 Z Z ξ hZ0 bin))
      (B:actualAllocations s.pools (columnIdeal reflected s modifier R₀ 1 Z Z ξ hZ0 bin j)):
      sourceRadius (child s _ R₀ B (columnCharacter reflected s modifier R₀ 1 Z Z ξ hZ0 bin j) ht)≤
        Z^(2:ℝ):=
    (child_source_radius_le s _ R₀ B _ ht (fun _=>by norm_num [s,initialInput]) hscales
      (by norm_num [s,initialInput]) (by norm_num [s,initialInput])).trans hcaps0.2.1
  have hg0 (j:FirstColumnIndex (source s modifier R₀ 1 Z Z ξ hZ0 bin)):=
    hzgeom.2 hZ rayM H hH Wslot hW hsW η η₀ R₀ θ w v t p X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hprod (le_refl _) hwp hadm hy₂ hl₁ hl₂ modifier reflected bin j
  have hPA:PoolAvoids (CenteredMomentPrimePool.primePool rayM H fixedBadPrimes (1/2) 1 (Z^amp)) s:=by
    intro P hP i I hI
    exact hzpool.avoids_canonical_slot rayM H (w i) (hwm i) P hP I hI
  obtain ⟨labels,column,hinj,hlive,alloc,hf,hfirst⟩:=hzmain.2 hZ s R₀ hz₁ hz₂ hcaps0.1 hcaps0.2.1
    hcaps0.2.2.2.1 W ht ell amp reserve _ hzpool.nonempty hzpool.prime
    (fun P hP=>hzpool.avoids_bad P hP) hPA
    hel hzpool.norm_lower hzpool.norm_upper hzpool.card_source
    reflected bin (fun j _=>(hg0 j).2.1) (fun j _=>(hg0 j).2.2.2.1)
    (fun j _ B _=>hchildcap j B)
  let common:=fun l:labels=>columnIdeal reflected s modifier R₀ 1 Z Z ξ hZ0 bin (column l)
  let label:=fun l:labels=>firstLabel s modifier R₀ 1 Z Z ξ hZ0 bin (column l)
  let radius:=fun l:labels=>literalFirstRadius reflected Z (volume s) Z ξ reserve (label l)
  let H0:=fun l:labels=>(source s modifier R₀ 1 Z Z ξ hZ0 bin (column l).1).H0
  let scalar:=fun l:labels=>balancedColumnScalar reflected s modifier R₀ 1 Z Z ξ 1
    (Real.logb Z (volume s)) hZ0 bin (fun q=>normPhase (coordinateBlock s modifier R₀ 1 W Z Z ξ q)) (column l)
  let P:=CenteredMomentPrimePool.primePool rayM H fixedBadPrimes (1/2) 1 (Z^amp)
  let amplitude:=fun l:labels=>‖scalar l‖^2*
    (((bands (H0 l)).card:ℝ)*((actualAllocations s.pools (common l)).card:ℝ)^2/(P.card:ℝ)*
      ((radius l+6*amp)/ell))*‖frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P‖^2
  have ha0:∀l:labels,0≤amplitude l:=by
    intro l
    have hrad:0≤radius l+6*amp:=(hg0 (column l)).2.1
    dsimp only [amplitude]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
      (div_nonneg hrad hel.le))) (sq_nonneg _)
  -- the pieces: every live slot is transferable
  let trans:=fun l:labels=>liveIndices (alloc l).val
  have htrans:∀l,trans l⊆liveIndices (alloc l).val:=fun _=>le_rfl
  have hJlive:∀l,pieceBlock G w mesh (trans l)⊆liveIndices (alloc l).val:=
    fun l=>(pieceBlock_subset G w mesh _).trans (htrans l)
  have hHA:∀l,firstMainRadius reflected Z (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ
      (3*(amp+pieceNode G w (trans l))) reserve (label l)≤Z^(33:ℝ):=by
    intro l
    have hW1:1≤∏ j∈pieceBlock G w mesh (trans l),s.P j:=by
      calc (1:ℝ)=∏ _j∈pieceBlock G w mesh (trans l),(1:ℝ):=Finset.prod_const_one.symm
        _≤∏ j∈pieceBlock G w mesh (trans l),s.P j:=
          Finset.prod_le_prod₀ (fun _ _=>zero_le_one) (fun j _=>hscales j)
    rw [volume_restrict]
    have h1:=firstMainRadius_restrict_le reflected Z (volume s) Z ξ amp (pieceNode G w (trans l))
      reserve (∏ j∈pieceBlock G w mesh (trans l),s.P j) (label l) hZ hW1
    have h2:firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (label l)=
        Z^(radius l+6*amp):=((hg0 (column l)).2.2.2.2.2.2).symm
    have h3:radius l+6*amp≤32:=(hg0 (column l)).2.2.1
    have hδ:(pieceNode G w (trans l):ℝ)≤G.d:=by
      have:=G.nodeOf_le_top (Finset.sum_nonneg (fun i _=>hwp i) : 0≤∑ i∈trans l,w i)
      exact_mod_cast this
    have h6:6*(pieceNode G w (trans l):ℝ)≤1:=by linarith
    calc _≤firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (label l)*
          Z^(6*(pieceNode G w (trans l):ℝ)):=h1
      _=Z^(radius l+6*amp)*Z^(6*(pieceNode G w (trans l):ℝ)):=by rw [h2]
      _≤Z^(32:ℝ)*Z^(1:ℝ):=mul_le_mul (Real.rpow_le_rpow_of_exponent_le hZ.le h3)
          (Real.rpow_le_rpow_of_exponent_le hZ.le h6) (by positivity) (by positivity)
      _=Z^(33:ℝ):=by rw [← Real.rpow_add hZ0]; norm_num
  have hpieces:=htr' (le_refl _) s w Z mesh Mmax hZ (fun _=>rfl)
    (fun i=>⟨by rw [hhi2 i]; norm_num, by rw [hhi2 i]⟩) (initialSlotBound_ge_one Wslot hW hsW)
    (fun _=>le_rfl) hm0.le hwp hwm hzlog G hmg hmκ hmd common (fun l=>(column l).2.1.val) alloc
    trans htrans reflected s modifier R₀ 1 Z Z ξ hZ0 bin column R₀ P hzpool.prime hPA
    amplitude ha0 ht amp reserve 33 (by norm_num) hHA
  have hCselZ:0≤Csel*Z^e:=mul_nonneg hCsel.le (Real.rpow_nonneg hZ0.le _)
  have hbase0:=hfirst.trans (mul_le_mul_of_nonneg_left hpieces hCselZ)
  let G':=geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin
  let Pc:=p.control S
  let Hh:=1+|ht|+height
  let zB:=Cz'*Pc^2*G'*Z^(-amp-(n.allowance:ℝ)+2*e)
  let rB:=Cr*Pc^2*G'*Hh^dr*Z^(-σ)
  let cB:=Ce*Pc^2*G'*Hh^de*Z^(-amp)
  let tB:=Ct'*Pc^2*G'*Z^(-amp-(n.allowance:ℝ)-1+2*e)
  have hseed:∀l:labels,Squarefree (column l).2.1.val:=fun l=>
    live_projector_squarefree s modifier R₀ 1 Z Z ξ hZ0 bin (fun _=>logAnnulus) (column l) (hlive l)
  have hcommon:∀l:labels,common l≠0:=by
    intro l
    have h:=label_supported s modifier R₀ 1 Z Z ξ hZ0 bin (column l)
    cases reflected
    · exact h.1.1
    · exact h.2.1.1
  have hb1:0≤s.b₁:=by norm_num [s,initialInput]
  have hb2:0≤s.b₂:=by norm_num [s,initialInput]
  have hup:s.upper≤2:=by norm_num [s,initialInput]
  have hG:0≤G':=(geometry_high_factor_pos reflected _ bin
    (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hp0:=plain_profile_control p S hS
  have hpr:=profile_control_mono p hSrS
  have hpe:=profile_control_mono p hSeS
  have herr:frequencyLoss Z 32 ξ+reserve+2*e+e+e≤2*(n.allowance:ℝ):=by
    have hfreq0:=hzfreq.2.2.le.trans hxstep
    linarith only [heRem,hfreq0,hrstep]
  have hwidth:(b:ℝ)-(n.allowance:ℝ)-width≤∑i,w i:=by linarith
  have hAd':amp+(G.d:ℝ)≤Amix:=hAd
  have hmargin:∀l,φ (pieceNode G w (trans l))≤(∑i,w i)-∑i∈liveIndices (alloc l).val,w i:=by
    intro l
    by_cases hd:pieceNode G w (trans l)=G.d
    · rw [hd]
      exact hφtop.trans (frozen_first_nonneg w hwp _)
    · exact (hφ _ (pieceFacts G w (trans l) hm0.le hwp hwm hmg hmκ hmd).node_mem hd).trans
        (piece_frozen_first G w (alloc l) hwp hwlo hεf hd)
  have hfam:∀k∈Finset.univ.image (pieceKey alloc trans),∀ξr:RayCharacter,
      (∑ l:PieceLabels alloc trans k,amplitude l.val*
        pieceEnergy s common alloc trans htrans G w mesh reflected s modifier R₀ 1 Z Z ξ hZ0 bin
          column (fun l=>(column l).2.1.val) R₀ P ht Z amp reserve k ξr l)≤zB+(rB+cB)+tB:=by
    intro k _ ξr
    have hPF:=pieceFacts G w k.2 hm0.le hwp hwm hmg hmκ hmd
    have hkt:∀l:PieceLabels alloc trans k,trans l.val=k.2:=fun l=>congrArg Prod.snd l.property
    have hJlive:∀l:PieceLabels alloc trans k,pieceBlock G w mesh k.2⊆liveIndices (alloc l.val).val:=
      fun l=>pieceBlock_sub_live s common alloc trans htrans G w mesh l
    have hmarg:∀l:PieceLabels alloc trans k,φ (pieceNode G w k.2)≤
        (∑i,w i)-∑i∈liveIndices (alloc l.val).val,w i:=by
      intro l
      have h:=hmargin l.val
      rwa [hkt l] at h
    have hδ0:(0:ℝ)≤(pieceNode G w k.2:ℝ):=by exact_mod_cast hPF.node_nonneg
    have hδd:(pieceNode G w k.2:ℝ)≤(G.d:ℝ):=by exact_mod_cast hPF.node_le_top
    have hav1:amp≤amp+(pieceNode G w k.2:ℝ):=by linarith
    have hav2:amp+(pieceNode G w k.2:ℝ)≤Amix:=by linarith
    have hav3:amp+(pieceNode G w k.2:ℝ)-amp≤(∑j∈pieceBlock G w mesh k.2,w j)+2*mesh:=by
      linarith [hPF.shift]
    let Jk:=pieceBlock G w mesh k.2
    let sv:=s.restrict Jk
    have hscalesv:∀i:{i//i∉Jk},1≤sv.P i:=fun i=>hscales i.val
    have hhiV:∀i:{i//i∉Jk},sv.hi i≤2:=fun i=>(hhi2 i.val).le
    have hW1:1≤∏ j∈Jk,s.P j:=by
      calc (1:ℝ)=∏ _j∈Jk,(1:ℝ):=Finset.prod_const_one.symm
        _≤∏ j∈Jk,s.P j:=Finset.prod_le_prod₀ (fun _ _=>zero_le_one) (fun j _=>hscales j)
    have hvolsv:volume sv≤volume s:=by
      rw [volume_restrict]
      exact div_le_self (CenteredMomentAmplificationChildInput.volume_pos s).le hW1
    have hsvr:sourceRadius sv≤Z^(2:ℝ):=
      (sourceRadius_restrict_le s Jk (fun i=>by rw [hhi2 i];norm_num) hscales hb1 hb2).trans hcaps0.2.1
    have hcardsv:Fintype.card {i//i∉Jk}≤N:=Fintype.card_subtype_le _
    let allocv:∀l:PieceLabels alloc trans k,actualAllocations sv.pools (common l.val):=
      fun l=>pieceAlloc s common alloc trans htrans G w mesh l
    let chars:PieceLabels alloc trans k→Character:=fun l=>
      columnCharacter reflected s modifier R₀ 1 Z Z ξ hZ0 bin (rayShift reflected (column l.val) ξr)
    have hfeq:∀l:PieceLabels alloc trans k,
        frozenCoefficient (allocv l).val (common l.val) R₀ sv.ν sv.W sv.P=
          frozenCoefficient (alloc l.val).val (common l.val) R₀ s.ν s.W s.P:=fun l=>
      frozenCoefficient_restrict s (common l.val) R₀ (alloc l.val) Jk (hJlive l)
    have hfv:∀l:PieceLabels alloc trans k,
        frozenCoefficient (allocv l).val (common l.val) R₀ sv.ν sv.W sv.P≠0:=fun l=>by
      rw [hfeq l]
      exact hf l.val
    let Hv:PieceLabels alloc trans k→ℝ:=fun l=>
      firstMainRadius reflected Z (volume sv) Z ξ (3*(amp+(pieceNode G w k.2:ℝ))) reserve (label l.val)
    let Tsecv:PieceLabels alloc trans k→ℝ:=fun l=>
      firstMainFourierScale reflected Z (volume sv) Z ξ (3*(amp+(pieceNode G w k.2:ℝ))) reserve 2 N
        (label l.val)
    have hHv:∀l,0<Hv l:=fun l=>first_main_radius_pos reflected Z (volume sv) Z ξ
      (3*(amp+(pieceNode G w k.2:ℝ))) reserve hZ0 (label l.val)
    let Λ:PieceLabels alloc trans k→ℝ:=fun l=>initialCann N/((common l.val).absNorm:ℝ)
    have hΛ:∀l,0<Λ l:=fun l=>div_pos (initialCann_pos N) (by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hcommon l.val)))
    have hchild:∀l:PieceLabels alloc trans k,
        sourceRadius (child sv (common l.val) R₀ (allocv l) (chars l) ht)≤Z^(2:ℝ):=fun l=>
      (child_source_radius_le sv _ R₀ (allocv l) _ ht
        (fun i=>by rw [show sv.hi i=2 from hhi2 i.val];norm_num) hscalesv hb1 hb2).trans hsvr
    have hVchild:∀l:PieceLabels alloc trans k,
        volume (child sv (common l.val) R₀ (allocv l) (chars l) ht)≤Z^(3:ℝ):=by
      intro l
      have h:=ForcedCost.child_volume_ordinary_bound sv (common l.val) R₀ (allocv l) (chars l) ht
        hscalesv
      have h':volume sv/ForcedCost.ordinaryNorm (allocv l).val≤volume sv:=
        div_le_self (CenteredMomentAmplificationChildInput.volume_pos sv).le
          (ForcedCost.ordinaryNorm_ge_one sv (common l.val) (allocv l))
      exact (h.trans h').trans (hvolsv.trans (hcaps0.2.2.2.1.trans (by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : (1:ℝ)≤3))))
    have hTsec:∀l:PieceLabels alloc trans k,Tsecv l≤Z^(3:ℝ):=by
      intro l
      have h:=modified_main_frequency_cap_mx reflected s modifier R₀ 1 Z Z ξ
        (3*(amp+(pieceNode G w k.2:ℝ))) reserve (volume sv) N hZ0 hZ
        (CenteredMomentAmplificationChildInput.volume_pos sv) hx.le hx1 (by linarith) hr0 le_rfl hNpow
        bin (column l.val)
      have hp:0≤Tsecv l:=by
        change 0≤_ ^ 2/Hv l
        exact div_nonneg (sq_nonneg _) (hHv l).le
      exact (show Tsecv l≤frequencyRadius (Tsecv l) Z ξ from by
        unfold frequencyRadius
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.one_le_rpow hZ.le (by positivity :0≤ξ/2)) hp).trans h
    have hnom:∀l:PieceLabels alloc trans k,
        (volume (child sv (common l.val) R₀ (allocv l) (chars l) ht))^2/Hv l≤Tsecv l:=fun l=>
      piece_fourier_child sv s modifier R₀ 1 Z ξ (amp+(pieceNode G w k.2:ℝ)) reserve hZ N hcardsv hup
        reflected bin (column l.val) (allocv l) (chars l) ht (hfv l)
    have hinjk:Function.Injective (fun l:PieceLabels alloc trans k=>
        (firstLabel s modifier R₀ 1 Z Z ξ hZ0 bin (column l.val),(column l.val).2.1.val)):=
      hinj.comp Subtype.val_injective
    have hrema:=hzrem.2 hZ0 η η₀ R₀ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod n low (b:ℝ) width Amix F
      amp (2*mesh) htw.room htw.F_nonneg htw.F_amp he.le hL0 htw.lowB_le hw hadm hwidth hwhi (le_refl _)
      ha.le htw.kappa_nonneg htw.kappa_le Jk (amp+(pieceNode G w k.2:ℝ)) hav1 hav2 hav3
      modifier R₀ W ξ reserve e 1 hZ0 herr P mesh 12 2 depth hzpool
    have hrema':=hrema reflected bin (PieceLabels alloc trans k) (fun l=>column l.val) hinjk
      (fun l=>hlive l.val) (fun l=>(hg0 (column l.val)).2.2.2.2.2.1)
      (fun l=>(hg0 (column l.val)).2.1) (fun l=>(hg0 (column l.val)).2.2.1) allocv chars (fun _=>ht) hfv
    let f:=mainAllocatedFamily sv ballProfile (p.profile 0) (p.profile 1) Z R₀
      (fun l:PieceLabels alloc trans k=>common l.val) (fun l=>(column l.val).2.1.val) allocv chars
      (fun _=>ht) P (fun l=>hseed l.val) hz₁ hz₂ Hv Tsecv (fun _=>volume sv)
      (fun l=>amplitude l.val) ξ hHv (fun _=>(1:RayCharacter)) (fixedBadMask*idealGenerator R₀)
    let zeroTerm:=fun l:PieceLabels alloc trans k=>C₀*(4*plainControl (f.input l) (p.profile 0) (p.profile 1))^2*
      S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Hv l*(Λ l)^(1+e)*(volume sv)^e/
        (column l.val).2.1.val.absNorm
    let tailTerm:=fun l:PieceLabels alloc trans k=>C₁*(2*plainControl (f.input l) (p.profile 0) (p.profile 1))^2*
      S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Hv l*
        (volume (f.input l)/volume sv)*Z^(-1:ℝ)/(column l.val).2.1.val.absNorm
    have hs:(∑ l:PieceLabels alloc trans k,amplitude l.val*correctedChildGaussEnergy sv 1 1 1 1
        (common l.val) R₀ (column l.val).2.1.val (fun _=>1) P (allocv l) (chars l) ht (volume sv)
        (Hv l))≤
        (∑ l,amplitude l.val*zeroTerm l)+(regularJointNorm f (internalQ Q η₀)+
          ‖∑q:f.Carrier,f.phase (internalQ Q η₀) q*(f.block (internalQ Q η₀) q).value ballProfile‖)+
        ∑ l,amplitude l.val*tailTerm l:=
      hzsecond.2 hcardsv sv R₀ (fun l:PieceLabels alloc trans k=>common l.val)
        (fun l=>(column l.val).2.1.val) allocv chars ht P hzpool.nonempty hzpool.prime ell 2 hel
        hzpool.norm_lower hzpool.card_source hchild (p.profile 0) (p.profile 1) rfl rfl hz₁ hz₂
        (p.support 0) (p.support 1) hhiV (fun l=>hseed l.val)
        (fun l=>(hg0 (column l.val)).2.2.2.2.2.1) Λ Hv Tsecv (volume sv) hΛ
        (CenteredMomentAmplificationChildInput.volume_pos sv) hrema'.1 hHv hVchild hTsec hnom
        (fun l=>amplitude l.val) (fun l=>ha0 l.val) (fun _=>1) (fixedBadMask*idealGenerator R₀)
        (internalQ Q η₀)
    -- the regular term
    have hr:regularJointNorm f (internalQ Q η₀)≤Cr*(p.control Sr)^2*G'*(1+|ht|+height)^dr*Z^(-σ):=
      hzreg.2 hZ θ w v t ht height hwp hwm hh hv hheight p X₁ X₂ hX₁ hX₂ hadm hcross hwlo hwhi
        hy₂ hl₁ hl₂ (pieceNode G w k.2) hPF.node_mem Jk hPF.theta_le_act hPF.act_le_node hPF.shift
        reflected bin (fun l:PieceLabels alloc trans k=>column l.val) (fun l=>hlive l.val)
        (fun l=>(column l.val).2.1.val) (fun l=>hseed l.val) (fun _=>dvd_rfl) hinjk
        (fun l=>alloc l.val) hJlive (fun l=>hf l.val) hmarg ξr (fun _=>1)
    have hr':regularJointNorm f (internalQ Q η₀)≤rB:=
      hr.trans (control_payment_mx Cr _ _ G' _ _ hCr.le (p.control_nonneg _) hpr hG (by positivity)
        (Real.rpow_nonneg hZ0.le _))
    -- the complement: the twin's amplitude has the residual frozen coefficient
    let ampT:PieceLabels alloc trans k→ℝ:=fun l=>‖scalar l.val‖^2*
      (((bands (H0 l.val)).card:ℝ)*((actualAllocations s.pools (common l.val)).card:ℝ)^2/(P.card:ℝ)*
        ((radius l.val+6*amp)/ell))*
      ‖frozenCoefficient (allocv l).val (common l.val) R₀ sv.ν sv.W sv.P‖^2
    have hAmpEq:∀l,ampT l=amplitude l.val:=by
      intro l
      show ‖scalar l.val‖^2*
        (((bands (H0 l.val)).card:ℝ)*((actualAllocations s.pools (common l.val)).card:ℝ)^2/(P.card:ℝ)*
          ((radius l.val+6*amp)/ell))*
        ‖frozenCoefficient (allocv l).val (common l.val) R₀ sv.ν sv.W sv.P‖^2=_
      rw [hfeq l]
    let ftw:=mainAllocatedFamily sv ballProfile (p.profile 0) (p.profile 1) Z R₀
      (fun l:PieceLabels alloc trans k=>common l.val) (fun l=>(column l.val).2.1.val) allocv chars
      (fun _=>ht) P (fun l=>hseed l.val) hz₁ hz₂ Hv Tsecv (fun _=>volume sv)
      ampT ξ hHv (fun _=>(1:RayCharacter)) (fixedBadMask*idealGenerator R₀)
    have hftw:ftw=f:=by
      have hA:ampT=fun l=>amplitude l.val:=funext hAmpEq
      show mainAllocatedFamily sv ballProfile (p.profile 0) (p.profile 1) Z R₀
        (fun l:PieceLabels alloc trans k=>common l.val) (fun l=>(column l.val).2.1.val) allocv chars
        (fun _=>ht) P (fun l=>hseed l.val) hz₁ hz₂ Hv Tsecv (fun _=>volume sv)
        ampT ξ hHv (fun _=>(1:RayCharacter)) (fixedBadMask*idealGenerator R₀)=f
      rw [hA]
    have hinjk':Function.Injective (fun l:PieceLabels alloc trans k=>
        (firstLabel s modifier R₀ 1 Z Z ξ hZ0 bin (rayShift reflected (column l.val) ξr),
          (rayShift reflected (column l.val) ξr).2.1.val)):=hinjk
    have hlivek':∀l:PieceLabels alloc trans k,rayShift reflected (column l.val) ξr∈
        firstLiveColumns (source s modifier R₀ 1 Z Z ξ hZ0 bin) (fun _=>logAnnulus):=fun l=>
      (rayShift_mem_firstLiveColumns reflected (column l.val) ξr _).mpr (hlive l.val)
    have hcomp0:‖∑q:ftw.Carrier,ftw.phase (internalQ Q η₀) q*
        (ftw.block (internalQ Q η₀) q).value ballProfile‖≤
        Ce*(p.control Se)^2*(1+|ht|)^de*G'*Z^(-Amix):=
      hzex.2 hZ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hwp hwm hadm hwidth hwhi hy₂ hl₁ hl₂ rfl
        Jk (amp+(pieceNode G w k.2:ℝ)) hav1 hav2 hav3 reflected bin
        (fun l:PieceLabels alloc trans k=>rayShift reflected (column l.val) ξr) hinjk' hlivek'
        (fun l=>(hg0 (column l.val)).2.2.2.2.2.1) allocv (fun _=>ht) (fun l=>H0 l.val)
        (fun l=>radius l.val) |ht| (fun _=>1) (abs_nonneg _) (fun _=>(Real.norm_eq_abs ht).le)
        (fun l=>(hg0 (column l.val)).1) (fun l=>(hg0 (column l.val)).2.1)
        (fun l=>(hg0 (column l.val)).2.2.1)
    rw [hftw] at hcomp0
    have hc':‖∑q:f.Carrier,f.phase (internalQ Q η₀) q*(f.block (internalQ Q η₀) q).value ballProfile‖≤cB:=by
      apply hcomp0.trans
      have hp:(1+|ht|)^de≤(1+|ht|+height)^de:=pow_le_pow_left₀ (by positivity) (by linarith) _
      have hZm:Z^(-Amix)≤Z^(-amp):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
      calc Ce*(p.control Se)^2*(1+|ht|)^de*G'*Z^(-Amix)≤Ce*(p.control Se)^2*(1+|ht|)^de*G'*Z^(-amp):=
            mul_le_mul_of_nonneg_left hZm (by positivity)
        _≤cB:=mixed_control_payment_mx Ce _ _ G' _ _ _ hCe.le (p.control_nonneg _) hpe hG
          (by positivity) hp (Real.rpow_nonneg hZ0.le _)
    -- the zero and tail terms
    have hzsum:(∑ l:PieceLabels alloc trans k,amplitude l.val*zeroTerm l)≤zB:=by
      have hid:(∑ l:PieceLabels alloc trans k,amplitude l.val*zeroTerm l)=
          (C₀*16*S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)*
          ∑ l:PieceLabels alloc trans k,ampT l*(plainControl (f.input l) (p.profile 0) (p.profile 1))^2*
            Hv l*(Λ l)^(1+e)*(volume sv)^e/(column l.val).2.1.val.absNorm:=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [hAmpEq l]
        dsimp only [zeroTerm]
        ring
      rw [hid]
      apply (mul_le_mul_of_nonneg_left hrema'.2.1 (by positivity)).trans
      have hp2:=pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hp0 2
      convert mul_le_mul_of_nonneg_left hp2 (show 0≤C₀*16*S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        ballProfile*Cz*G'*Z^(-amp-(n.allowance:ℝ)+2*e) by positivity) using 1 <;>
        dsimp only [zB,Cz',G',Pc] <;> ring
    have htsum:(∑ l:PieceLabels alloc trans k,amplitude l.val*tailTerm l)≤tB:=by
      have hid:(∑ l:PieceLabels alloc trans k,amplitude l.val*tailTerm l)=
          (C₁*4*S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)*
          ∑ l:PieceLabels alloc trans k,ampT l*(plainControl (f.input l) (p.profile 0) (p.profile 1))^2*
            Hv l*(volume (f.input l)/volume sv)*Z^(-1:ℝ)/(column l.val).2.1.val.absNorm:=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [hAmpEq l]
        dsimp only [tailTerm]
        ring
      rw [hid]
      apply (mul_le_mul_of_nonneg_left hrema'.2.2 (by positivity)).trans
      have hp2:=pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hp0 2
      convert mul_le_mul_of_nonneg_left hp2 (show 0≤C₁*4*S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        ballProfile*Ct*G'*Z^(-amp-(n.allowance:ℝ)-1+2*e) by positivity) using 1 <;>
        dsimp only [tB,Ct',G',Pc] <;> ring
    exact hs.trans (add_le_add (add_le_add hzsum (add_le_add hr' hc')) htsum)
  -- the sum over the pieces
  have hHh:1≤Hh:=by dsimp only [Hh]; linarith [abs_nonneg ht]
  have hHh0:0≤Hh:=zero_le_one.trans hHh
  have hPc0:0≤Pc:=p.control_nonneg _
  have hzB0:0≤zB:=by dsimp only [zB]; positivity
  have hrB0:0≤rB:=by dsimp only [rB]; positivity
  have hcB0:0≤cB:=by dsimp only [cB]; positivity
  have htB0:0≤tB:=by dsimp only [tB]; positivity
  have hT0:0≤zB+(rB+cB)+tB:=by positivity
  have hM1:1≤Mmax:=initialSlotBound_ge_one Wslot hW hsW
  have hSfac:0≤Sfac:=mul_nonneg (mul_nonneg (mul_nonneg hCsel.le (zero_le_one.trans hKt1))
    (pow_nonneg (zero_le_one.trans hM1) _)) (Nat.cast_nonneg _)
  have hsumk:(∑ k∈Finset.univ.image (pieceKey alloc trans),∑ ξr:RayCharacter,
      ∑ l:PieceLabels alloc trans k,amplitude l.val*
        pieceEnergy s common alloc trans htrans G w mesh reflected s modifier R₀ 1 Z Z ξ hZ0 bin
          column (fun l=>(column l).2.1.val) R₀ P ht Z amp reserve k ξr l)≤
      nfam*(zB+(rB+cB)+tB):=by
    calc _≤∑ k∈Finset.univ.image (pieceKey alloc trans),∑ _ξr:RayCharacter,(zB+(rB+cB)+tB):=
          Finset.sum_le_sum (fun k hk=>Finset.sum_le_sum (fun ξr _=>hfam k hk ξr))
      _=(((Finset.univ.image (pieceKey alloc trans)).card*Fintype.card RayCharacter:ℕ):ℝ)*
          (zB+(rB+cB)+tB):=by
        simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Nat.cast_mul]
        ring
      _≤nfam*(zB+(rB+cB)+tB):=by
        apply mul_le_mul_of_nonneg_right _ hT0
        exact Nat.cast_le.mpr (Nat.mul_le_mul_right _ (card_pieces_le (pieceKey alloc trans)))
  have hKM:0≤Kt*Mmax^(2*N)*Z^(33*(e/33)):=
    mul_nonneg (mul_nonneg (zero_le_one.trans hKt1) (pow_nonneg (zero_le_one.trans hM1) _))
      (Real.rpow_nonneg hZ0.le _)
  have hstep:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumk hKM) hCselZ
  have h33:Z^(33*(e/33))=Z^e:=by congr 1; ring
  have h2e:Z^e*Z^e=Z^(2*e):=by rw [← Real.rpow_add hZ0]; congr 1; ring
  have hbase:_≤(Sfac*Z^(2*e))*(zB+(rB+cB)+tB):=hbase0.trans (hstep.trans (le_of_eq (by
    rw [h33,← h2e]
    dsimp only [Sfac]
    ring)))
  have hz2:zB≤Cz'*Pc^2*G'*Z^(-amp-(n.allowance:ℝ)+2*(2*e)):=by
    show Cz'*Pc^2*G'*Z^(-amp-(n.allowance:ℝ)+2*e)≤_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
      (by positivity)
  have ht2:tB≤Ct'*Pc^2*G'*Z^(-amp-(n.allowance:ℝ)-1+2*(2*e)):=by
    show Ct'*Pc^2*G'*Z^(-amp-(n.allowance:ℝ)-1+2*e)≤_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
      (by positivity)
  have htotal:=selected_four_payment Z (2*e) amp (n.allowance:ℝ) σ Sfac Cz' Cr Ce Ct' Pc G' Hh _ zB rB cB tB
    dr de hZ.le (by linarith) (by linarith) (by linarith) he.le hSfac hCz' hCr.le hCe.le hCt' hG hHh
    hbase hz2 le_rfl le_rfl ht2
  apply htotal.trans
  gcongr
  exact le_max_right _ _

end
end QRH.MixedStep.Downstream
#print axioms QRH.MixedStep.Downstream.balanced_of_regular3
#print axioms QRH.MixedStep.Downstream.piece_fourier_child
