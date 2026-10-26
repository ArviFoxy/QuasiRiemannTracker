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
  have hfam:∀k∈Finset.univ.image (pieceKey alloc trans),∀ξr:RayCharacter,
      (∑ l:{l//pieceKey alloc trans l=k},amplitude l.val*
        pieceEnergy s common alloc trans htrans G w mesh reflected s modifier R₀ 1 Z Z ξ hZ0 bin
          column (fun l=>(column l).2.1.val) R₀ P ht Z amp reserve k ξr l)≤zB+(rB+cB)+tB:=by
    sorry
  sorry

end
end QRH.MixedStep.Downstream
