/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Core.InitialRegularToTruncatedMainExceptional
(Hailey Collet). Original notes: the first radial profile and
the second ball profile are independent; the actual MAIN correction is evaluated at the child column
(frozen factor one); the literal initial complementary family, with its first frozen coefficients,
is paid by the checked second radical sum and the original first MAIN scalar; all constants precede
the moving profiles, scales, widths and heights.

**MAIN complement twin** (design `L45_DESIGN.md` §3 F6, risk 6). Two parents, two amplitudes:
* first layer: the canonical initial input `s₀` (columns, labels, common ideals, projector seeds,
  characters, the balanced scalar at `logb Z (volume s₀)`, the MAIN-prefactor allocation card);
* second layer: the transfer residual `s := s₀.restrict J` (allocations, frozen coefficients,
  children, `volume s`, the MAIN radius and Fourier scale at `(volume s, 3·amp)`);
* the pool `P` of actual width `a` (the amplitude's `1/|P|` and ball factor `radius+6a`); the MAIN
  radius amplitude `amp` (`= a + δ` at the transfer node) with `a ≤ amp ≤ Amix`;
* the δ-shift `amp - a ≤ Σ_{j∈J} w j + κ` (= `logb Z (volume s₀) - logb Z (volume s) + κ`).
The node facts enter as plain hypotheses: the mixed centered gate
`hgate : T + 9·Amix + fee < 5/6 + 0.499·Lref` (`MixedGeometry.centered_twin`) and the error room
`hκ : e + 2κ ≤ 2·Amix - a`. The target is Collet's with `amp` replaced by `Amix`. The constants are
uniform in the block `J ⊆ α` (finitely many residual slot types). -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularToTruncatedMainExceptional
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Core.ExceptionalFrozenOne
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Core.ExceptionalFirstErrors
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Contraction.SelectedMainExceptionalAggregate
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Low.SelectedExceptionalInitialCapsAudit
import Submissions.arvi_mixed_step.Downstream.MainRestrict

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths OAI.SevenEighths.Record1252270103Source
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CompletedGauss RayFourExpansion CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentSecondInputCapacitySource CenteredMomentSecondWindowBudget
open CenteredMomentFirstSectors CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSourceRow CenteredMomentFirstPhysicalSource CenteredMomentSupport
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstCanonicalFamily
open Cycle61Moment Cycle61InitialMass Record12518109Natural
open Record1252270103Finite Record1252270103StepScalar Record1252270103Second
open QRH.Record1252270103Low OAI.SevenEighths.Record1252270103Source.Collision
open High.CoupledFirst Admission.FirstFamily Pool InitialPhysical InitialTruncated
open Low.SelectedExceptionalNormalized
open QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
local notation "O"=>HeckeFamily.O
local notation "source"=>High.CoupledFirst.geometryFirstSource

/-- Profile controls are monotone in the control set (as `Cycle61Physical.profile_control_mono`). -/
theorem profile_control_le_mx {lo hi:ℝ}(p:Profiles lo hi){S T:Finset (ℕ×ℕ)}(hST:S⊆T) :
    p.control S≤p.control T := by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem eventually_initial_main_joint_mx {α:Type}[Fintype α][DecidableEq α]
    (N:ℕ)(hN:Fintype.card α≤N)(K:ℚ)(n:Source)(b Amix a κ:ℝ)
    (hgate:sourceTReal n b+b+9*Amix+(n.highFee:ℝ)<5/6+(499/1000)*(49/100-(K:ℝ)*b))
    (hκ:(n.allowance:ℝ)+2*κ≤2*Amix-a)
    (hB:(n.B:ℝ)≤1)(hL:1≤(n.L:ℝ))(hcap:(n.cap:ℝ)≤1)
    (rayM:Ideal O)[NeZero rayM](H:Subgroup (O⧸rayM)ˣ)
    (hH:RayOrthogonality.globalUnits rayM≤H)
    (Wslot:ℝ→ℂ)(hW:ContDiff ℝ ∞ Wslot)(hsW:Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (η η₀:Character)(R₀:Ideal O)(hR:R₀≠0)
    (Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (ell mesh poolLoss ξ reserve width radiusMax:ℝ)(depth:ℕ)
    (hmesh:0≤mesh)(hgap:mesh<ell)(hell:ell<a)(hloss:0<poolLoss)
    (hξ:0<ξ)(hξ1:ξ≤1)(hreserve:0≤reserve)(hdepth:(2:ℝ)/ell≤depth)
    (hradius:0≤radiusMax)(he:0<(n.allowance:ℝ))
    (hξstep:ξ≤PhysicalLowGuard.step n)(hrstep:reserve≤PhysicalLowGuard.step n)
    (hwstep:width≤PhysicalLowGuard.step n)
    (W Wsecond:𝓢(ℝ,ℂ))(decay:ℕ)(ε εL δ epsMass epsCount epsCard:ℝ)
    (hε:0<ε)(hεL:0<εL)(hδ:0<δ)(hεm:0<epsMass)(hεc:0<epsCount)(hεa:0<epsCard)
    (hsmall:epsCard+poolLoss+ξ/12≤PhysicalLowGuard.step n):
    ∀Q:Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃Ctotal:ℝ,0<Ctotal ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀{Label:Type}[Fintype Label],
    ∀(θ:α→RayQuotient.Characters rayM H)(w v:α→ℝ)(t:ℝ)
      (p:Profiles (1/4) (9/4))(X₁ X₂ Y₁ Y₂:ℝ)
      (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂),
    (∀i,0≤w i)→(∀i,w i≤mesh)→
    (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z X₁) (length Z X₂) (∑i,w i) 1→
    b-(n.allowance:ℝ)-width≤∑i,w i→(∑i,w i)≤b→
    1≤Y₂→Y₂≤X₁→Y₂≤X₂→Y₂=Z^(49/100-(K:ℝ)*b)→
    let s₀:=initialInput rayM H hH Wslot hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    let modifier:=markedSourceModifier 1 1 1 1 (fun _=>1)
    ∀(Jset:Finset α)(amp:ℝ),a≤amp→amp≤Amix→amp-a≤(∑j∈Jset,w j)+κ→
    let s:=s₀.restrict Jset
    ∀(reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
      (column:Label→FirstColumnIndex (source s₀ modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin)),
    Function.Injective (fun j=>(firstLabel s₀ modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column j),
      (column j).2.1.val))→
    ∀hLive:∀l,column l∈firstLiveColumns (source s₀ modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin)
      (fun _=>logAnnulus),
    (∀l,((column l).2.1.val.absNorm:ℝ)≤Z^(4:ℝ))→
    let hseed:∀l,Squarefree (column l).2.1.val:=fun l=>
      live_projector_squarefree s₀ modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin
        (fun _=>logAnnulus) (column l) (hLive l)
    let C:=fun l=>columnIdeal reflected s₀ modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    let scalar:=fun l=>balancedColumnScalar reflected s₀ modifier R₀ 1 Z Z ξ 1
      (Real.logb Z (volume s₀)) (zero_lt_one.trans hZ) bin
      (fun q=>normPhase (coordinateBlock s₀ modifier R₀ 1 W Z Z ξ q)) (column l)
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^a)
    ∀(alloc:∀l,actualAllocations s.pools (C l))(ht H0 radius:Label→ℝ)(height:ℝ)
      (χ₀:Label→RayCharacter),0≤height→(∀l,‖ht l‖≤height)→
      (∀l,0<H0 l)→(∀l,0≤radius l+6*a)→(∀l,radius l+6*a≤radiusMax)→
    let extra:=fun l=>((bands (H0 l)).card:ℝ)*((actualAllocations s₀.pools (C l)).card:ℝ)^2/
      (P.card:ℝ)*((radius l+6*a)/ell)
    let amplitude:=fun l=>‖scalar l‖^2*extra l*‖frozenCoefficient (alloc l).val (C l) R₀ s.ν s.W s.P‖^2
    let m:=fixedBadMask*idealGenerator R₀
    let τ:=fun l=>columnCharacter reflected s₀ modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    let labels:=fun l=>firstLabel s₀ modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    let Kmain:=fun l=>firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (labels l)
    let Tsec:=fun l=>firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve 2 N (labels l)
    let f:=InitialRegularToTruncated.mainAllocatedFamily s Wsecond (p.profile 0) (p.profile 1) Z R₀ C
      (fun l=>(column l).2.1.val) alloc τ ht P hseed (initial_plain_zero p (by norm_num) 0)
      (initial_plain_zero p (by norm_num) 1) Kmain Tsec (fun _=>volume s) amplitude ξ
      (fun l=>first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve
        (zero_lt_one.trans hZ) (labels l)) χ₀ m
    ‖∑q,f.phase Q q*(f.block Q q).value Wsecond‖≤
      Ctotal*(p.control S)^2*(1+height)^degree*
        geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        Z^(-(n.highFee:ℝ)-4*Amix+2*epsCount+epsMass+δ+4*εL+2*ε) := by
  have hL0:0≤(n.L:ℝ):=zero_le_one.trans hL
  have hel:0<ell:=hmesh.trans_lt hgap
  have hlower:=lowerFactor_pos N (1:ℝ) (1/4) (by norm_num) (by norm_num)
  obtain ⟨Cp,hCp,hpaid⟩:=selected_frozen_first_sum_one_mx N 1 (1/4) 2 4 epsCount epsCard ell
    (lowerFactor N 1 (1/4)) radiusMax (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hεc hεa hel hlower hradius
  intro Q hQ0 hQ hQ72
  have hfamJ:=fun Jset:Finset α=>
    Contraction.SelectedMainExceptional.eventually_initial_family_uniform_mx
      (α:={i // i∉Jset}) N ((Fintype.card_subtype_le _).trans hN) (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)
      hB hL hcap rayM H hH Wslot hW hsW η η₀ R₀ hR Sbad hbad a ell mesh poolLoss ξ depth
      hmesh hgap hell hloss hdepth Wsecond decay ε εL δ epsMass hε hεL hδ hεm Q hQ0 hQ hQ72
  choose degJ SJ CJ hCJ hfamJ using hfamJ
  let degree:ℕ:=Finset.univ.sup degJ
  let S:Finset (ℕ×ℕ):=Finset.univ.biUnion SJ
  let Ce:ℝ:=∑ J:Finset α,CJ J
  have hCe:0<Ce:=Finset.sum_pos (fun J _=>hCJ J) Finset.univ_nonempty
  have hCJle:∀J,CJ J≤Ce:=fun J=>
    Finset.single_le_sum (f:=CJ) (fun J _=>(hCJ J).le) (Finset.mem_univ J)
  have hdegle:∀J,degJ J≤degree:=fun J=>Finset.le_sup (f:=degJ) (Finset.mem_univ J)
  have hSle:∀J,SJ J⊆S:=fun J=>Finset.subset_biUnion_of_mem SJ (Finset.mem_univ J)
  let Cprofile:=((initialSlotBound Wslot hW hsW)^N)^2*(2:ℝ)^N
  have hprofile:0<Cprofile:=by
    have hh:=initialSlotBound_ge_one Wslot hW hsW
    dsimp only [Cprofile]
    positivity
  refine ⟨degree,S,Ce*Cp*Cprofile,by positivity,?_⟩
  have hcapsEv:=eventually_initial_caps N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hB hL hcap
  have hpoolEv:=eventually_fixed_cell_pool rayM H hH Sbad hbad a ell mesh poolLoss 12 2 depth
    hmesh hgap hell hloss
  have herrEv:=eventually_centered_error_guard_mx n ξ reserve (epsCard+poolLoss+ξ/12) width he hL0 hξ
    hξstep hreserve hrstep hsmall hwstep
  have hcharEv:=RegularSelectedStateCaps.eventually_actual_first_character_cap η 1 (by norm_num)
  have hfamEv:=Filter.eventually_all.2 hfamJ
  refine (hfamEv.and (hpaid.and (hcapsEv.and (hpoolEv.and (herrEv.and (hcharEv.and
    (eventually_ge_atTop ((2:ℝ)^(2*N))))))))).mono ?_
  rintro Z ⟨hz,hp,hcaps,hpool,herr,hcharZ,hNpow⟩
  refine ⟨hp.1,?_⟩
  intro hZ Label instLabel θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hw hwm hadm hwlo hwhi hy₂ hl₁ hl₂ hY s₀ modifier Jset amp hamplo hamp hshiftw s reflected bin
    column hinj hLive hseedcap hseed C scalar P alloc ht H0 radius height χ₀ hheight hht hH0 hr0 hr
    extra amplitude m τ labels Kmain Tsec f
  have hZ0:=zero_lt_one.trans hZ
  have hrad:=hcaps.2 hZ rayM H hH Wslot hW hsW η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hN hw hadm hy₂ hl₁ hl₂
  have hlog:=initial_log_volume_node_bound rayM H hH Wslot hW hsW Z hZ0 η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod n b width hZ hL0 hadm hwlo hwhi
  -- the residual: the canonical initial input of the restricted slot data
  have hcardv:Fintype.card {i // i∉Jset}≤N:=(Fintype.card_subtype_le _).trans hN
  have hwv:∀i:{i // i∉Jset},0≤w i.val:=fun i=>hw i.val
  have hwmv:∀i:{i // i∉Jset},w i.val≤mesh:=fun i=>hwm i.val
  have hadmv:=QRH.MixedStep.Downstream.restrict_admissible (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) _ _ hL0 w hw
    Jset hadm
  have hforce:forcedProfileCost s≤Cprofile:=(initial_cost_bounds rayM H hH Wslot hW hsW Z hZ0 η η₀ R₀
    (fun i:{i // i∉Jset}=>θ i.val) (fun i=>w i.val) (fun i=>v i.val) t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod N hcardv).2
  have hlogv:Real.logb Z (volume s)=Real.logb Z (volume s₀)-∑ j∈Jset,w j:=
    QRH.MixedStep.Downstream.logb_volume_restrict s₀ Jset Z hZ w (fun _=>rfl)
  have hshift:amp-a≤Real.logb Z (volume s₀)-Real.logb Z (volume s)+κ:=by
    rw [hlogv]
    linarith
  -- first-layer column caps
  have hCne:∀l,C l≠0:=by
    intro l
    have h:=label_supported s₀ modifier R₀ 1 Z Z ξ hZ0 bin (column l)
    cases reflected
    · exact h.1.1
    · exact h.2.1.1
  have hCcap:∀l,((C l).absNorm:ℝ)≤Z^(2:ℝ):=by
    intro l
    have h:=label_common_bounds s₀ modifier R₀ 1 Z Z ξ hZ0 bin squarefree_one
      (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1) (column l)
    cases reflected
    · exact h.2.2.1.trans hrad.2.1
    · exact h.2.2.2.trans hrad.2.1
  have hchar:∀l,((τ l).modulus.absNorm:ℝ)≤Z^(5:ℝ):=by
    intro l
    have hc:=hcharZ.2 reflected s₀ modifier rfl R₀ 1 Z ξ 2 hZ0 bin (column l)
      squarefree_one (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
      hrad.2.1
    convert hc using 1 <;> first | rfl | norm_num
  have hK:∀l,0<Kmain l:=fun l=>first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve hZ0
    (labels l)
  have hT0:∀l,0≤Tsec l:=by
    intro l
    change 0≤_ ^ 2 / Kmain l
    exact div_nonneg (sq_nonneg _) (hK l).le
  have hamp0:0≤3*amp:=by linarith
  have hradiusT:∀l,frequencyRadius (Tsec l) Z ξ≤Z^(3:ℝ):=fun l=>
    modified_main_frequency_cap_mx reflected s₀ modifier R₀ 1 Z Z ξ (3*amp) reserve (volume s) N
      hZ0 hZ (volume_pos s) hξ.le hξ1 hamp0 hreserve le_rfl hNpow bin (column l)
  have ha (l:Label):0≤amplitude l:=by
    have he0:0≤extra l:=mul_nonneg
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
      (div_nonneg (hr0 l) hel.le)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) he0) (sq_nonneg _)
  -- the family bound on the residual
  have hnorm:=(hz Jset).2 hZ (fun i:{i // i∉Jset}=>θ i.val) (fun i=>w i.val) (fun i=>v i.val) t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hwv hwmv hadmv hy₂ hl₁ hl₂
    C (fun l=>(column l).2.1.val) hseed τ Kmain Tsec hK hCne hCcap hchar hT0 hradiusT
    alloc ht amplitude χ₀ ha
  -- the first-key price, with two parents
  have hprice:=hp.2 s₀ s 1 1 1 1 R₀ 1 (fun _=>1) W K n b ξ reserve poolLoss
    ((n.L:ℝ)*width) Amix a κ amp hgate hN (by change (1:ℝ)≤1;exact le_rfl) (by simp) (by simp)
    (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
    hrad.2.1 (fun x hx=>(p.support 0 hx).1) (fun x hx=>(p.support 1 hx).1)
    hlog hshift hamp (by linarith [herr.2]) hZ reflected bin
  have hsum:=hprice Label column hinj hLive hseedcap alloc τ ht H0 radius P mesh 12 2 depth
    hpool hH0 hr0 hr
  let price:Label→ℝ:=fun l=>(amplitude l/volume s)*(Kmain l/lowerFactor N 1 (1/4))*
    (max 1 (Y₂/((C l).absNorm:ℝ)))^(-(2*(499/1000:ℝ)))*
    volume (f.input l)*(4*frequencyRadius (Tsec l) Z ξ)^(1/6:ℝ)/((column l).2.1.val.absNorm:ℝ)
  have hsum':(∑l,price l)≤Cp*forcedProfileCost s*
      geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
      Z^(-(n.highFee:ℝ)-4*Amix+2*epsCount):=by
    rw [←hY] at hsum
    have hunit:((1:Ideal O).absNorm:ℝ)=1:=by simp
    simp only [hunit,div_one] at hsum
    convert hsum using 1 <;> rfl
  have hside:0≤geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin:=
    (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hsum'':(∑l,price l)≤Cp*Cprofile*
      geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
      Z^(-(n.highFee:ℝ)-4*Amix+2*epsCount):=by
    apply hsum'.trans
    gcongr
  have hterm (l:Label):0≤price l:=by
    have hh:=ha l
    have hv:=volume_pos s
    have hc:=volume_pos (f.input l)
    have hrad0:0≤4*frequencyRadius (Tsec l) Z ξ:=
      mul_nonneg (by norm_num) (mul_nonneg (hT0 l) (Real.rpow_nonneg hZ0.le _))
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (div_nonneg hh hv.le) (div_nonneg (hK l).le hlower.le))
      (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)) hc.le)
      (Real.rpow_nonneg hrad0 _)) (Nat.cast_nonneg _)
  have hone:1≤1+height:=by linarith
  have hpoint(l:Label):
      (amplitude l/volume s)*(Kmain l/lowerFactor N 1 (1/4))*volume (f.input l)*
        (4*frequencyRadius (Tsec l) Z ξ)^(1/6:ℝ)*
        (max 1 (Y₂/((C l).absNorm:ℝ)))^(-2*(499/1000:ℝ))*(1+‖ht l‖)^(degJ Jset)/
        ((column l).2.1.val.absNorm:ℝ)≤price l*(1+height)^degree:=by
    have hpow:(1+‖ht l‖)^(degJ Jset)≤(1+height)^degree:=
      (pow_le_pow_left₀ (by positivity : 0≤1+‖ht l‖) (add_le_add (le_refl (1:ℝ)) (hht l)) _).trans
        (pow_le_pow_right₀ hone (hdegle Jset))
    convert mul_le_mul_of_nonneg_left hpow (hterm l) using 1 <;>
      dsimp only [price] <;> ring
  have hsumheight:=Finset.sum_le_sum (s:=Finset.univ) (fun l _=>hpoint l)
  rw [←Finset.sum_mul] at hsumheight
  have hpc:(p.control (SJ Jset))^2≤(p.control S)^2:=
    pow_le_pow_left₀ (p.control_nonneg _) (profile_control_le_mx p (hSle Jset)) 2
  have hZx:0≤Z^(epsMass+δ+4*εL+2*ε):=Real.rpow_nonneg hZ0.le _
  have htotal:‖∑q,f.phase Q q*(f.block Q q).value Wsecond‖≤
      Ce*(p.control S)^2*Z^(epsMass+δ+4*εL+2*ε)*((Cp*Cprofile*
        geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        Z^(-(n.highFee:ℝ)-4*Amix+2*epsCount))*(1+height)^degree):=by
    apply hnorm.trans
    have hsumH:=hsumheight.trans (mul_le_mul_of_nonneg_right hsum'' (by positivity))
    calc
      _≤CJ Jset*(p.control (SJ Jset))^2*Z^(epsMass+δ+4*εL+2*ε)*
          ((Cp*Cprofile*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
            Z^(-(n.highFee:ℝ)-4*Amix+2*epsCount))*(1+height)^degree):=by
        apply mul_le_mul_of_nonneg_left hsumH
        exact mul_nonneg (mul_nonneg (hCJ Jset).le (sq_nonneg _)) hZx
      _≤_:=by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg hCp.le hprofile.le) hside) (Real.rpow_nonneg hZ0.le _)) (pow_nonneg (by linarith) _))
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hCJle Jset) hpc (sq_nonneg _) hCe.le) hZx
  apply htotal.trans_eq
  rw [show -(n.highFee:ℝ)-4*Amix+2*epsCount+epsMass+δ+4*εL+2*ε=
    (epsMass+δ+4*εL+2*ε)+(-(n.highFee:ℝ)-4*Amix+2*epsCount) by ring,
    Real.rpow_add hZ0 (epsMass+δ+4*εL+2*ε) (-(n.highFee:ℝ)-4*Amix+2*epsCount)]
  ring

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.profile_control_le_mx
#print axioms QRH.Record1252270103Source.ExceptionalPrice.eventually_initial_main_joint_mx
