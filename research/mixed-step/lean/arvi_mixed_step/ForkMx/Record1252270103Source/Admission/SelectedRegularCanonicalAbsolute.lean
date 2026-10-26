/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Canonical initial data specialize the actual allocated-family absolute envelope. -/
/- Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F5): fork of Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute
(Hailey Collet, Apache-2.0); changes: two parents and two amplitudes.
- The anchor is `Initial.anchor_mx i₀ i`. The first layer `i₀` carries the face hypotheses of
  `eventually_initial_caps` on `globalFace B₀ lam₀ cap₀`; the second layer `i` carries them on
  `globalFace B lam cap`; `i₀.p = i.p`.
- The first geometry (H0, the radius `literalFirstRadius … (volume a.s₀) …` with the ball factor at the
  pool width `poolAmp`, the projector cap) is Collet's `eventually_initial_first_geometry` on `i₀`.
- The MAIN radius `Hmain` of the family is read at the second-layer volume `volume a.s` with the node
  amplitude `amp`. Its caps `Z^(-32) ≤ Hmain ≤ Z^32` are `mixed_main_radius_bounds_mx` below: the upper
  cap is Collet's `actual_first_radius_upper` with a free volume `V ≤ Z`; the lower cap compares the
  nominal logarithm at `V ≥ 1` with the one at `volume s₀ ≤ Z` (`nominalLog_volume_mx`, loss ≤ 2).
  The absolute envelope is therefore called with `Dlo = 32` instead of Collet's `0`; its exponent
  `exponent 2 4 32 4 4 = 75` does not involve `Dlo`, so the conclusion is Collet's `Z^75`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularCanonicalAbsoluteData
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularLowPointData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open CenteredMomentEnergyBands CenteredMomentCommonProfile RayFourExpansion CenteredMomentCommonAllocationSum
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceMass CenteredMomentLogDyadic
open Record12518109Natural.MarkedPlain Record1252270103Finite
open Cycle61Moment Cycle61InitialMass Record1252270103Second
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open High.GlobalPhysical SecondSectorDatum SelectedRegularSourceData SelectedRegularLowPoint
local notation "O"=>HeckeFamily.O
local instance canonicalAbsoluteDecEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance canonicalAbsoluteFinite_mx (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

section MixedRadius
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCompleteCommon
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstCanonicalFamily CenteredMomentLogDyadic
open CenteredMomentSourceInputFirstTailUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile Cycle61Moment Cycle61InitialMass
open High.CoupledFirst Admission.FirstFamily ExceptionalPrice
local notation "source"=>High.CoupledFirst.geometryFirstSource

/-- Collet's `actual_first_radius_upper` with a free volume `V` (here: the second-layer volume) in
place of `volume s`; the label and its caps are those of `s` (here: the first layer). -/
theorem actual_first_radius_upper_mx {α:Type*}[Fintype α]
    (s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)(Z ξ amp reserve V:ℝ)(hZ:1<Z)
    (hs:Squarefree seed)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (hsource:sourceRadius s≤Z^(2:ℝ))(hV0:0<V)(hV:V≤Z)
    (hamp:amp≤1)(hreserve:reserve≤1)(hfreq:frequencyLoss Z 32 ξ≤1)
    (reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (source s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin)):
    literalFirstRadius reflected Z V Z ξ reserve
      (firstLabel s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j)+6*amp≤32 := by
  let l:=firstLabel s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j
  have hl:=label_supported s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j
  have hn:=label_common_bounds s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin hs hz₁ hz₂ j
  have logbound (I:Ideal O)(hI:I≠0)(hcap:(I.absNorm:ℝ)≤Z^(2:ℝ)):
      0≤Real.logb Z (I.absNorm:ℝ) ∧ Real.logb Z (I.absNorm:ℝ)≤2 := by
    have hnorm:0<(I.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos I hI
    have hnorm1:(1:ℝ)≤I.absNorm:=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have hh:=Real.logb_le_logb_of_le hZ hnorm hcap
    rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
    exact ⟨Real.logb_nonneg hZ hnorm1,hh⟩
  have hc:=logbound l.1.1 hl.1.1 (hn.2.2.1.trans hsource)
  have hd:=logbound l.1.2 hl.2.1.1 (hn.2.2.2.trans hsource)
  have hdiff:max (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) 0≤2 := by
    cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    all_goals exact max_le (by linarith) (by norm_num)
  let E:=Ideal.span {primeSubsetGenerator (fun p:CommonIndex l.1.1 l.1.2=>p.val) l.2.val}
  have hE:E≠0:=(subsetGenerator_supported l.1.1 l.1.2 hl.1 l.2.val).1
  have hT:=firstNominalScale_pos l.1.1 l.1.2 E hE Z V (zero_lt_one.trans hZ) hV0
  have htcap:firstNominalScale l.1.1 l.1.2 E Z V≤Z:=by
    have hh:=first_nominal_scale_le l.1.1 l.1.2 l.2.val Z V (zero_lt_one.trans hZ)
    have hh':firstNominalScale l.1.1 l.1.2 E Z V≤V^2/Z:=by
      simpa only [E,primeSubsetGenerator,span_idealGenerator] using hh
    apply hh'.trans
    apply (div_le_iff₀ (zero_lt_one.trans hZ)).mpr
    simpa only [pow_two] using pow_le_pow_left₀ hV0.le hV 2
  have hlog:nominalLog l.1.1 l.1.2 E Z V Z≤1:=by
    have hh:=Real.logb_le_logb_of_le hZ hT htcap
    simpa only [nominalLog,Real.logb_self_eq_one hZ] using hh
  change literalFirstRadius reflected Z V Z ξ reserve l+6*amp≤32
  dsimp only [literalFirstRadius]
  change nominalLog l.1.1 l.1.2 E Z V Z+_+_+_+6*amp≤32
  linarith only [hlog,hdiff,hfreq,hreserve,hamp]

/-- The nominal logarithm moves by at most `2` when the volume `V₀ ≤ Z` is replaced by `V ≥ 1`. -/
theorem nominalLog_volume_mx (I J E:Ideal O)(hE:E≠0)(K V₀ V Z:ℝ)(hK:0<K)(hZ:1<Z)
    (hV₀:0<V₀)(hV₀Z:V₀≤Z)(hV:1≤V):
    nominalLog I J E K V₀ Z-2≤nominalLog I J E K V Z := by
  have hc:=firstNominalScale_pos I J E hE K 1 hK one_pos
  have hform:∀X:ℝ,firstNominalScale I J E K X=firstNominalScale I J E K 1*X^2:=by
    intro X;unfold firstNominalScale;ring
  have hlogX:∀X:ℝ,0<X→nominalLog I J E K X Z=
      Real.logb Z (firstNominalScale I J E K 1)+2*Real.logb Z X:=by
    intro X hX
    unfold nominalLog
    rw [hform X,Real.logb_mul hc.ne' (pow_ne_zero 2 hX.ne'),Real.logb_pow]
    push_cast;ring
  have hl₀:Real.logb Z V₀≤1:=by
    have hh:=Real.logb_le_logb_of_le hZ hV₀ hV₀Z
    rwa [Real.logb_self_eq_one hZ] at hh
  have hl₁:0≤Real.logb Z V:=Real.logb_nonneg hZ hV
  rw [hlogX V₀ hV₀,hlogX V (zero_lt_one.trans_le hV)]
  linarith

/-- The MAIN radius of a first-layer label read at a second-layer volume `V ∈ [1,Z]`: Collet's caps
`Z^(-32) ≤ Hmain ≤ Z^32`, with the label caps from `s₀` (`sourceRadius s₀ ≤ Z^2`, `volume s₀ ≤ Z`). -/
theorem mixed_main_radius_bounds_mx {α:Type*}[Fintype α]
    (s₀:Input α)(modifier₀:Tuple α→ℂ)(R seed:Ideal O)(Z ξ amp reserve V:ℝ)(hZ:1<Z)
    (hs:Squarefree seed)(hz₁:s₀.W₁ 0=0)(hz₂:s₀.W₂ 0=0)
    (hsource:sourceRadius s₀≤Z^(2:ℝ))(hV₀:volume s₀≤Z)(hV1:1≤V)(hV:V≤Z)
    (hamp0:0≤amp)(hamp:amp≤1)(hreserve0:0≤reserve)(hreserve:reserve≤1)(hfreq:frequencyLoss Z 32 ξ≤1)
    (reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (source s₀ modifier₀ R seed Z Z ξ (zero_lt_one.trans hZ) bin)):
    Z^(-(32:ℝ))≤firstMainRadius reflected Z V Z ξ (3*amp) reserve
        (firstLabel s₀ modifier₀ R seed Z Z ξ (zero_lt_one.trans hZ) bin j) ∧
      firstMainRadius reflected Z V Z ξ (3*amp) reserve
        (firstLabel s₀ modifier₀ R seed Z Z ξ (zero_lt_one.trans hZ) bin j)≤Z^(32:ℝ) := by
  let l:=firstLabel s₀ modifier₀ R seed Z Z ξ (zero_lt_one.trans hZ) bin j
  have hl:=label_supported s₀ modifier₀ R seed Z Z ξ (zero_lt_one.trans hZ) bin j
  have hE:=(subsetGenerator_supported l.1.1 l.1.2 hl.1 l.2.val).1
  have h₀:0≤literalFirstRadius reflected Z (volume s₀) Z ξ reserve l:=
    (actual_first_radius_envelope s₀ modifier₀ R seed Z Z ξ reserve
      (zero_lt_one.trans hZ) hZ hreserve0 reflected bin j).1
  have hrel:=nominalLog_volume_mx l.1.1 l.1.2 _ hE Z (volume s₀) V Z (zero_lt_one.trans hZ) hZ
    (volume_pos s₀) hV₀ hV1
  have hup:literalFirstRadius reflected Z V Z ξ reserve l+6*amp≤32:=
    actual_first_radius_upper_mx s₀ modifier₀ R seed Z ξ amp reserve V hZ hs hz₁ hz₂ hsource
      (zero_lt_one.trans_le hV1) hV hamp hreserve hfreq reflected bin j
  have hlo:-(32:ℝ)≤literalFirstRadius reflected Z V Z ξ reserve l+6*amp:=by
    unfold literalFirstRadius at h₀ ⊢
    linarith
  have hm:=literal_first_main_radius reflected Z V Z ξ amp reserve l
  show Z^(-(32:ℝ))≤firstMainRadius reflected Z V Z ξ (3*amp) reserve l ∧
    firstMainRadius reflected Z V Z ξ (3*amp) reserve l≤Z^(32:ℝ)
  rw [←hm]
  exact ⟨Real.rpow_le_rpow_of_exponent_le hZ.le hlo,Real.rpow_le_rpow_of_exponent_le hZ.le hup⟩

end MixedRadius

theorem eventually_canonical_absolute_mx (N:ℕ)(B₀ lam₀ cap₀ B lam cap ξ amp poolAmp reserve:ℝ)
    (hB₀:B₀≤1)(hlam₀:1≤lam₀)(hcap₀:cap₀≤1)(hB:B≤1)(hlam:1≤lam)(hcap:cap≤1)(hξ:0<ξ)(hξ1:ξ≤1)
    (hamp:0≤amp)(hamp1:amp≤1)(hpoolAmp:0<poolAmp)(hpoolAmp1:poolAmp≤1)(hreserve:0≤reserve)(hreserve1:reserve≤1)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hsW:Function.support W⊆Set.Icc (1:ℝ) 2):
    ∃Ca:ℝ,0<Ca ∧ ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀{α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label](rayM:Ideal O)[NeZero rayM]
      (H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H)
      (i₀:Initial (α:=α₀) rayM H Z)(i:Initial (α:=α) rayM H Z)(η η₀:Character)(R₀:Ideal O)(hR₀:R₀≠0)
      (bin:ℤ×(Fin 5→ℤ))(reflected:Bool)(Q:Ideal O),
      Fintype.card α₀≤N→Fintype.card α≤N→i₀.p=i.p→
      (∀ j : α₀, (0:ℝ) ≤ i₀.w j)→
      (globalFace B₀ lam₀ cap₀).Admissible (length Z i₀.X₁) (length Z i₀.X₂) (∑j,i₀.w j) 1→
      (1:ℝ) ≤ i₀.Y₂ → i₀.Y₂ ≤ i₀.X₁ → i₀.Y₂ ≤ i₀.X₂ →
      (∀ j : α, (0:ℝ) ≤ i.w j)→
      (globalFace B lam cap).Admissible (length Z i.X₁) (length Z i.X₂) (∑j,i.w j) 1→
      (1:ℝ) ≤ i.Y₂ → i.Y₂ ≤ i.X₁ → i.Y₂ ≤ i.X₂ →
    let a:=Initial.anchor_mx i₀ i hH W hW hsW hZ η η₀ R₀ 1 hR₀ (by simp) 1 1 1 1 (fun _=>1)
      ξ reserve bin reflected Q
    ∀(column:Label→a.Column)
      (hLive:∀l,column l∈firstLiveColumns
        (High.CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin)
        (fun _=>logAnnulus))
      (alloc:∀l,actualAllocations a.s.pools (FirstFamily.columnIdeal a.reflected a.s₀ a.modifier₀ a.R a.seed
        (Z^a.D) Z a.ξ a.hK a.bin (column l)))
      (P:Finset (Ideal O))(ht:ℝ)(χ₀:Label→RayCharacter),
      Function.Injective (fun l=>(a.label (column l),(column l).2.1.val))→
      P.Nonempty→∀(mesh loss BD:ℝ)(depth:ℕ),
      Pool.FixedCellPoolData P Z poolAmp (poolAmp/2) mesh loss BD 4 depth→
    let F:=allocatedRegularFamily_mx a column hLive alloc P amp ht N χ₀
    let H0:=fun l=>(High.CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (column l).1).H0
    let radius:=fun l=>ExceptionalPrice.literalFirstRadius reflected Z (volume a.s₀) Z ξ reserve (a.label (column l))
    ∀Wa:𝓢(ℝ,ℂ),
      secondAbsoluteBudget F.datum (fun q=>F.childModifier q.1)
        (regularFamilyWeight_mx F Wa (fun _=>P) (fun _=>poolAmp) H0 radius (poolAmp/2))≤
        Ca*(i.p.control {(0,0)})^2*Z^(75:ℝ) := by
  obtain ⟨Ca,hCa,habs⟩:=full_family_absolute_mx N
    (initialSlotBound W hW hsW) 2 (1/4) (9/4) (poolAmp/2) 32 2 4 32 32 4 4
    (initialSlotBound_ge_one W hW hsW) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Ca,hCa,?_⟩
  filter_upwards [habs,InitialTruncated.eventually_initial_caps N B₀ lam₀ cap₀ hB₀ hlam₀ hcap₀,
    InitialTruncated.eventually_initial_caps N B lam cap hB hlam hcap,
    ExceptionalPrice.eventually_initial_first_geometry N B₀ lam₀ cap₀ ξ poolAmp reserve hB₀ hlam₀ hcap₀
      hξ hξ1 hpoolAmp.le hpoolAmp1 hreserve hreserve1,
    CenteredMomentFirstAmplificationChoice.eventually_frequency_loss 32 ξ (by norm_num) hξ,
    allocated_frequency_mx N] with Z ha hc₀ hc hg hfl hf
  refine ⟨ha.1,?_⟩
  intro hZ α₀ α Label _ _ _ rayM _ H hH i₀ i η η₀ R₀ hR₀ bin reflected Q hN₀ hN hp0 hw₀ hadm₀ hy₀ hyl₀ hyr₀
    hw hadm hy₂ hyl hyr a column hLive alloc P ht χ₀ hinj hP mesh loss BD depth hcell F H0 radius Wa
  have hz:=zero_lt_one.trans hZ
  have caps₀:=hc₀.2 hZ rayM H hH W hW hsW η η₀ R₀ i₀.θ i₀.w i₀.freq i₀.t₀ i₀.p
    i₀.X₁ i₀.X₂ i₀.Y₁ i₀.Y₂ i₀.hX₁ i₀.hX₂ i₀.hY₁ i₀.hY₂ i₀.same hN₀ hw₀ hadm₀ hy₀ hyl₀ hyr₀
  have caps:=hc.2 hZ rayM H hH W hW hsW η η₀ R₀ i.θ i.w i.freq i.t₀ i.p
    i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same hN hw hadm hy₂ hyl hyr
  have geom:=hg.2 hZ rayM H hH W hW hsW η η₀ R₀ i₀.θ i₀.w i₀.freq i₀.t₀ i₀.p
    i₀.X₁ i₀.X₂ i₀.Y₁ i₀.Y₂ i₀.hX₁ i₀.hX₂ i₀.hY₁ i₀.hY₂ i₀.same hN₀ hw₀ hadm₀ hy₀ hyl₀ hyr₀
  have hfreq1:frequencyLoss Z 32 ξ≤1:=hfl.2.2.le.trans hξ1
  have hgeom (l:Label):0<H0 l ∧ 0≤radius l+6*poolAmp ∧ radius l+6*poolAmp≤32 ∧
      ((F.childSeed l).absNorm:ℝ)≤Z^(4:ℝ) ∧ Z^(-(32:ℝ))≤F.Hmain l ∧ F.Hmain l≤Z^(32:ℝ):=by
    have gg:=fun j=>by
      have g:=geom a.modifier₀ reflected bin j
      have m:=mixed_main_radius_bounds_mx a.s₀ a.modifier₀ a.R a.seed Z ξ amp reserve (volume a.s) hZ
        a.seed_sf (initial_plain_zero i₀.p (by norm_num) 0) (initial_plain_zero i₀.p (by norm_num) 1)
        caps₀.2.1 caps₀.2.2.2.1 caps.2.2.1 caps.2.2.2.1 hamp hamp1 hreserve hreserve1 hfreq1 reflected bin j
      exact And.intro g.1 (And.intro g.2.1 (And.intro g.2.2.1
        (And.intro g.2.2.2.2.2.1 (And.intro m.1 m.2))))
    let prop:=(fun (K:ℝ)(hK:0<K)=>∀j:FirstColumnIndex
        (High.CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed K Z ξ hK bin),
      0<(High.CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed K Z ξ hK bin j.1).H0 ∧
      let rad:=ExceptionalPrice.literalFirstRadius reflected Z (volume a.s₀) Z ξ reserve
        (FirstFamily.firstLabel a.s₀ a.modifier₀ a.R a.seed K Z ξ hK bin j)
      0≤rad+6*poolAmp ∧ rad+6*poolAmp≤32 ∧ (j.2.1.val.absNorm:ℝ)≤Z^(4:ℝ) ∧
        Z^(-(32:ℝ))≤firstMainRadius reflected K (volume a.s) Z ξ (3*amp) reserve
          (FirstFamily.firstLabel a.s₀ a.modifier₀ a.R a.seed K Z ξ hK bin j) ∧
        firstMainRadius reflected K (volume a.s) Z ξ (3*amp) reserve
          (FirstFamily.firstLabel a.s₀ a.modifier₀ a.R a.seed K Z ξ hK bin j)≤Z^(32:ℝ))
    have base:prop Z hz:=gg
    have transport (K:ℝ)(hK:0<K)(he:K=Z):prop K hK:=by
      subst K
      exact base
    exact transport (Z^a.D) a.hK (by change Z^(1:ℝ)=Z;exact Real.rpow_one Z) (column l)
  have hVlo:1≤volume F.s:=caps.2.2.1
  have hVhi:volume F.s≤Z^(2:ℝ):=caps.2.2.2.1.trans
    (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num:(1:ℝ)≤2))
  have hV₀lo:1≤volume F.s₀:=caps₀.2.2.1
  have hV₀hi:volume F.s₀≤Z:=caps₀.2.2.2.1
  have hlog:|Real.logb Z (volume F.s₀)|≤2:=by
    rw [abs_of_nonneg (Real.logb_nonneg hZ hV₀lo)]
    exact (Real.logb_le_iff_le_rpow hZ (volume_pos F.s₀)).mpr (hV₀hi.trans
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num:(1:ℝ)≤2)))
  have hfull:=ha.2 a F i.p Wa (fun _=>P) (fun _=>poolAmp) H0 radius hN₀ hN (fun _=>le_rfl)
    (fun _=>by change (1:ℝ)≤2;norm_num)
    (fun _=>by change (2:ℝ)≤2;exact le_rfl)
    (fun j=>by change 1≤Z^(i.w j);exact Real.one_le_rpow hZ.le (hw j)) (by change (0:ℝ)≤9/4;norm_num)
    (by change (0:ℝ)≤9/4;norm_num) (by change (1:ℝ)≤1;exact le_rfl) (by change (1:ℝ)≤1;exact le_rfl)
    (by rw [←hp0];rfl) (by rw [←hp0];rfl) rfl rfl caps₀.2.1 caps.2.1 hVlo hVhi hlog
    (by change (1:Ideal O)≠0;exact one_ne_zero) hinj hLive
    (fun l=>(hgeom l).2.2.2.1) (fun l=>(hgeom l).2.2.2.2.1) (fun l=>(hgeom l).2.2.2.2.2)
    (hf.2 a column hLive alloc P amp ht χ₀ rfl hξ.le hξ1 hreserve hamp)
    (SelectedRegularAbsolute.column_cap_irrel _ _ _ _ caps.2.2.2.2)
    (fun _=>hP) (fun l=>(hgeom l).1) (fun l=>(hgeom l).2.1) (fun l=>(hgeom l).2.2.1)
    (fun l=>(alloc l).val (Sum.inr 0)) (fun l=>(alloc l).val (Sum.inr 1)) (fun _=>1)
    (fun l=>Collision.markedProduct (alloc l).val) (fun _=>poolAmp) (fun _=>mesh) (fun _=>loss) (fun _=>BD)
    (fun _=>depth) (fun _=>hcell) (fun _=>rfl)
  norm_num only [SelectedRegularAbsolute.exponent] at hfull
  exact hfull

end
end QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute.mixed_main_radius_bounds_mx
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute.eventually_canonical_absolute_mx
