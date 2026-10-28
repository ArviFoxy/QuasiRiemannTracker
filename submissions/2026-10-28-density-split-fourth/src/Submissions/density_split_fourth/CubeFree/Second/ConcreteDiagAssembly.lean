/- Copyright (c) 2026 Sil. Apache-2.0.
WP-J: the diagonal hypotheses `hdiagL/hdiagR` of `balanced_summed_raw_side_bounds_avg`
(`ConcreteAssemblyAvg`), with an explicit height-uniform `Ed`.

For one allocation `B` and residual ray `ξ`, `diagAvg` is the sum over the residual seeds
`v ∈ Vset` of the three diagonal parts of ONE residual `r_B = restOf … B (J B)` at Gauss scale
`Kc = 16·K·W_B⁴`:
* zero frequency: `‖Kc·Φ̂(0)·sourceSecondZero‖ ≤ Kc·|Φ̂(0)|·C₀·prof(r_B)²·Y_B^{1+ε}/N v`
  (`seed_second_zero`: FP's column divisor bound and the seed divisibility);
* fixed-inducing rows: the inner exceptional ledger `uniform_actual_exceptional_part` at `K`, `W_B`
  (`partEnergy … (16·K·W_B⁴)`), times `V(r_B)·W_B` (`seed_exceptional`), height through
  `heightBase t^(2J) ≤ (1+2π)^{4J}(1+‖t‖)^{2J}`;
* tails: `secondDiscardedEnergy(16·K·W_B⁴) = W_B·localizedDensity(K,W_B)` (`source_discarded`)
  with arbitrary decay `Z^{-saving}` (`seed_tail`).
`diag_avg_uniform` assembles them under `outerAvg`, with `Atot ≤ AtotP` (height-free), into
`outerAvg … diagAvg … ≤ Ed·(1+‖v‖)^{2J}` where `Ed = #B·Σ_B‖w_B‖²·AtotP_B·2^{|J_B|}·M_B·#Ray²·Ξ_B`. -/
import Submissions.density_split_fourth.CubeFree.Second.ConcreteAssemblyAvg
import Submissions.density_split_fourth.CubeFree.Second.ConcreteDiag
import Submissions.density_split_fourth.CubeFree.FP.MixedLocalizedDictionary
import Submissions.density_split_fourth.CubeFree.FP.MixedFirstExceptionalWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.ConcreteDiagAssembly
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentFirstAmplificationChoice CenteredMomentSmoothedWindowEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentChildRows CenteredMomentFirstColumns
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondLocalization CenteredMomentSupportedTailAggregate
open CenteredMomentSourceSecondZeroEnergy EisensteinSchwartzPoisson CenteredMomentSectorLocalization
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open QRH.Record1252270103KernelMass
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalSecondZero MixedFirstLiveSource
open MixedOriginalTail MixedOriginalNormCap MixedOriginalTailPower MixedPoissonLocalization
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedLocalizedDictionary
open QRH.DensitySplitThird.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypeDiagAsm {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-! ### Helpers -/

theorem heightBase_pow_le (J : ℕ) (t : ℝ) :
    heightBase t^(2*J)≤((1+2*Real.pi)^2)^(2*J)*(1+‖t‖)^(2*J) := by
  rw [←mul_pow]
  apply pow_le_pow_left₀ (heightBase_pos t).le
  unfold heightBase
  have hpi := Real.pi_pos
  have ht := norm_nonneg t
  have h : 1+‖t‖+2*Real.pi ≤ (1+2*Real.pi)*(1+‖t‖) := by nlinarith [mul_nonneg hpi.le ht]
  calc (1+‖t‖+2*Real.pi)*(1+2*Real.pi) ≤ ((1+2*Real.pi)*(1+‖t‖))*(1+2*Real.pi) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by ring

/-- The height-free selected Cauchy mass. -/
def AtotP {κ : Type*} [Fintype κ] {a b : ℝ} (s : Source κ a b) (J : Finset κ) : ℝ :=
  ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
    ‖pairCoeff firstPhaseTable χ ξ‖^2 * ‖selAmp s J y‖^2

theorem AtotP_nonneg {κ : Type*} [Fintype κ] {a b : ℝ} (s : Source κ a b) (J : Finset κ) :
    0 ≤ AtotP s J := by unfold AtotP; positivity

theorem Atot_le {κ : Type*} [Fintype κ] {a b : ℝ} (s : Source κ a b) (J : Finset κ)
    (τ : Character) (t : ℝ) : Atot s J τ t ≤ AtotP s J := by
  unfold Atot AtotP
  apply Finset.sum_le_sum; intro y hy
  apply Finset.sum_le_sum; intro χ _
  apply Finset.sum_le_sum; intro ξ _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  have h1 : ‖(if Function.Injective y then (1:ℂ) else 0)‖≤1 := by split_ifs <;> simp
  have h2 : ‖(if IsCoprime (∏ j, y j) s.R then (1:ℂ) else 0)‖≤1 := by split_ifs <;> simp
  have h3 := heightCoeff_norm_le_one τ t (∏ j, y j) (selY_supported s J y hy).1
  calc ‖selScalar s J y τ t‖
      =‖(if Function.Injective y then (1:ℂ) else 0)‖*‖selAmp s J y‖*
        ‖(if IsCoprime (∏ j, y j) s.R then (1:ℂ) else 0)‖*‖heightCoeff τ t (∏ j, y j)‖ := by
        simp only [selScalar, norm_mul]
    _≤1*‖selAmp s J y‖*1*1 := by gcongr
    _=_ := by ring

/-! ### The diagonal part of one residual -/

/-- `Z0 + Zf + Zt` of one residual over a seed set, at Gauss scale `Kc`. -/
def diagR {κ : Type*} [Fintype κ] {a b : ℝ} (r : Source κ a b) (ha : 0 < a) (V : Finset Id)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc Tsec Z ξr H : ℝ) : ℝ :=
  (∑ v ∈ V, ‖((Kc:ℂ) * paperRadialFourier ballProfile 0) *
      sourceSecondZero (sourceColumns r) (sourceCoefficient r ha v) ψ t‖) +
  (∑ v ∈ V, ‖partEnergy true ψ χ₀ Q m t (sourceColumns r)
      (sourceCoefficient r ha v) ballProfile Kc Tsec Z ξr H‖) +
  (∑ v ∈ V, ‖secondDiscardedEnergy ψ t (sourceColumns r)
      (sourceCoefficient r ha v) ballProfile Kc Tsec Z ξr‖)

theorem diagAvg_eq {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Tsec Z ξr : ℝ)
    (W : actualAllocations (tuplePools s) G → ℝ)
    (B : actualAllocations (tuplePools s) G) (ξ : RayCharacter) :
    diagAvg s ha hb cover G J Us τ χ₀ Q m t K Tsec Z ξr W B ξ =
      diagR (restOf s hb cover G B (J B)) ha
        (Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (J B) Us)
        (childCharacter τ ξ) χ₀ Q m t (16 * K * W B^4) Tsec Z ξr
        (sourceNormCap (restOf s hb cover G B (J B)).P b (restOf s hb cover G B (J B)).T
          (restOf s hb cover G B (J B)).d) := rfl

theorem diagR_le {κ : Type*} [Fintype κ] {a b : ℝ} (r : Source κ a b) (ha : 0 < a) (V : Finset Id)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc Tsec Z ξr H : ℝ) (hKc : 0 ≤ Kc)
    (z e d : Id → ℝ)
    (hz : ∀ v ∈ V, ‖sourceSecondZero (sourceColumns r) (sourceCoefficient r ha v) ψ t‖ ≤ z v)
    (he : ∀ v ∈ V, ‖partEnergy true ψ χ₀ Q m t (sourceColumns r)
      (sourceCoefficient r ha v) ballProfile Kc Tsec Z ξr H‖ ≤ e v)
    (hd : ∀ v ∈ V, ‖secondDiscardedEnergy ψ t (sourceColumns r)
      (sourceCoefficient r ha v) ballProfile Kc Tsec Z ξr‖ ≤ d v) :
    diagR r ha V ψ χ₀ Q m t Kc Tsec Z ξr H ≤
      ∑ v ∈ V, (Kc*‖paperRadialFourier ballProfile 0‖*z v + e v + d v) := by
  unfold diagR
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  gcongr with v hv v hv v hv
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hKc]
    exact mul_le_mul_of_nonneg_left (hz v hv) (by positivity)
  · exact he v hv
  · exact hd v hv

/-! ### Per-seed bounds -/

/-- Zero frequency of one seed. -/
theorem seed_second_zero (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀r : Source ι a b,
      Fintype.card ι≤N→∀ha : 0<a,∀seed : Id,seed≠0→∀(τ : Character)(t Y : ℝ),1≤Y→
      sourceNormCap r.P b r.T r.d≤Y→
      ‖sourceSecondZero (sourceColumns r) (sourceCoefficient r ha seed) τ t‖≤
        C*(profileCap r)^2*Y^(1+ε)/(seed.absNorm:ℝ) := by
  obtain ⟨C0,hC0,hbound⟩ := original_column_bound N (ε/2) (half_pos hε)
  refine ⟨128*C0^2,by positivity,?_⟩
  intro ι instι a b r hcard ha seed hseed τ t Y hY hcap
  have hY0 : 0<Y := zero_lt_one.trans_le hY
  have hsize (I : Id) (_ : I∈supportedColumns (sourceColumns r))
      (hi : sourceCoefficient r ha seed I≠0) : (I.absNorm:ℝ)≤Y :=
    (original_coefficient_cap r ha seed I hi).2.trans hcap
  have hcoeff (I : Id) (hI : I∈supportedColumns (sourceColumns r))
      (hi : sourceCoefficient r ha seed I≠0) :
      ‖sourceCoefficient r ha seed I‖≤C0*profileCap r*Y^(ε/2) :=
    hbound ι a b r hcard ha seed I Y (original_coefficient_cap r ha seed I hi).1 hY
      (hsize I hI hi)
  have hh := sourceSecondZero_divisor_bound (sourceColumns r) (sourceCoefficient r ha seed)
    τ t (C0*profileCap r*Y^(ε/2)) Y
    (by have := profileCap_nonneg r;positivity) hY0.le seed hseed hcoeff
    (fun I _ hi=>source_coefficient_seed r ha seed I hi) hsize
  have hp : (Y^(ε/2))^2*Y=Y^(1+ε) := by
    rw [←Real.rpow_mul_natCast hY0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ)=ε by ring,Real.rpow_add hY0,Real.rpow_one]
    ring
  apply hh.trans_eq
  calc
    _=(128*C0^2)*(profileCap r)^2*((Y^(ε/2))^2*Y)/(seed.absNorm:ℝ) := by ring
    _=_ := by rw [hp]

/-- Tails of one seed at Gauss scale `16·K·W⁴`: arbitrary decay. -/
theorem seed_tail (B ξ saving : ℝ) (hB : 0≤B) (hξ : 0<ξ) :
    ∃(control : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀r : Source ι a b,∀ha : 0<a,0≤b→
      ∀(seed : Id)(η : Character)(t K W X Tsec : ℝ),0<K→0<W→0<X→
      poolCap r≤Z^B→sourceNormCap r.P b r.T r.d≤X→
      X≤Z^B→K≤Z^B→W≤Z^B→W⁻¹≤Z^B→Tsec≤Z^B→X^2/(16*K*W^4)≤Tsec→
      ‖secondDiscardedEnergy η t (sourceColumns r) (sourceCoefficient r ha seed) ballProfile
        (16*K*W^4) Tsec Z ξ‖≤
      W*(C*(profileCap r)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)) := by
  obtain ⟨control,C,hC,hZ⟩ := original_tail_arbitrary_saving.{u} B ξ saving hB hξ
  refine ⟨control,C,hC,?_⟩
  filter_upwards [hZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι instι a b r ha hb seed η t K W X Tsec hK hW hX hpool hcap hXc hKc hWc hWic hTc hscale
  have h := hZ.2 ι a b r ha hb seed η t K W X Tsec hK hW hX hpool hcap hXc hKc hWc hWic hTc hscale
  rw [source_discarded η t (sourceColumns r) (sourceCoefficient r ha seed) K W Tsec Z ξ hW,
    norm_div, Complex.norm_real, Real.norm_of_nonneg hW.le] at h
  have := (div_le_iff₀ hW).mp h
  linarith [mul_comm W (C*(profileCap r)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*
    Z^(-saving))]

/-! ### The uniform diagonal bound -/

/-- The per-allocation diagonal bound `Ξ_B` (height-free). -/
def xiB {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (K Lref : ℝ) (W Y : actualAllocations (tuplePools s) G → ℝ) (J : ℕ)
    (control controlT : Finset (ℕ×ℕ)) (Q : Id)
    (Z ε α Bnorm δ εsum saving C0 Ckernel A Csum Ct : ℝ)
    (B : actualAllocations (tuplePools s) G) : ℝ :=
  ∑ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us,
    (16*K*W B^4*‖paperRadialFourier ballProfile 0‖*
        (C0*(profileCap (restOf s hb cover G B (JB B)))^2*(Y B)^(1+ε)/(w.absNorm:ℝ)) +
      sourceVolume (restOf s hb cover G B (JB B))*W B*
        ((Ckernel*A*((1+2*Real.pi)^2)^(2*J)*(windowMoment J)^2)*
          savedBudget (restOf s hb cover G B (JB B)) J control Q Z ε K (W B)*
          refLoss (restOf s hb cover G B (JB B)) Lref α*Z^(2*Bnorm*δ)*
          (Csum*Z^εsum/(w.absNorm:ℝ))) +
      W B*(Ct*(profileCap (restOf s hb cover G B (JB B)))^2*
        controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)))

theorem diagR_nonneg {κ : Type*} [Fintype κ] {a b : ℝ} (r : Source κ a b) (ha : 0 < a)
    (V : Finset Id) (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t Kc Tsec Z ξr H : ℝ) : 0 ≤ diagR r ha V ψ χ₀ Q m t Kc Tsec Z ξr H := by
  unfold diagR; positivity

/-- **`hdiag` with an explicit height-uniform `Ed`.** All constants (degree, seminorm set, kernel,
exceptional, summation, zero and tail constants) are fixed before `Z` and before the source,
the allocations, the selected blocks, the widths and the multiplicities; the remaining
hypotheses are the structural caps of each residual `r_B` (as in FP's applications). -/
theorem diag_avg_uniform (N : ℕ)
    (α Bcap a b ε δ Bnorm Lrad Cr εsum Btl ξr saving : ℝ)
    (hα0 : 0≤α) (hα23 : α<2/3) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1)
    (hBnorm : 0≤Bnorm) (hLrad : 0≤Lrad) (hCr : 0<Cr) (hεsum : 0<εsum)
    (hBtl : 0≤Btl) (hξr : 0<ξr) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃A Csum C0 Ct : ℝ,∃controlT : Finset (ℕ×ℕ),0<A ∧ 0<Csum ∧ 0<C0 ∧ 0<Ct ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,∀cover : OriginalEnclosure s,∀G : Id,
      ∀JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val),
      ∀(Us : Finset Id)(τ : Character)(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(K Tsec Lref : ℝ)(W M Y : actualAllocations (tuplePools s) G → ℝ),
      0<K → 0≤Tsec → 0<Lref → Lref≤s.L →
      frequencyRadius Tsec Z ξr≤Cr*Z^Lrad → Tsec≤Z^Btl → K≤Z^Btl →
      (∀B, 0<W B ∧ W B≤Z^Btl ∧ (W B)⁻¹≤Z^Btl ∧ 0≤M B ∧ 1≤Y B ∧ Y B≤Z^Btl) →
      (∀B, Fintype.card (Rest (JB B))≤N ∧
        ((restOf s hb cover G B (JB B)).Fhole.absNorm:ℝ)≤Z^Bcap ∧
        (∏i,2*(restOf s hb cover G B (JB B)).P i)≤Z^Bcap ∧
        poolCap (restOf s hb cover G B (JB B))≤Z^Bnorm ∧
        poolCap (restOf s hb cover G B (JB B))≤Z^Btl ∧
        sourceNormCap (restOf s hb cover G B (JB B)).P b (restOf s hb cover G B (JB B)).T
          (restOf s hb cover G B (JB B)).d≤Z^Bnorm ∧
        sourceNormCap (restOf s hb cover G B (JB B)).P b (restOf s hb cover G B (JB B)).T
          (restOf s hb cover G B (JB B)).d≤Y B ∧
        (Y B)^2/(16*K*W B^4)≤Tsec ∧
        ∀ξ : RayCharacter, familyConductorBudget (restOf s hb cover G B (JB B))
          (childCharacter τ ξ) (frequencyRadius Tsec Z ξr)≤Z^Bcap) →
      ∀v : ℝ,
      outerAvg s hb cover G JB τ v M (diagAvg s ha hb cover G JB Us τ χ₀ Q m v K Tsec Z ξr W)≤
        (((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
          ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
            (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
              ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
                xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α Bnorm δ εsum saving
                  C0 Ckernel A Csum Ct B)))*
          (1+‖v‖)^(2*J) := by
  obtain ⟨J,control,h00,hk⟩ := uniform_actual_exceptional_part.{u} N α Bcap a b ε δ Bnorm Lrad Cr
    εsum hα0 hα23 hBcap ha hb hε hδ hgap hBnorm hLrad hCr hεsum
  obtain ⟨Ckernel,hCk,hQ⟩ := hk ballProfile
  refine ⟨J,control,Ckernel,hCk,?_⟩
  intro Q hQ0 hQt hQ72
  obtain ⟨A,Csum,hA,hCsum,hZe⟩ := hQ Q hQ0 hQt hQ72
  obtain ⟨C0,hC0,hzero⟩ := seed_second_zero.{u} N ε hε
  obtain ⟨controlT,Ct,hCt,hZt⟩ := seed_tail.{u} Btl ξr saving hBtl hξr
  refine ⟨A,Csum,C0,Ct,controlT,hA,hCsum,hC0,hCt,?_⟩
  filter_upwards [hZe,hZt] with Z hZe hZt
  refine ⟨hZe.1,?_⟩
  intro ι instι s cover G JB Us τ χ₀ m hm hml hm2 K Tsec Lref W M Y hK hT hLref0 hLref hrad hTc hKc
    hWMY hcaps v
  have hpoint : ∀ B ξ, diagAvg s ha hb cover G JB Us τ χ₀ Q m v K Tsec Z ξr W B ξ ≤
      (1+‖v‖)^(2*J) *
        xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α Bnorm δ εsum saving
          C0 Ckernel A Csum Ct B := by
    intro B ξ
    obtain ⟨hW0, hWc, hWic, _, hY1, hYc⟩ := hWMY B
    obtain ⟨hcard, hF, hP, hpool, hpoolT, hH, hYcap, hscale, hcond⟩ := hcaps B
    have hsq : ∀ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us,
        Squarefree w := Vset_squarefree _ _ _ Us
    have hne : ∀ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us,
        w ≠ 0 := fun w hw h => not_squarefree_zero (h ▸ hsq w hw)
    rw [diagAvg_eq]
    have hKc0 : 0 ≤ 16*K*W B^4 := by positivity
    refine (diagR_le (restOf s hb cover G B (JB B)) ha
      (Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us)
      (childCharacter τ ξ) χ₀ Q m v (16*K*W B^4) Tsec Z ξr _ hKc0
      (fun w => C0*(profileCap (restOf s hb cover G B (JB B)))^2*(Y B)^(1+ε)/(w.absNorm:ℝ))
      (fun w => (1+‖v‖)^(2*J)*(sourceVolume (restOf s hb cover G B (JB B))*W B*
              ((Ckernel*A*((1+2*Real.pi)^2)^(2*J)*(windowMoment J)^2)*
                savedBudget (restOf s hb cover G B (JB B)) J control Q Z ε K (W B)*
                refLoss (restOf s hb cover G B (JB B)) Lref α*Z^(2*Bnorm*δ)*
                (Csum*Z^εsum/(w.absNorm:ℝ)))))
      (fun _ => W B*(Ct*(profileCap (restOf s hb cover G B (JB B)))^2*
              controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)))
      ?_ ?_ ?_).trans ?_
    · intro w hw
      exact hzero (Rest (JB B)) a b (restOf s hb cover G B (JB B)) hcard ha w (hne w hw)
        (childCharacter τ ξ) v (Y B) hY1 hYcap
    · intro w hw
      have h := hZe.2 (Rest (JB B)) (restOf s hb cover G B (JB B))
        (ConcreteDiag.rest_enclosure _ _ _ (MixedFirstExceptionalWindow.live_enclosure _)) hcard hF hP hpool
        (childCharacter τ ξ) χ₀ m hm hml hm2 w (hsq w hw) (hne w hw)
        v K (W B) Tsec ξr _ hK hW0 hT hH hrad (hcond ξ) Lref hLref0 hLref
      have hV := sourceVolume_pos (restOf s hb cover G B (JB B))
      have hb2 := heightBase_pow_le J v
      have hrest : 0 ≤ savedBudget (restOf s hb cover G B (JB B)) J control Q Z ε K (W B)*
          refLoss (restOf s hb cover G B (JB B)) Lref α*Z^(2*Bnorm*δ)*
          (Csum*Z^εsum/(w.absNorm:ℝ)) := by
        have := savedBudget_nonneg (restOf s hb cover G B (JB B)) J control Q Z ε K (W B) hK hW0
        have := refLoss_nonneg (restOf s hb cover G B (JB B)) Lref α hLref0.le
        have := (zero_lt_one.trans hZe.1).le
        positivity
      have hwm : 0 ≤ Ckernel*A*(windowMoment J)^2 := by positivity
      rw [div_div, div_le_iff₀ (mul_pos hV hW0)] at h
      calc _ ≤ (Ckernel*A*heightBase v^(2*J)*(windowMoment J)^2)*
              savedBudget (restOf s hb cover G B (JB B)) J control Q Z ε K (W B)*
              refLoss (restOf s hb cover G B (JB B)) Lref α*Z^(2*Bnorm*δ)*
              (Csum*Z^εsum/(w.absNorm:ℝ))*
              (sourceVolume (restOf s hb cover G B (JB B))*W B) := h
        _ = ((Ckernel*A*(windowMoment J)^2)*(savedBudget (restOf s hb cover G B (JB B)) J control
              Q Z ε K (W B)*refLoss (restOf s hb cover G B (JB B)) Lref α*Z^(2*Bnorm*δ)*
              (Csum*Z^εsum/(w.absNorm:ℝ)))*
              (sourceVolume (restOf s hb cover G B (JB B))*W B))*heightBase v^(2*J) := by ring
        _ ≤ ((Ckernel*A*(windowMoment J)^2)*(savedBudget (restOf s hb cover G B (JB B)) J control
              Q Z ε K (W B)*refLoss (restOf s hb cover G B (JB B)) Lref α*Z^(2*Bnorm*δ)*
              (Csum*Z^εsum/(w.absNorm:ℝ)))*
              (sourceVolume (restOf s hb cover G B (JB B))*W B))*
              (((1+2*Real.pi)^2)^(2*J)*(1+‖v‖)^(2*J)) := by
            apply mul_le_mul_of_nonneg_left hb2
            have := hV.le; have := hW0.le; positivity
        _ = _ := by ring
    · intro w _
      exact hZt.2 (Rest (JB B)) a b (restOf s hb cover G B (JB B)) ha hb w (childCharacter τ ξ) v K
        (W B) (Y B) Tsec hK hW0 (zero_lt_one.trans_le hY1) hpoolT hYcap hYc hKc hWc hWic hTc hscale
    · unfold xiB
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro w _
      have hp1 : 1≤(1+‖v‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg v])
      have hzt : 0 ≤ W B*(Ct*(profileCap (restOf s hb cover G B (JB B)))^2*
          controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)) := by
        have := hW0.le
        have := (zero_lt_one.trans hZe.1).le
        have : 0 ≤ controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile := apply_nonneg _ _
        positivity
      have hzz : 0 ≤ 16*K*W B^4*‖paperRadialFourier ballProfile 0‖*
          (C0*(profileCap (restOf s hb cover G B (JB B)))^2*(Y B)^(1+ε)/(w.absNorm:ℝ)) := by
        have := (zero_lt_one.trans_le hY1).le
        have := profileCap_nonneg (restOf s hb cover G B (JB B))
        positivity
      nlinarith
  have hsum : ∀ B, (∑ _χ : RayCharacter, ∑ ξ : RayCharacter,
      diagAvg s ha hb cover G JB Us τ χ₀ Q m v K Tsec Z ξr W B ξ) ≤
      (Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
        ((1+‖v‖)^(2*J) * xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α Bnorm δ
          εsum saving C0 Ckernel A Csum Ct B) := by
    intro B
    calc _ ≤ ∑ _χ : RayCharacter, ∑ _ξ : RayCharacter, (1+‖v‖)^(2*J) *
          xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α Bnorm δ εsum saving
            C0 Ckernel A Csum Ct B :=
        Finset.sum_le_sum fun χ _ => Finset.sum_le_sum fun ξ _ => hpoint B ξ
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hnn : ∀ B, 0 ≤ ∑ _χ : RayCharacter, ∑ ξ : RayCharacter,
      diagAvg s ha hb cover G JB Us τ χ₀ Q m v K Tsec Z ξr W B ξ := by
    intro B
    apply Finset.sum_nonneg; intro χ _
    apply Finset.sum_nonneg; intro ξ _
    rw [diagAvg_eq]; exact diagR_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _
  unfold outerAvg
  calc _ ≤ ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
          ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
            (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
              ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
                ((1+‖v‖)^(2*J) * xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α
                  Bnorm δ εsum saving C0 Ckernel A Csum Ct B))) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum; intro B _
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hM0 := (hWMY B).2.2.2.1
        have h2M : 0 ≤ (2:ℝ)^(Fintype.card (JB B)) * M B := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_right (Atot_le _ _ _ _) h2M) (hsum B) (hnn B)
          (mul_nonneg (AtotP_nonneg _ _) h2M)
    _ = _ := by
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl; intro B _
        ring

end
end QRH.DensitySplitThird.CubeFree.Second.ConcreteDiagAssembly
