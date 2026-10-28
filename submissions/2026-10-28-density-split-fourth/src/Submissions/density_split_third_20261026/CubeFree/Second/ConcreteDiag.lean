/- Copyright (c) 2026 Sil. Apache-2.0.
WP-J (item 4 of the concrete second step): the three non-window parts of the second Poisson
split of the TRANSFERRED residual `restSource s hB1 J` (seed `seedRest u D_y`, character
`childCharacter τ ξ`, after the D⁴ transfer `residual_transfer`), single source, at the
uncompleted Gauss scale `16·K·W⁴` (CF §7: `g = 4u` is the `W⁴`; no positive-part completion).

* `Z0` — second zero frequency: `residual_second_zero` (the FP diagonal for an arbitrary seed),
  and CF's exponent count `cf_second_zero_excess` (`A-1-c+4u ≤ -Δ-(λ₁-1-4a)S+4mesh`).
* `Zf` — fixed-inducing rows (`partEnergy true`): the inner exceptional ledger
  `MixedInnerExceptionalLedger.uniform_actual_exceptional_part` holds for every `Source`, hence
  for `restSource` (`residual_fixed_inducing`, with `rest_enclosure`); `rest_saved_raw` gives its
  raw form with the residual volume `V/∏_{j∈J}P_j`. CF's K₄ ledger (`w = u`, `w_o = 0`, `g = 4u`,
  `ℓ_gain = 0`) is `cf_first_common` (`F₁+(c-d) ≥ c-3u-5δ/6`) and `cf_exceptional_excess` ((7.1)).
* `Zt` — Poisson tails: `MixedOriginalTailPower.original_tail_arbitrary_saving` (any source,
  arbitrary decay `Z^(-saving)`); `rest_poolCap_le`, `rest_profileCap_le` transfer its caps.
All three bounds are uniform in the height `t` (the exceptional one through `heightBase t^(2J)`). -/
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteResidual4
import Submissions.density_split_third_20261026.CubeFree.FP.MixedFirstExceptionalNormalization
import Submissions.density_split_third_20261026.CubeFree.FP.MixedOriginalTailPower
import Submissions.density_split_third_20261026.CubeFree.FP.MixedPoissonLocalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.ConcreteDiag
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion
open QRH.Record1252270103KernelMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentSourceSecondZeroEnergy CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSecondEnergySplit CenteredMomentDescentLedger
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedPrincipalBudget
open MixedOriginalTail MixedOriginalSecondZero MixedOriginalTailPower MixedPoissonLocalization
open MixedPrincipalCentered MixedOriginalNormCap EisensteinSchwartzPoisson
open CenteredMomentFirstAmplificationChoice
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedFirstExceptionalNormalization
open QRH.DensitySplitThird.CubeFree.Second.Concrete (restSource seedRest Rest prod_split_subtype
  seedRest_squarefree)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-! ### The residual source: volume, enclosure, caps -/

/-- The residual keeps `X₁,X₂` and drops the selected marked lengths. -/
theorem rest_volume (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) :
    sourceVolume (restSource s hB1 J)*∏ j ∈ J, s.P j=sourceVolume s := by
  change s.X₁*s.X₂*(∏ j : Rest J, s.P j.val)*∏ j ∈ J, s.P j=s.X₁*s.X₂*∏ i, s.P i
  rw [prod_split_subtype J s.P,←Finset.prod_coe_sort J s.P]
  ring

theorem rest_enclosure (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι)
    (cover : OriginalEnclosure s) : OriginalEnclosure (restSource s hB1 J) := cover

theorem rest_profileCap_le (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) :
    profileCap (restSource s hB1 J)≤profileCap s := by
  change 2*supControl s.W₁*supControl s.W₂*(∏ j : Rest J, s.M j.val)≤
    2*supControl s.W₁*supControl s.W₂*∏ i, s.M i
  have hs1 : 0≤supControl s.W₁ := (norm_nonneg _).trans (norm_le_supControl s.W₁ 0)
  have hs2 : 0≤supControl s.W₂ := (norm_nonneg _).trans (norm_le_supControl s.W₂ 0)
  have h0 : 0≤2*supControl s.W₁*supControl s.W₂ := by positivity
  apply mul_le_mul_of_nonneg_left _ h0
  rw [(Finset.prod_subtype (Jᶜ) (fun i => by simp) s.M).symm]
  apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
  · intro i _
    exact zero_le_one.trans (s.hM i)
  · intro i _ _
    exact s.hM i

theorem rest_poolCap_le (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (hb : 0≤b) :
    poolCap (restSource s hB1 J)≤poolCap s := by
  change (128*b)^2*(s.X₁+s.Y₁)*(s.X₂+s.Y₂)/pairNorm s.d*(∏ j : Rest J, 256*s.P j.val)≤
    (128*b)^2*(s.X₁+s.Y₁)*(s.X₂+s.Y₂)/pairNorm s.d*∏ i, 256*s.P i
  have hL := s.hL
  have hx1 : 0≤s.X₁+s.Y₁ := by linarith [s.hX₁, s.hY₁]
  have hx2 : 0≤s.X₂+s.Y₂ := by linarith [s.hX₂, s.hY₂]
  have hp := (pairNorm_pos s.hd.1 s.hd.2).le
  have h0 : 0≤(128*b)^2*(s.X₁+s.Y₁)*(s.X₂+s.Y₂)/pairNorm s.d := by positivity
  apply mul_le_mul_of_nonneg_left _ h0
  rw [(Finset.prod_subtype (Jᶜ) (fun i => by simp) (fun i=>256*s.P i)).symm]
  apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
  · intro i _
    linarith [s.hP i]
  · intro i _ _
    linarith [s.hP i]

/-- Raw form of the residual's saved exceptional budget: `savedBudget` at the residual
volume `V/∏_{j∈J} P_j` (prefixes, `L`, `K`, `W` unchanged). -/
theorem rest_saved_raw (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (ha : 0<a)
    (Jd : ℕ) (control : Finset (ℕ×ℕ)) (Q : Id) (Z ε K W : ℝ) :
    sourceVolume (restSource s hB1 J)*savedBudget (restSource s hB1 J) Jd control Q Z ε K W=
      fixedQCost Q*(sourceProfile (restSource s hB1 J) Jd control Z ε)^2*(16:ℝ)^(5/6:ℝ)*
        a^(-4/3:ℝ)*shape (sourceVolume s/∏ j ∈ J, s.P j) (pairNorm s.d) (prefixNormMax s.d)
          s.L K W := by
  have hP : 0<∏ j ∈ J, s.P j := Finset.prod_pos (fun j _=>zero_lt_one.trans_le (s.hP j))
  have hv : sourceVolume (restSource s hB1 J)=sourceVolume s/∏ j ∈ J, s.P j := by
    rw [←rest_volume s hB1 J, mul_div_assoc, div_self hP.ne', mul_one]
  rw [source_raw_budget (restSource s hB1 J) ha, hv]
  rfl

/-! ### Z0: the second zero frequency -/

/-- The second zero-frequency density of an arbitrary source with an arbitrary seed `D`
(the FP diagonal `allocated_second_zero` without allocations): columns are bounded by `Y`,
coefficients by the divisor bound, and every surviving column is divisible by the seed. -/
theorem residual_second_zero (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀r : Source ι a b,
      Fintype.card ι≤N→∀ha : 0<a,∀seed : Id,seed≠0→∀(τ : Character)(t Y K W : ℝ),1≤Y→
      sourceNormCap r.P b r.T r.d≤Y→0≤K→0≤W→
      ‖zeroDensity Finset.univ (sourceGenerator (sourceColumns r))
        (sourceGenerator_supported (sourceColumns r))
        (fun I : supportedColumns (sourceColumns r)=>sourceCoefficient r ha seed I*heightCoeff τ t I)
        K W‖≤
        (16*K*W^3)*‖paperRadialFourier ballProfile 0‖*
          (C*(profileCap r)^2*Y^(1+ε)/(seed.absNorm:ℝ)) := by
  obtain ⟨C0,hC0,hbound⟩ := original_column_bound N (ε/2) (half_pos hε)
  refine ⟨128*C0^2,by positivity,?_⟩
  intro ι instι a b r hcard ha seed hseed τ t Y K W hY hcap hK hW
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
  change ‖((16*K*W^3:ℝ):ℂ)*paperRadialFourier ballProfile 0*
    sourceSecondZero (sourceColumns r) (sourceCoefficient r ha seed) τ t‖≤_
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤16*K*W^3)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply hh.trans_eq
  calc
    _=(128*C0^2)*(profileCap r)^2*((Y^(ε/2))^2*Y)/(seed.absNorm:ℝ) := by ring
    _=_ := by rw [hp]

/-- CF §7 second zero frequency, exponent count: relative to `A-c+q_C` the excess is
`A-1-d+4u-(c-d) = A-1-c+4u`, at most `-Δ-(λ₁-1-4a)S` up to the selection mesh. -/
theorem cf_second_zero_excess (A P S c d u Δ lam a mesh : ℝ) (hA : A=P+S)
    (hface : P+lam*S≤1-Δ) (hc : 0≤c) (hu : u≤a*S+mesh) :
    (A-1-d+4*u)-(c-d)≤-Δ-(lam-1-4*a)*S+4*mesh := by
  subst hA
  nlinarith

/-! ### Zf: the fixed-inducing rows -/

/-- The inner exceptional ledger applies verbatim to the transferred residual
(`restSource`, seed `seedRest u D`, any character, Gauss scale `16·K·W⁴`). -/
theorem residual_fixed_inducing (N : ℕ)
    (α Bcap a b ε δ Bnorm Lrad Cr εsum : ℝ)
    (hα0 : 0≤α) (hα23 : α<2/3) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1)
    (hBnorm : 0≤Bnorm) (hLrad : 0≤Lrad) (hCr : 0<Cr) (hεsum : 0<εsum) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Φ : 𝓢(ℝ,ℂ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃A Csum : ℝ,0<A ∧ 0<Csum ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,∀hB1 : (∀ k, s.B k = 1),∀Jsel : Finset ι,
      OriginalEnclosure s →
      Fintype.card (Rest Jsel)≤N → (s.Fhole.absNorm:ℝ)≤Z^Bcap →
      (∏i,2*(restSource s hB1 Jsel).P i)≤Z^Bcap →
      poolCap (restSource s hB1 Jsel)≤Z^Bnorm →
      ∀(η : Character)(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∀useed Dsel : Id,seedRest useed Dsel≠0 →
      ∀(t K W Tsec ξ Hsource : ℝ),0<K → 0<W → 0≤Tsec →
      Hsource≤Z^Bnorm →
      frequencyRadius Tsec Z ξ≤Cr*Z^Lrad →
      familyConductorBudget (restSource s hB1 Jsel) η (frequencyRadius Tsec Z ξ)≤Z^Bcap →
      ∀Lref : ℝ,0<Lref → Lref≤s.L →
      ‖partEnergy true η χ₀ Q m t (sourceColumns (restSource s hB1 Jsel))
          (sourceCoefficient (restSource s hB1 Jsel) ha (seedRest useed Dsel))
          Φ (16*K*W^4) Tsec Z ξ Hsource‖/sourceVolume (restSource s hB1 Jsel)/W≤
        (Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*
          savedBudget (restSource s hB1 Jsel) J control Q Z ε K W*
          refLoss (restSource s hB1 Jsel) Lref α*Z^(2*Bnorm*δ)*
          (Csum*Z^εsum/((seedRest useed Dsel).absNorm:ℝ)) := by
  obtain ⟨J,control,h00,hk⟩ := uniform_actual_exceptional_part N α Bcap a b ε δ Bnorm Lrad Cr
    εsum hα0 hα23 hBcap ha hb hε hδ hgap hBnorm hLrad hCr hεsum
  refine ⟨J,control,h00,?_⟩
  intro Φ
  obtain ⟨Ck,hCk,hQ⟩ := hk Φ
  refine ⟨Ck,hCk,?_⟩
  intro Q hQ0 hQt hQ72
  obtain ⟨A,Csum,hA,hCsum,hZ⟩ := hQ Q hQ0 hQt hQ72
  refine ⟨A,Csum,hA,hCsum,?_⟩
  filter_upwards [hZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι instι s hB1 Jsel cover hcard hF hP hpool η χ₀ m hm hml hm2 useed Dsel hseed0
    t K W Tsec ξ Hsource hK hW hT hH hrad hcond Lref hLref0 hLref
  exact hZ.2 (Rest Jsel) (restSource s hB1 Jsel) (rest_enclosure s hB1 Jsel cover) hcard hF hP
    hpool η χ₀ m hm hml hm2 (seedRest useed Dsel) (seedRest_squarefree useed Dsel) hseed0
    t K W Tsec ξ Hsource hK hW hT hH hrad hcond Lref hLref0 hLref

/-- CF §7, first common part of the K₄ ledger at `w = u`, `w_o = 0`, `g = 4u`, `ℓ = 0`:
`F₁ = c/6+5(d+t)/6+q/6-3u` (allowance `0`), and `F₁+(c-d) ≥ c-3u-5δ/6` because
`q ≥ r ≥ |c-d|` (cube-free first common multiplicities) and `t ≥ -δ`. -/
theorem cf_first_common (c d t q u δ : ℝ) (hq : |c-d|≤q) (ht : -δ≤t) :
    c-3*u-5*δ/6≤firstSaving c (d+t) u q 0 0 (4*u) 0+(c-d) := by
  have h1 := neg_abs_le (c-d)
  unfold firstSaving
  linarith

/-- CF (7.1): with the first common part from `cf_first_common`, the second common part
`F₂ ≥ 2b₂/3`, `v = c+b₂` and the principal saving at the shortened length paid at rate `α`,
the exceptional excess relative to `A-c+q_C` is at most `A-5/6+3u-αl+o(1)`, for every
`0 ≤ α ≤ 2/3` (`cubefree_principal_excess`). -/
theorem cf_exceptional_excess (A c u b₂ l α F₁c F₂ o : ℝ)
    (hα0 : 0≤α) (hα : α≤2/3) (hc : 0≤c) (hb : 0≤b₂)
    (hF₁ : c-3*u-o≤F₁c) (hF₂ : 2*b₂/3≤F₂) :
    A-5/6-F₁c-F₂-α*max 0 (l-(c+b₂))≤A-5/6+3*u-α*l+o := by
  have hp := cubefree_principal_excess α (c+b₂) l hα0 hα (by linarith)
  linarith

end
end QRH.DensitySplitThird.CubeFree.Second.ConcreteDiag
