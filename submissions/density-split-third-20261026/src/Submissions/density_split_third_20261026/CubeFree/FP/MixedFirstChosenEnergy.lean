/- Copyright (c) 2026 Sil. Apache-2.0.
Actual grouped energy with chosen losses and actual logarithmic geometry.
No Gates, SourceGeometry or energy estimate is an input. Parent checks Lean.
Modified by Sil (2026-10-26): cube-free: alpha_e < 2/3; per-subset AllocatedSupply under the balanced pair gate; generic gate enon - d + B0*h <= step in place of FP's (3/4)S < d; arbitrary reference exponent l with ReferenceChoice, reference length cstar*Z^l (cstar <= 1) and the alpha-loss margin (2/3-alpha_e)*l + (P+S-5R/6+7d/3-2l/3) <= 0; AlphaReferenceMargin for the FP midpoint (holds when (2/3-alpha_e)*R <= 2*rho/3); the selected block is Second.SelectedBlock..
-/
import Submissions.density_split_third_20261026.CubeFree.FP.MixedFirstUniformEnergy
import Submissions.density_split_third_20261026.CubeFree.FP.MixedFirstUniformLossBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.FP.MixedFirstChosenEnergy
open Candidate.FourthPower
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ActualEisensteinCubic RayFourExpansion
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open MixedFirstActualNonexceptional MixedFirstExceptionalApplication
open MixedFirstAvoidance MixedFirstPhysicalApplication MixedFirstGeometricCaps
open MixedFirstPaidCosts MixedFirstCutoffs MixedFirstProfileEnvelope
open MixedFirstUniformEnergy MixedFirstUniformLossBudget
open MixedCompletedRows ReferencePrimeEnclosure
open QRH.Record1252270103KernelMass (pairNorm ideal_norm_one_le)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι]

/-- The deterministic midpoint already used in the paper and in
reference_interval_nonempty. Equality belongs to the uncentered case. -/
def referenceExponent (R P S d : ℝ) : ℝ :=
  if P+S≤5*R/6-7*d/3 then 0
  else (MixedLedger.lower R P S d+MixedLedger.upper R P S d)/2

/-- Cube-free (WP-J α-loss): the α-loss `(2/3-α)·l` at the FP midpoint reference exponent
`l` must be covered by that reference's reserve `2l/3-(P+S-5R/6+7d/3)` at every admissible
geometry. The argument `κα` is the coefficient `2/3-α`. It holds when `κα·R ≤ 2ρ/3`
(`alphaReferenceMargin_of_width`): the centered reserve is the third of the interval width
`R-P-2S-4d ≥ ρ`, and `l < P/2 ≤ R/2`. -/
def AlphaReferenceMargin (κα R d rho : ℝ) : Prop :=
  ∀P S : ℝ,0≤S→P+2*S+4*d≤R-rho→
    κα*referenceExponent R P S d+(P+S-5*R/6+7*d/3-2*(referenceExponent R P S d)/3)≤0

theorem reference_exponent_choice (R P S d : ℝ) (h : P+2*S+4*d<R) :
    ReferenceChoice R P S d (referenceExponent R P S d) := by
  unfold referenceExponent
  split_ifs with hc
  · exact Or.inl ⟨rfl,hc⟩
  · have hw := MixedLedger.reference_interval_width R P S d
    refine Or.inr ⟨lt_of_not_ge hc,?_,?_⟩ <;> linarith

/-- The reference may pay its fixed conductor by d+omega while the
actual first energy keeps d. The midpoint has a common original reserve;
omega=budgetStep and deltaRef=budgetStep/2 fit these two inequalities. -/
theorem reference_exponent_margins (R P S d rho omega deltaRef : ℝ)
    (hrho : 0<rho) (hS : 0≤S) (hd : 0≤d)
    (hcap : P+2*S+4*d≤R-rho) (hcenter : 5*R/6-7*d/3<P+S)
    (homega : omega≤rho/100) (hdelta : deltaRef≤rho/200) :
    let l := referenceExponent R P S d
    0<l ∧ l<P/2 ∧
      l+(R+(d+omega))/2+S+2*deltaRef≤(4/5)*R ∧
      R+(d+omega)+2*l-P+S+2*deltaRef≤R/2 := by
  have hmix : P+2*S+4*d<R := by linarith
  have href := reference_exponent_choice R P S d hmix
  have hlower : MixedLedger.lower R P S d<referenceExponent R P S d := by
    rcases href with ⟨_,hc⟩|⟨_,hl,_⟩
    · linarith
    · exact hl
  have hupper : referenceExponent R P S d<MixedLedger.upper R P S d := by
    rcases href with ⟨_,hc⟩|⟨_,_,hu⟩
    · linarith
    · exact hu
  have hg := MixedLedger.reference_gate hS hd hmix (by linarith) hlower hupper
  dsimp only
  refine ⟨hg.1,hg.2.1,?_,?_⟩ <;>
    simp only [referenceExponent,if_neg (not_le.mpr hcenter)] <;>
    dsimp only [MixedLedger.lower,MixedLedger.upper] <;> linarith

theorem alphaReferenceMargin_of_width (κα R d rho : ℝ) (hκ : 0≤κα) (hd : 0≤d) (hrho : 0<rho)
    (hR : κα*R≤2*rho/3) : AlphaReferenceMargin κα R d rho := by
  intro P S hS h
  by_cases hc : P+S≤5*R/6-7*d/3
  · simp only [referenceExponent,if_pos hc]
    linarith
  · have hm := reference_exponent_margins R P S d rho 0 0 hrho hS hd h (lt_of_not_ge hc)
      (by linarith) (by linarith)
    dsimp only at hm
    have hw : 2*(referenceExponent R P S d)/3-(P+S-5*R/6+7*d/3)=(R-P-2*S-4*d)/3 := by
      simp only [referenceExponent,if_neg hc]
      dsimp only [MixedLedger.lower,MixedLedger.upper]
      ring
    have hl : κα*referenceExponent R P S d≤κα*(R/2) :=
      mul_le_mul_of_nonneg_left (by linarith [hm.2.1]) hκ
    linarith

theorem fixed_presentation_one_le : 1≤fixedPresentationCost := by
  have h₁ := ideal_norm_one_le (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero)
  have h₂ : (1:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ) := ideal_norm_one_le (by simp)
  unfold fixedPresentationCost
  nlinarith

/-- This is the actual width, including the fixed presentation factor.
It is not logb(Neta*K) with that factor silently discarded. -/
theorem input_width_power (η : Character) (K Z : ℝ) (hK : 0<K) (hZ : 1<Z) :
    Z^(inputWidth η K Z)=fixedPresentationCost*(η.modulus.absNorm:ℝ)*K := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hη : 0<(η.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (ideal_norm_one_le η.modulus_ne_bot)
  unfold inputWidth
  rw [Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hη,
    Real.rpow_logb hz hZ.ne' fixedPresentationCost_pos]
  ring

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Actual unit-prefix, live-seed-one energy, uniformly over every live
subset. Numeric exponents are the actual logarithms of total ordinary
volume and selected volume, and the actual sum of live marked widths.

The remaining length inequality is literal: the source must have the
chosen reference length. allocatedReference supplies it in the centered
branch; a short original rectangle is handled by the separate reference
supplier, not by assuming this inequality for an arbitrary source.

The full original seed norm is only an outside reconstruction cost here.
Its subpower and one reference loss are paid explicitly on the left.
All constants precede T, that seed, and every original profile/height.
-/
theorem uniform_chosen_first_energy
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b B Lslot Lcap Cap BR BH Bη lo hi αe cstar Kslot Bseed εfinal rho : ℝ)
    (ha : 0<a) (hb : 1≤b)
    (hB : 1≤B) (hBH : 0≤BH)
    (hα0 : 0≤αe) (hα23 : αe<2/3) (hcstar : 0<cstar) (hcstar1 : cstar≤1) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hεfinal : 0<εfinal) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)})
    (expo : (T : Finset ι)→(T→ℝ)→Id→Id→Character→ℝ→ℝ)
    (hsupply : ∀T : Finset ι,MixedFirstFullBudget.AllocatedSupply (ι:=T) M Hray hHray Holes Wslot a b B Lslot Lcap Cap BR
      (sourceExponent B) BH (sourceExponent B)
      (Bη+sourceExponent B+physicalStep B Bseed εfinal rho) (physicalStep B Bseed εfinal rho) lo hi
      (geometryExponent (sourceExponent B) (physicalStep B Bseed εfinal rho)) 1 ha hb Q (expo T)) :
    let step := budgetStep B Bseed εfinal rho
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀T : Finset ι,
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source T a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t (fun i=>R₀ i.val) s→
      s.d=(1,1)→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i : T,∀P∈s.H,P.val∈R₀ i.val)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      Z^(-B)≤s.L→s.X₁≤Z^B→s.X₂≤Z^B→s.Y₁≤Z^B→s.Y₂≤Z^B→(∏i,s.P i)≤Z^B→
    ∀cover : OriginalEnclosure s,∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→1≤sharpSupport s→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀u : Id,u∣s.R→∀(α : Type v) [Fintype α],∀q : QRH.DensitySplitThird.CubeFree.Second.SelectedBlock.SelectedBlock α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.amp i I‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R := inputWidth η K Z
    let P := Real.logb Z s.T
    let S := ∑i : T,w i.val
    let d := Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→
    ∀enon : ℝ,MixedFirstFullBudget.PairGate Z enon (fun G Gopp τ=>expo T (fun i=>w i.val) G Gopp τ (MixedSelectedVolume.scale q))→
      enon-d+sourceExponent B*physicalStep B Bseed εfinal rho≤budgetStep B Bseed εfinal rho→
    ∀l : ℝ,ReferenceChoice R P S d l→(2/3-αe)*l+(P+S-5*R/6+7*d/3-2*l/3)≤0→
      cstar*Z^l≤s.L→
    ∀Dseed : Id,Dseed≠0→(Dseed.absNorm:ℝ)≤Z^Bseed→
    let A := sourceControl control s.W₁*sourceControl control s.W₂
    let H := height t V s.t₁ s.t₂
    ((Dseed.absNorm:ℝ)^step*Z^step)*
      (‖∑F∈QRH.DensitySplitThird.CubeFree.Second.SelectedBlock.selectedProducts q,
          ((QRH.DensitySplitThird.CubeFree.Second.SelectedBlock.groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
          finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 t
            (sourceColumns (avoidSource s u)) (selectedCoefficient (avoidSource s u) ha 1 F) Φ K‖/
          sourceVolume s)≤
      C*Kslot^(2*N)*A^2*H^J*((η.modulus.absNorm:ℝ)*K)*Z^εfinal := by
  dsimp only
  let step := budgetStep B Bseed εfinal rho
  let h := physicalStep B Bseed εfinal rho
  let B0 := sourceExponent B
  have hbud := chosen_loss_budgets B Bseed εfinal rho hB hBseed hεfinal hrho
  dsimp only at hbud
  have hstep : 0<step := hbud.1
  have hh : 0<h := hbud.2.1
  have hh1 : h≤1 := by have hhsmall := hbud.2.2.2.1;change h≤1/100 at hhsmall;linarith
  have hgap : αe+2*h<1 := by have := hbud.2.2.2.2.2.1;linarith
  have hB0 : 1≤B0 := by dsimp only [B0,sourceExponent];linarith
  obtain ⟨J,control,henergy⟩ := uniform_grouped_first_energy_subsets (ι:=ι) M Hray hHray
    Φ N Holes hcard Wslot a b B Lslot Lcap Cap BR BH Bη h h lo hi αe h h h
    (2*B0+1) step step cstar Kslot ha hb hB hBH hh hh hα0 hα23 hgap hh hh hh
    hstep hstep hcstar hKslot Q hQt hQ72 expo hsupply
  have hgates := uniform_chosen_gates.{v} N B Bseed εfinal rho hB hBseed hεfinal hrho
  have hsharp := eventually_sharp_support.{u} N b 1 (by norm_num)
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C0,hC0,henergy⟩ := henergy η₀ hη₀
  refine ⟨3*fixedPresentationCost*C0,
    mul_pos (mul_pos (by norm_num) fixedPresentationCost_pos) hC0,?_⟩
  filter_upwards [henergy,hgates,hsharp] with Z henergyZ hgatesZ hsharpZ
  refine ⟨henergyZ.1,?_⟩
  intro T θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreqs hR₀ s hcanonical hunit hMs
    hR hHholes hholes hHR hFhole hmin hX₁ hX₂ hY₁ hY₂ hP cover η hη
    K hK hKcap hKinv hX χ₀ msecond hm hml hm2 u hu α instα q hα hqP hqpool hqamp
    hWcap hWinv hqvolume hR0 hmixed enon hexpo hnative l hreference hαmargin hlength Dseed hDseed hDcap
  let R := inputWidth η K Z
  let P := Real.logb Z s.T
  let S := ∑i : T,w i.val
  let d := Real.logb Z (MixedSelectedVolume.volume q)
  have hZ : 1<Z := henergyZ.1
  have hz : 0<Z := zero_lt_one.trans hZ
  have hS : 0≤S := Finset.sum_nonneg (fun i _=>hw i.val)
  have hd : 0≤d := Real.logb_nonneg hZ hqvolume
  have hmix : P+2*S+4*d<R := by linarith
  have hqvolumePos : 0<MixedSelectedVolume.volume q := zero_lt_one.trans_le hqvolume
  have hqpower : MixedSelectedVolume.volume q=Z^d :=
    (Real.rpow_logb hz hZ.ne' hqvolumePos).symm
  let p := chosenParameters B0 B0 B0 step (normExponent B B h) R P S d
    l cstar Z K 0 (MixedSelectedVolume.scale q) enon ((2/3-αe)*l)
  have hαloss0 : 0≤(2/3-αe)*l :=
    mul_nonneg (by linarith) (reference_choice_bounds hreference).1
  have hp : Gates p := hgatesZ.2 R P S d l cstar enon ((2/3-αe)*l)
    hS hd hcstar hcstar1 hmix hnative hαloss0 hαmargin hreference α q hα hqP hqpower K 0 hK
  have hcardT : Fintype.card T≤N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.subset_univ T)).trans (by simpa using hcard)
  have hvolcap := (source_volume_caps s Z B hZ hmin hX₁ hX₂ hP).1
  have hpair : pairNorm s.d=1 := by simp only [hunit,pairNorm,map_one,Nat.cast_one,mul_one]
  have hxcap : sharpSupport s≤Z^B0 := by
    have hhcap := hsharpZ.2 T a s hcardT (3*B) hvolcap
    simpa only [hpair,div_one,B0,sourceExponent] using hhcap
  have hprod : (∏i : T,s.P i)=Z^S := by
    rw [hcanonical.2.2.2.2,←Real.rpow_sum_of_pos hz]
  have hvol : Real.logb Z (sourceVolume s)=P+S := by
    unfold sourceVolume
    rw [s.hpX,hprod,Real.logb_mul s.total_pos.ne' (Real.rpow_pos_of_pos hz S).ne',
      Real.logb_rpow hz hZ.ne']
  have hg : SourceGeometry p s η (fun i=>w i.val) := {
    volume := hvol.le
    width := le_refl _
    length := hlength
    support := hxcap
    slots := le_refl _ }
  have he := henergyZ.2 T θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreqs hR₀ s hcanonical
    hunit hMs hR hHholes hholes hHR hFhole hmin hX₁ hX₂ hY₁ hY₂ hP cover η hη
    K hK hKcap hKinv hX χ₀ msecond hm hml hm2 u hu α q hα hqP hqpool hqamp
    hWcap hWinv R P S d l cstar h (3*h) step B0 enon hexpo (le_refl _) hp hg
  have hηone : (1:ℝ)≤(η.modulus.absNorm:ℝ) := ideal_norm_one_le η.modulus_ne_bot
  have hwidth : (η.modulus.absNorm:ℝ)*K≤Z^R := by
    change (η.modulus.absNorm:ℝ)*K≤Z^(inputWidth η K Z)
    rw [input_width_power η K Z hK hZ]
    have hh := mul_le_mul_of_nonneg_right fixed_presentation_one_le
      (mul_nonneg (zero_le_one.trans hηone) hK.le)
    simpa only [one_mul,mul_assoc] using hh
  have hNs : 0<(Dseed.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hDseed)
  have hpay := normalized_grouped_rhs_paid B Bseed εfinal rho Z R (η.modulus.absNorm:ℝ) K
    (Dseed.absNorm:ℝ) 1 hB hBseed hεfinal hrho hZ.le hR0 hηone hK.le hwidth hNs hDcap
    zero_lt_one
  simp only [one_mul] at hpay
  have hpay' := (div_le_div_iff_of_pos_right hNs).mp hpay
  let A := sourceControl control s.W₁*sourceControl control s.W₂
  let H := height t V s.t₁ s.t₂
  let Ap := C0*Kslot^(2*N)*A^2*H^J
  have hH : 1≤H := by
    dsimp only [H,height]
    linarith [abs_nonneg t,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hAp : 0≤Ap := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC0.le
      (pow_nonneg (zero_le_one.trans hKslot) _)) (sq_nonneg A))
      (pow_nonneg (zero_le_one.trans hH) _)
  have hfac : 0≤(Dseed.absNorm:ℝ)^step*Z^step :=
    mul_nonneg (Real.rpow_nonneg hNs.le _) (Real.rpow_nonneg hz.le _)
  dsimp only at he hpay' ⊢
  have he' := mul_le_mul_of_nonneg_left he hfac
  have hpay'' := mul_le_mul_of_nonneg_left hpay' hAp
  calc
    _≤Ap*((Dseed.absNorm:ℝ)^step*Z^step)*
        ((η.modulus.absNorm:ℝ)*K*Z^(step+5*(tailExponent B0 h h)*h+step+
          (tailExponent B0 h h)*step)+K*Z^(B0*h+(tailExponent B0 h h)*step)+
          Z^(-(2*B0+1)+(tailExponent B0 h h)*step)) := by
      convert he' using 1 <;> (try dsimp only [Ap,A,H]) <;> ring
    _≤Ap*(3*Z^(R+εfinal)) := by
      convert hpay'' using 1 <;> ring
    _=_ := by
      change Ap*(3*Z^(inputWidth η K Z+εfinal))=_
      rw [Real.rpow_add hz,input_width_power η K Z hK hZ]
      dsimp only [Ap,A,H]
      ring

end
end QRH.DensitySplitThird.CubeFree.FP.MixedFirstChosenEnergy
