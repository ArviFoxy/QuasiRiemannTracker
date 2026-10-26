/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F1/F2): fork of Record1252270103Source.Admission.SelectedHighPaidComparison
(Hailey Collet, Apache-2.0; inherited notices retained).

* `PhaseBound_mx`: Collet's `PhaseBound` with two parents. The balanced column scalar is read
  from the first layer `s₀` at the original volume `logb Z (volume s₀)` (never at the virtual
  volume: the scalar trap of `L45_DESIGN.md` §1); the selection, its first frozen coefficient, the
  normalizing volume and the MAIN radius are read from the second-layer parent `s` at the
  amplitude `amp` (the virtual `a_v` for a transfer residual).
* `uniform_selected_paid_sum_mx`: the pool `P` is the actual one, with `FixedCellPoolData` at the
  pool width `poolAmp`; `mainExtra` is read at `s₀` and `poolAmp` (the ball factor is the original
  one). The paid sum is bounded by the *shifted* first mass `Z^(amp - poolAmp) * mass(s₀)`, which
  `QRH.MixedStep.Downstream.shifted_high_mass_mx` converts to the virtual side. `mainExtra` itself
  is reused verbatim. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedHighPaidComparison
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalSelectedMass
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedHighPaid
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentAddedZeroUniform CenteredMomentFirstAnnularMajorant
open Cycle61InitialMass Cycle61Moment Record1252270103Second
open CenteredMomentSecondCanonicalScalar Record12518109Natural.MarkedPlain
open CenteredMomentAmplificationChildSourceCaps
open OAI.SevenEighths.Record1252270103Source
open High High.GlobalPhysical SelectedHighCofactorFamily SelectedHighCofactorCoordinates
open Pool
local notation "O" => HeckeFamily.O
local instance selectedHighPaidDecEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- Two parents: the scalar of the first layer `s₀` at its own volume; selection, frozen
coefficient, volume and radius at the second-layer parent `s`. -/
def PhaseBound_mx {α₀ α:Type}[Fintype α₀][Fintype α](s₀:Input α₀)(modifier₀:Tuple α₀→ℂ)
    (s:Input α)(R seed:Ideal O)
    (W:𝓢(ℝ,ℂ))(D Z ξ amp reserve:ℝ)(hK:0<Z^D)(bin:ℤ×(Fin 5→ℤ))(reflected second:Bool)
    (j:FirstColumnIndex (CoupledFirst.geometryFirstSource s₀ modifier₀ R seed (Z^D) Z ξ hK bin))
    (C₂ D₂:Ideal O)(U:Finset (CommonIndex C₂ D₂))
    (sel:Selection s reflected second (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin j) C₂ D₂ R)
    (extra lower ω:ℝ):Prop :=
  ω≤(‖CoupledFirst.balancedColumnScalar reflected s₀ modifier₀ R seed (Z^D) Z ξ D
    (Real.logb Z (volume s₀)) hK bin
    (fun q=>normPhase (CoupledFirst.coordinateBlock s₀ modifier₀ R seed W (Z^D) Z ξ q)) j‖^2*
    extra*‖frozenCoefficient sel.B₁.val
      (if reflected then (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin j).1.2
        else (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin j).1.1)
      R s.ν s.W s.P‖^2/volume s)*
    (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve
      (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin j)/lower)*normalizer C₂ D₂ U

/-- Collet's `uniform_selected_paid_sum` with two parents and two amplitudes: the radius at
`amp l`, the actual pool `P l` at `poolAmp l`. The excess `Z^(amp l - poolAmp l)` stays on the
first mass. -/
theorem uniform_selected_paid_sum_mx (N:ℕ)(B₁ B₂ ε ell lower radiusMax:ℝ)
    (hB₁:0≤B₁)(hB₂:0≤B₂)(hε:0<ε)(hell:0<ell)(hlower:0<lower)(hmax:0≤radiusMax):
    ∃C:ℝ,0<C ∧ ∀{α₀ α:Type}[Fintype α₀][Fintype α](s₀:Input α₀)(s:Input α),
      Fintype.card α₀≤N→Fintype.card α≤N→
    ∀(modifier₀:Tuple α₀→ℂ)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(D Z ξ reserve εmass:ℝ)
      (hK:0<Z^D)(bin:ℤ×(Fin 5→ℤ))(reflected second:Bool),0≤εmass→
    ∀{κ:Type}(labels:Finset κ)
      (column:κ→FirstColumnIndex (CoupledFirst.geometryFirstSource s₀ modifier₀ R seed (Z^D) Z ξ hK bin))
      (C₂ D₂:κ→Ideal O)(U:∀l,Finset (CommonIndex (C₂ l) (D₂ l)))
      (sel:∀l,Selection s reflected second
        (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l)) (C₂ l) (D₂ l) R)
      (P:κ→Finset (Ideal O))(amp poolAmp H0 radius mesh loss BD Bsource:κ→ℝ)(depth:κ→ℕ)
      (lossMax:ℝ)(ω cost:κ→ℝ),
      (∀l∈labels,Supported (C₂ l))→
      (∀l∈labels,((if reflected then (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l)).1.2
        else (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l)).1.1).absNorm:ℝ)≤Z^B₁)→
      (∀l∈labels,((if second then D₂ l else C₂ l).absNorm:ℝ)≤Z^B₂)→
      (∀l∈labels,FixedCellPoolData (P l) Z (poolAmp l) ell (mesh l) (loss l) (BD l) (Bsource l) (depth l))→
      (∀l∈labels,0<H0 l)→(∀l∈labels,0≤radius l+6*poolAmp l)→
      (∀l∈labels,radius l+6*poolAmp l≤radiusMax)→(∀l∈labels,loss l≤lossMax)→
      (∀l∈labels,PhaseBound_mx s₀ modifier₀ s R seed W D Z ξ (amp l) reserve hK bin reflected second
        (column l) (C₂ l) (D₂ l) (U l) (sel l)
        (mainExtra s₀ (if reflected then (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l)).1.2
          else (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l)).1.1)
          (P l) (H0 l) (radius l) (poolAmp l) ell) lower (ω l))→
      (∀l∈labels,0≤cost l)→
      (∑l∈labels,cost l*selectedPaidWeight (sel l) (ω l))≤
      (C*Z^(ε+lossMax)*forcedProfileCost s)*
      ∑l∈labels,(Z^(amp l-poolAmp l)*
        CoupledFirst.balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ εmass hK bin (column l))*
        cost l*(sel l).raw (U l) Z D (amp l) ξ reserve := by
  obtain ⟨C,hC,hpref⟩:=MarkedMainPrefactor.uniform_main_prefactor N B₁ B₂ ε ell lower radiusMax
    hB₁ hB₂ hε hell hlower hmax
  refine ⟨C,hC,?_⟩
  intro α₀ α _ _ s₀ s hN₀ hN modifier₀ R seed W D Z ξ reserve εmass hK bin reflected second hεmass
    κ labels column C₂ D₂ U sel P amp poolAmp H0 radius mesh loss BD Bsource depth lossMax ω cost
    hC₂ hcap₁ hcap₂ hpool hH hrad0 hrad hloss hphase hcost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  let C₁:=if reflected then (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l)).1.2
    else (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l)).1.1
  let extra:=mainExtra s₀ C₁ (P l) (H0 l) (radius l) (poolAmp l) ell
  have hz:0<Z:=zero_lt_one.trans (hpool l hl).scale_gt_one
  have he:0≤extra:=by
    dsimp only [extra,mainExtra]
    exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
      (div_nonneg (hrad0 l hl) hell.le)
  have hn₁:Fintype.card (liveIndices (sel l).B₁.val)≤N:=
    (Fintype.card_le_of_injective (fun i:liveIndices (sel l).B₁.val=>i.val) Subtype.val_injective).trans hN
  have hp:=hpref s₀ (sel l).firstInput hN₀ hn₁
    C₁ (if second then D₂ l else C₂ l) (P l) Z (poolAmp l) (mesh l) (loss l) (BD l) (Bsource l) (depth l)
    (allocation_ne s C₁ (sel l).B₁) (allocation_ne (sel l).firstInput _ (sel l).B₂)
    (hcap₁ l hl) (hcap₂ l hl) (hpool l hl) (H0 l) (radius l) (hH l hl) (hrad0 l hl) (hrad l hl)
  have hpay:extra*((actualAllocations (sel l).firstInput.pools (if second then D₂ l else C₂ l)).card:ℝ)^2*
      Z^(poolAmp l)/lower≤C*Z^(ε+lossMax) := by
    have heq:extra*((actualAllocations (sel l).firstInput.pools (if second then D₂ l else C₂ l)).card:ℝ)^2*
        Z^(poolAmp l)/lower=
        ((bands (H0 l)).card:ℝ)*((actualAllocations s₀.pools C₁).card:ℝ)^2*
        ((actualAllocations (sel l).firstInput.pools (if second then D₂ l else C₂ l)).card:ℝ)^2*
        (Z^(poolAmp l)/(P l).card)*((radius l+6*poolAmp l)/ell)/lower := by
      dsimp only [extra,mainExtra];ring
    rw [heq]
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hpool l hl).scale_gt_one.le (by linarith [hloss l hl])) hC.le)
  have hh:=High.GlobalPhysical.actual_selected_paid_weight_mx s₀ modifier₀ s R seed W D Z ξ (amp l) reserve εmass
    hz hK hεmass bin reflected second (column l) (C₂ l) (D₂ l) (hC₂ l hl) (U l) (sel l) extra lower (ω l)
    he hlower (hphase l hl)
  have hm:0≤CoupledFirst.balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ εmass hK bin (column l):=by
    unfold CoupledFirst.balancedFirstHighMass
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hr:=selected_raw_nonneg (sel l) (hC₂ l hl) (U l) Z D (amp l) ξ reserve hz
  have hsplit:extra*((actualAllocations (sel l).firstInput.pools (if second then D₂ l else C₂ l)).card:ℝ)^2*
      Z^(amp l)/lower*forcedProfileCost s=
      (extra*((actualAllocations (sel l).firstInput.pools (if second then D₂ l else C₂ l)).card:ℝ)^2*
        Z^(poolAmp l)/lower)*forcedProfileCost s*Z^(amp l-poolAmp l) := by
    have hza:Z^(amp l)=Z^(poolAmp l)*Z^(amp l-poolAmp l):=by
      rw [← Real.rpow_add hz];congr 1;ring
    rw [hza];ring
  have hh':selectedPaidWeight (sel l) (ω l)≤(C*Z^(ε+lossMax)*forcedProfileCost s)*
      (Z^(amp l-poolAmp l)*CoupledFirst.balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ εmass hK bin (column l))*
      (sel l).raw (U l) Z D (amp l) ξ reserve := by
    refine hh.trans ?_
    rw [hsplit]
    have hz':0≤Z^(amp l-poolAmp l):=(Real.rpow_pos_of_pos hz _).le
    calc (extra*((actualAllocations (sel l).firstInput.pools (if second then D₂ l else C₂ l)).card:ℝ)^2*
          Z^(poolAmp l)/lower)*forcedProfileCost s*Z^(amp l-poolAmp l)*
          CoupledFirst.balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ εmass hK bin (column l)*
          (sel l).raw (U l) Z D (amp l) ξ reserve
        =(extra*((actualAllocations (sel l).firstInput.pools (if second then D₂ l else C₂ l)).card:ℝ)^2*
          Z^(poolAmp l)/lower)*(forcedProfileCost s*(Z^(amp l-poolAmp l)*
          CoupledFirst.balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ εmass hK bin (column l))*
          (sel l).raw (U l) Z D (amp l) ξ reserve) := by ring
      _≤(C*Z^(ε+lossMax))*(forcedProfileCost s*(Z^(amp l-poolAmp l)*
          CoupledFirst.balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ εmass hK bin (column l))*
          (sel l).raw (U l) Z D (amp l) ξ reserve) :=
        mul_le_mul_of_nonneg_right hpay
          (mul_nonneg (mul_nonneg (forcedProfileCost_nonneg s) (mul_nonneg hz' hm)) hr)
      _=_ := by ring
  exact (mul_le_mul_of_nonneg_left hh' (hcost l hl)).trans_eq (by ring)

end
end QRH.Record1252270103Source.Admission.SelectedHighPaid
#print axioms QRH.Record1252270103Source.Admission.SelectedHighPaid.uniform_selected_paid_sum_mx
