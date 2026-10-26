/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Coarse actual coordinate and canonical volume gates for the fixed HIGH caller. -/
/- Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F4): fork of Record1252270103Source.Admission.SelectedRegularHighPointSomeGeometry
(Hailey Collet, Apache-2.0); changes: two parents. `actual_coordinate_box_mx` and `SharedState_mx` over
`Anchor_mx`/`Family_mx`/`Selected_mx`: the first label and its caps are read from the first layer
(`sourceRadius F.s₀`, `F.zero₁₀`, `F.zero₂₀`), the selection's coordinate box from the second-layer parent
(`|logb Z (volume F.s)| ≤ 1`). `Canonical.source_volume` and `pointBudget` are generic in the input and
are reused from Collet. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularHighPointSomeGeometry
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularSourceData
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.Admission.SelectedRegularHighPoint
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open CenteredMomentEnergyState CenteredMomentRetainedProfile
open Record12518109Natural Record12518109Natural.WeightedHigh
open OAI.SevenEighths.Record1252270103Source
open Set Filter HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice Cycle61Moment Cycle61InitialMass LocalMoment Record12518109Raw
open Cycle61Moment.LowBranch Record1252270103Second Record12518109Natural.MarkedPlain
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open Record1252270103Finite PhysicalAnalytic High.GlobalPhysical
open SelectedRegularSourceData SelectedHighCofactorFamily QRH.Record1252270103Low
local notation "O"=>HeckeFamily.O
local instance selectedRegularHighPointGeometryDecEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

variable {α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}{a:Anchor_mx α₀ α Z}
    (F:Family_mx a Label)(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second)

theorem actual_coordinate_box_mx (θ annular wmin:ℝ)(w:α→ℝ)(T:Finset α)
    (hD:F.D=1)(hθ:0≤θ)(hθ1:θ≤1)(hreserve:F.reserve=θ)
    (ha:∀r,|F.amp (G.row r).val.1.1|≤1)
    (hω:|frequencyLoss Z 32 F.ξ+θ|≤1)
    (hV:|Real.logb Z (volume F.s)|≤1)
    (hsource:sourceRadius F.s₀≤Z^(2:ℝ))
    (hchild:∀r,sourceRadius (F.input (G.row r).val.1.1)≤Z^(2:ℝ))
    (hL:(G.L.absNorm:ℝ)≤Z^(4:ℝ))(hw:∀i,0≤w i)(htotal:(∑i,w i)≤1)
    (hann0:0≤annular)(hann1:annular≤1):
    ∀r i,-256≤G.x θ θ annular w wmin T r i ∧ G.x θ θ annular w wmin T r i≤256 := by
  intro r
  have hs:=FirstFamily.label_supported F.s₀ F.modifier₀ F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin (G.column r)
  have hf:=FirstFamily.label_common_bounds F.s₀ F.modifier₀ F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin
    F.seed_sf F.zero₁₀ F.zero₂₀ (G.column r)
  have hc:=SelectedSecondKeyCaps.regular_common_caps F.slots F.input F.childModifier F.mask F.childSeed
    F.Hmain F.Tsec Z F.ξ ballProfile F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂)
    F.Hmain_pos F.χ₀ F.Q F.m (G.row r).val.1
  have h26:Z^(2:ℝ)≤Z^(6:ℝ):=Real.rpow_le_rpow_of_exponent_le F.hZ.le (by norm_num)
  have hforced:((G.sel r).Cf.absNorm:ℝ)≤Z^(8:ℝ):=by
    have hnorm:=SelectedForcedGeometry.norm_le_of_dvd (G.sel r).Cf (G.L^2)
      (pow_ne_zero 2 G.L_ne) (G.forced_upper r)
    rw [map_pow,Nat.cast_pow] at hnorm
    apply hnorm.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2).trans_eq _)
    rw [←Real.rpow_mul_natCast (zero_lt_one.trans F.hZ).le]
    norm_num
  have hh:=selected_cofactor_coordinate_box F.s F.reflected second (F.first (G.row r).val.1)
    (G.datum r).C (G.datum r).D F.R (G.sel r) (G.datum r).inactive
    Z F.D (F.amp (G.row r).val.1.1) F.ξ F.reserve θ θ annular wmin 6 8 1 1 w T
    F.hZ (by norm_num) hs.1 hs.2.1 (G.datum r).hC (G.datum r).hD (G.datum r).sameSupport
    ⟨hf.2.2.1.trans (hsource.trans h26),hf.2.2.2.trans (hsource.trans h26)⟩
    ⟨hc.1.trans ((hchild r).trans h26),hc.2.trans ((hchild r).trans h26)⟩
    (by rw [hD];norm_num) (hV.trans (by norm_num)) ((ha r).trans (by norm_num))
    (by rw [hreserve];exact hω.trans (by norm_num))
    (by rw [abs_of_nonneg hθ];linarith) hforced hw htotal hann0 hann1
  intro i
  have h:=hh i
  change -256≤(G.sel r).coordinate _ _ _ _ _ _ _ _ _ _ _ _ i ∧ _≤256
  rw [abs_of_nonneg hθ] at h
  exact ⟨(show (-256:ℝ)≤-(32*6+θ+8+2*1+1) by linarith only [hθ1]).trans h.1,
    h.2.trans (show (32*6+θ+8+2*1+1:ℝ)≤256 by linarith only [hθ1])⟩

variable (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (η₀:Character)(P:HighSourceParameters)(e q θ annular wmin:ℝ)(w:α→ℝ)(T:Finset α)
    (Snew Anew:Finset (Ideal O))(hQM:F.Q≤M)(hQη:F.Q≤η₀.modulus)

def SharedState_mx (st:rows→NaturalState Z P.Bmask P.bΦ)
    (hfixed:∀l,(st l).fixedModulus=F.Q)(keep:∀l,(st l).radial.keep (G.z l))
    (select:rows→BufferIndex e):Prop :=
  ∀l,(st l).character=G.τ l ∧
    (st l).puncture=Selection.puncture (G.sel l)*((newtonDivisorPair Snew Anew).1*(newtonDivisorPair Snew Anew).2) ∧
    (st l).width≤P.Mcap ∧
    RetainedZeroBin M H hH (st l) η₀ ((hfixed l).trans_le hQM) ((hfixed l).trans_le hQη)
      (G.z l) (keep l) e (Z^P.τ) (select l) ∧
    (bufferValue e (select l)<(q+1)/2→ActualLow M H hH (st l) η₀
      ((hfixed l).trans_le hQM) ((hfixed l).trans_le hQη) ((q+1)/2) e
      (3*((select l).1.val+1:ℕ)*Z^P.τ) (G.z l)) ∧
    1≤((st l).radial.profile (‖ConcreteTraceCRT.eisEmbedding (G.z l)‖^2/(st l).radial.scale)).re ∧
    (st l).radial.profile (‖ConcreteTraceCRT.eisEmbedding (G.z l)‖^2/(st l).radial.scale)≠0 ∧
    SelectedSecondKeyCaps.KeyCaps (G.key l) Z 6
      (Real.logb Z ((firstSourceMissing (!F.reflected) (G.key l).val.1).absNorm:ℝ)) ∧
    rawFrequencyNorm (nonzeroJointSourceRow (G.key l))≤Z^(G.x θ θ annular w wmin T l 2)

section Budget
variable {β:Type}[Fintype β]

/-- Collet's `pointBudget` with the shift loss added to every exponent. -/
def pointBudget_mx (n:Source)(N J:ℕ)(θ reserve εslot wmin C Z:ℝ)(P:HighSourceParameters)
    (control:Finset (ℕ×ℕ))(s:Input β)(reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
    (ξ:ℝ)(p:Profiles (1/4) (9/4))(shiftLoss:ℝ):ℝ :=
  let e:=highBuffer 1 1 εslot (θ/16)
  let annular:=3*(N:ℝ)*Real.logb Z 2
  ∑k∈High.BufferedSelectedPaidSome.highBins e (n.q:ℝ),
    (C*Z^(θ+θ)*forcedProfileCost s)*((max 1 (forcedProfileCost s))^2*(
    geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
    cofactorRestorationCost θ 2 Z*(p.control control)^2*
    ((Finset.Icc (⌊-((256:ℝ)+5*6)/θ⌋:ℤ) ⌊((256:ℝ)+5*6)/θ⌋).card^4:ℕ)*
    (1+rawGeometryHeight Z P.τ (bufferCount e))^J*
    Z^(((1-unmarkedDensity (2*bufferValue e k-1))*(frequencyLoss Z 32 ξ+θ)+
      unmarkedDensity (2*bufferValue e k-1)*θ+θ)-((n.highFee:ℝ)+reserve)+
      (2*bufferValue e k-1)*annular+4*θ+θ+reserve/16+2*P.εplain*P.d+
      (2*P.εslot*P.d)*N+6*(θ/100)+shiftLoss)))

/-- The shifted budget is `Z^shiftLoss` times Collet's budget. -/
theorem pointBudget_mx_eq (n:Source)(N J:ℕ)(θ reserve εslot wmin C Z:ℝ)(P:HighSourceParameters)
    (control:Finset (ℕ×ℕ))(s:Input β)(reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
    (ξ:ℝ)(p:Profiles (1/4) (9/4))(shiftLoss:ℝ)(hZ:0<Z):
    pointBudget_mx n N J θ reserve εslot wmin C Z P control s reflected bin ξ p shiftLoss=
      Z^shiftLoss*pointBudget n N J θ reserve εslot wmin C Z P control s reflected bin ξ p := by
  simp only [pointBudget_mx,pointBudget]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _=>?_)
  rw [Real.rpow_add hZ (((1-unmarkedDensity (2*bufferValue (highBuffer 1 1 εslot (θ/16)) k-1))*
      (frequencyLoss Z 32 ξ+θ)+unmarkedDensity (2*bufferValue (highBuffer 1 1 εslot (θ/16)) k-1)*θ+θ)-
      ((n.highFee:ℝ)+reserve)+(2*bufferValue (highBuffer 1 1 εslot (θ/16)) k-1)*(3*(N:ℝ)*Real.logb Z 2)+
      4*θ+θ+reserve/16+2*P.εplain*P.d+(2*P.εslot*P.d)*N+6*(θ/100)) shiftLoss]
  ring
end Budget

end
end QRH.Record1252270103Source.Admission.SelectedRegularHighPoint
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighPoint.actual_coordinate_box_mx
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighPoint.pointBudget_mx_eq
