import Candidate.Cycle63.Physical.InitialMass.GeometryPayment
import Candidate.Uneven.SkewGeometry
import Candidate.Target830.Source.BalancedPayment
import Candidate.Cycle63.Physical.InitialMass.Normalization

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source.Uneven
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstSourceConductorCaps CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
local notation "O" => HeckeFamily.O

open Cycle63InitialMass

def skew (v : Fin 5 → ℝ) : ℝ :=
  SkewNormalization.skew (v 0) (v 1) (v 3) (v 2)

def unevenLeft (A : ℝ) (v : Fin 5 → ℝ) : ℝ := balancedLeft A v+skew v
def unevenRight (A : ℝ) (v : Fin 5 → ℝ) : ℝ := balancedRight A v-skew v
def allocation (reflected : Bool) (v : Fin 5 → ℝ) : ℝ :=
  surplus v + if reflected then -skew v else skew v

theorem allocation_nonneg (reflected : Bool) (v : Fin 5 → ℝ) (hs : 0 ≤ surplus v) :
    0 ≤ allocation reflected v := by
  have hh := Sil.Uneven.Geometry.allocations_nonnegative hs
  cases reflected <;> dsimp [allocation,skew,surplus] at * <;> linarith only [hh.1,hh.2]

theorem left_eq_old (A : ℝ) (v : Fin 5 → ℝ) :
    unevenLeft A v=Cycle63InitialMass.leftExponent A v+allocation false v := by
  rw [unevenLeft,Source.left_eq_old]
  simp only [allocation,Bool.false_eq_true,ite_false]
  ring

theorem right_eq_old (A : ℝ) (v : Fin 5 → ℝ) :
    unevenRight A v=Cycle63InitialMass.rightExponent A v+allocation true v := by
  rw [unevenRight,Source.right_eq_old]
  simp only [allocation,ite_true]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem actual_allocation_nonneg (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hZ : 1<Z) (q : FirstSourceCoordinate s R seed K Z ξ) :
    0 ≤ allocation reflected (geometryExponents s R seed K Z ξ q) := by
  exact allocation_nonneg reflected _ (actual_surplus_nonneg s R seed K Z ξ hZ q)

omit [DecidableEq ι] in
/-- Uniform cross-label payment. The left and right labels may differ;
no sum of per-label Cauchy estimates is substituted for joint Cauchy. -/
theorem actual_uneven_cross_payment (s : Input ι) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hZ : 1<Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤ Z^B)
    (key : ℤ×(Fin 5→ℤ)) (q r : CommonGeometryFiber s R seed K Z ξ key) :
    Z^(outsideExponent M A (geometryExponents s R seed K Z ξ q.val))*
      Real.sqrt (Z^(unevenLeft A (geometryExponents s R seed K Z ξ q.val)))*
      Real.sqrt (Z^(unevenRight A (geometryExponents s R seed K Z ξ r.val))) ≤
        32*Z^M := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hw : 0≤ Real.logb Z 2 := Real.logb_nonneg hZ (by norm_num)
  have hdiff := actual_geometry_fiber_difference s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key
  have he := Sil.Uneven.Geometry.cross_label_budget
    (m := M) (a := A)
    (c := geometryExponents s R seed K Z ξ q.val 0)
    (d := geometryExponents s R seed K Z ξ q.val 1)
    (r := geometryExponents s R seed K Z ξ q.val 3)
    (e := geometryExponents s R seed K Z ξ q.val 4)
    (c' := geometryExponents s R seed K Z ξ r.val 0)
    (d' := geometryExponents s R seed K Z ξ r.val 1)
    (r' := geometryExponents s R seed K Z ξ r.val 3)
    (e' := geometryExponents s R seed K Z ξ r.val 4)
    (p := geometryExponents s R seed K Z ξ q.val 2)
    (p' := geometryExponents s R seed K Z ξ r.val 2)
    (w := Real.logb Z 2)
    (abs_le.mpr ⟨by linarith [hdiff q r 0],hdiff r q 0⟩)
    (abs_le.mpr ⟨by linarith [hdiff q r 1],hdiff r q 1⟩)
    (abs_le.mpr ⟨by linarith [hdiff q r 3],hdiff r q 3⟩)
    (abs_le.mpr ⟨by linarith [hdiff q r 4],hdiff r q 4⟩)
    (abs_le.mpr ⟨by linarith [hdiff q r 2],hdiff r q 2⟩)
  change outsideExponent M A (geometryExponents s R seed K Z ξ q.val)+
    (unevenLeft A (geometryExponents s R seed K Z ξ q.val)+
      unevenRight A (geometryExponents s R seed K Z ξ r.val))/2≤ M+41*Real.logb Z 2/10 at he
  have hp : Z^(M+5*Real.logb Z 2)=32*Z^M := by
    rw [Real.rpow_add hz,show 5*Real.logb Z 2=Real.logb Z 2*5 by ring,
      Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' (by norm_num : (0:ℝ)<2)]
    norm_num
    ring
  rw [←hp]
  simp only [Real.sqrt_eq_rpow,←Real.rpow_mul hz.le,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith


omit [DecidableEq ι] in
/-- The actual first scalar stays on the left of joint Cauchy. Normalized
left and right energies are still summed over every label in the bin. -/
theorem actual_uneven_joint_energy {I J : Type*} [Fintype I] [Fintype J] (s : Input ι) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hZ : 1<Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤ Z^B)
    (key : ℤ×(Fin 5→ℤ))
    (left : I→CommonGeometryFiber s R seed K Z ξ key)
    (right : J→CommonGeometryFiber s R seed K Z ξ key) (L : I→ℝ) (N : J→ℝ)
    (hL : ∀q,0≤ L q) (hN : ∀q,0≤ N q) :
    Real.sqrt (∑q,Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ (left q).val)+
        unevenLeft A (geometryExponents s R seed K Z ξ (left q).val))*L q)*
      Real.sqrt (∑q,Z^(unevenRight A (geometryExponents s R seed K Z ξ (right q).val))*N q) ≤
        32*Z^M*Real.sqrt (∑q,L q)*Real.sqrt (∑q,N q) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  apply weighted_joint_energy _ _ _ _ _ (fun _=>Real.rpow_nonneg hz.le _)
    (fun _=>Real.rpow_nonneg hz.le _) hL hN (by positivity)
  intro q r
  have hh := actual_uneven_cross_payment s R seed K Z ξ B M A hZ hs hz₁ hz₂ hsource key (left q) (right r)
  have hsquared := pow_le_pow_left₀ (by positivity) hh 2
  rw [mul_pow,mul_pow,Real.sq_sqrt (Real.rpow_nonneg hz.le _),
    Real.sq_sqrt (Real.rpow_nonneg hz.le _),←Real.rpow_mul_natCast hz.le,
    ←Real.rpow_add hz] at hsquared
  convert hsquared using 1
  congr 2
  ring

end
end OAI.SevenEighths.Target830.Source.Uneven
#print axioms OAI.SevenEighths.Target830.Source.Uneven.actual_uneven_joint_energy
