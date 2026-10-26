/- Mixed step (L4/L5, F2): the δ-shift.

The first-layer scalar stays at the original volume `A₀ = logb Z (volume s₀)` (the scalar trap,
`L45_DESIGN.md` §1), while the second layer is read at the virtual pair `(A_v, a_v)`,
`A_v = logb Z (volume s)`. The balanced side has slope 1 in its volume argument, so the actual
amplitude `Z^{-a-side(A₀)}` equals `Z^{-a_v-side(A_v)}·Z^{(a_v-a)-(A₀-A_v)}`, and the hypothesis
`hshift : a_v - a ≤ A₀ - A_v + κ` turns the excess into `Z^κ`.

* `balanced_side_shift`: `side(A - δ) = side(A) - δ`.
* `shifted_high_mass_mx`: Collet's bound on the balanced first mass, read at the virtual side, for
  the shifted mass `Z^(a_v - a) * balancedFirstHighMass s₀ …`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalHighMass
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.MixedStep.Downstream
noncomputable section
open OAI OAI.SevenEighths Cycle61InitialMass OAI.SevenEighths.Record12518109Natural
open scoped SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open QRH.Record1252270103Source.High.CoupledFirst
local notation "O" => HeckeFamily.O

/-- The balanced side has slope one in the volume. -/
theorem balanced_side_shift (reflected : Bool) (A δ : ℝ) (v : Fin 5 → ℝ) :
    balancedGeometrySide reflected (A - δ) v = balancedGeometrySide reflected A v - δ := by
  cases reflected <;>
    simp only [balancedGeometrySide, QRH.Record12518109Assembly.balancedLeft,
      QRH.Record12518109Assembly.balancedRight, QRH.Record12518109Assembly.Scalar.left,
      QRH.Record12518109Assembly.Scalar.right, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The side at an arbitrary volume `Av`, compared with the side at `A`. -/
theorem balanced_side_eq (reflected : Bool) (A Av : ℝ) (v : Fin 5 → ℝ) :
    balancedGeometrySide reflected A v = balancedGeometrySide reflected Av v + (A - Av) := by
  have h := balanced_side_shift reflected A (A - Av) v
  rw [show A - (A - Av) = Av by ring] at h
  linarith

/-- The exponent conversion: with `hshift`, the actual exponent `-a - side(A₀)` is at most the
virtual exponent `-a_v - side(A_v)` plus `κ`. -/
theorem shift_exponent (reflected : Bool) (A₀ Av amp a κ : ℝ) (v : Fin 5 → ℝ)
    (hshift : amp - a ≤ A₀ - Av + κ) :
    (amp - a) - balancedGeometrySide reflected A₀ v ≤ κ - balancedGeometrySide reflected Av v := by
  rw [balanced_side_eq reflected A₀ Av v]
  linarith

/-- Collet's balanced first-mass bound (`actual_balanced_uniform_high_mass`) for the shifted mass
`Z^(amp - a) * mass(s₀)`, read at the virtual side `side(Av)` of the second-layer parent. -/
theorem shifted_high_mass_mx {α₀ : Type} [Fintype α₀] [DecidableEq α₀]
    (reflected : Bool) (N : ℕ) (lo ap : ℝ) (hlo : 0 < lo) (hap : 0 < ap)
    (s₀ : Input α₀) (modifier₀ : CenteredMomentAddedZeroUniform.Tuple α₀ → ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z ξ B ε : ℝ) (hZ : 1 < Z) (hK : 0 < Z^D)
    (hε : 0 ≤ ε) (hcard : Fintype.card α₀ ≤ N) (hlower : lo ≤ s₀.lower)
    (hs : Squarefree seed) (hz₁ : s₀.W₁ 0 = 0) (hz₂ : s₀.W₂ 0 = 0)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s₀ ≤ Z^B)
    (hs₁ : ∀ x, s₀.W₁ x ≠ 0 → ap ≤ x) (hs₂ : ∀ x, s₀.W₂ x ≠ 0 → ap ≤ x)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s₀ modifier₀ R seed (Z^D) Z ξ hK bin))
    (Av amp a κ : ℝ) (hshift : amp - a ≤ Real.logb Z (volume s₀.toData) - Av + κ) :
    Z^(amp - a) * balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ ε hK bin j ≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin * Z^(B*ε + κ) /
        Z^(balancedGeometrySide reflected Av (geometryExponents s₀ modifier₀ R seed (Z^D) Z ξ j.1.val)) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hm := actual_balanced_uniform_high_mass reflected N lo ap hlo hap s₀ modifier₀ R seed W D Z ξ B ε
    hZ hK hε hcard hlower hs hz₁ hz₂ hsource hs₁ hs₂ bin j
  set v := geometryExponents s₀ modifier₀ R seed (Z^D) Z ξ j.1.val
  set fac := geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
  have hfac : 0 ≤ fac := (geometry_high_factor_pos reflected _ bin
    (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
  have he := shift_exponent reflected (Real.logb Z (volume s₀.toData)) Av amp a κ v hshift
  have hpow : Z^(amp - a) / Z^(balancedGeometrySide reflected (Real.logb Z (volume s₀.toData)) v) ≤
      Z^κ / Z^(balancedGeometrySide reflected Av v) := by
    rw [← Real.rpow_sub hz, ← Real.rpow_sub hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le he
  have hp0 : 0 ≤ Z^(amp - a) := (Real.rpow_pos_of_pos hz _).le
  calc Z^(amp - a) * balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ ε hK bin j
      ≤ Z^(amp - a) * (fac * Z^(B*ε) /
          Z^(balancedGeometrySide reflected (Real.logb Z (volume s₀.toData)) v)) :=
        mul_le_mul_of_nonneg_left hm hp0
    _ = fac * Z^(B*ε) * (Z^(amp - a) /
          Z^(balancedGeometrySide reflected (Real.logb Z (volume s₀.toData)) v)) := by ring
    _ ≤ fac * Z^(B*ε) * (Z^κ / Z^(balancedGeometrySide reflected Av v)) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hfac (Real.rpow_pos_of_pos hz _).le)
    _ = fac * Z^(B*ε + κ) / Z^(balancedGeometrySide reflected Av v) := by
        rw [Real.rpow_add hz]; ring

end
end QRH.MixedStep.Downstream
#print axioms QRH.MixedStep.Downstream.balanced_side_shift
#print axioms QRH.MixedStep.Downstream.shifted_high_mass_mx
