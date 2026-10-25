/- Mixed source step, ledger: the transfer of width `δ` is Collet's step at virtual parameters.

The residual of a fourth-power transfer of a selected block of width `δ` has volume `A - δ`, MAIN
radius `μ + 4δ` and no cardinality factor. Collet's coordinate formula `actualHighCoordinates`
evaluated at the virtual pair `(A - δ, a + δ)` has the same radius, and its outside coordinate
differs from the actual one by exactly the side shift `labelSide (A - δ) = labelSide A - δ`. So
every generic payment lemma of Collet's step applies to the residual at
`(A - δ, a + δ, b - δ, F - 6δ)`. This file records the identities that make this precise and the
resulting mixed LOW payment. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalModifiedLowPayment
set_option autoImplicit false
namespace QRH.MixedStep.Ledger
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.Cycle61InitialMass OAI.SevenEighths.Record12518109Natural
open QRH.Record12518109Source OAI.SevenEighths.Cycle61Moment OAI.SevenEighths.CenteredMomentCanonicalFirst

/-- The MAIN radius at the virtual pair equals the actual residual radius `μ + 4δ`. -/
theorem virtual_coordinates (reflected left second : Bool) (l : FirstSourceLabel)
    (C₂ D₂ : Ideal HeckeFamily.O) (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve ε δ : ℝ) :
    let x := actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε
    let x' := actualHighCoordinates reflected left second l C₂ D₂ U Z M (A - δ) (a + δ) ξ reserve ε
    x' 0 = x 0 + 4*δ ∧ x' 1 = x 1 ∧ x' 2 = x 2 - 6*δ ∧ x' 3 = x 3 - δ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [actualHighCoordinates] <;> ring

/-- The side of a residual of volume `A - δ` is the original side minus `δ`. -/
theorem virtual_side (reflected : Bool) (l : FirstSourceLabel) (Z A δ : ℝ) :
    labelSide reflected l Z (A - δ) = labelSide reflected l Z A - δ := by
  unfold labelSide; ring

/-- The actual residual excess (outside coordinate `x 0 + 5δ`, original side) equals the virtual
one (outside coordinate `x 0 + 4δ`, side at `A - δ`). -/
theorem actual_eq_virtual_excess (x0 x1 x2 side δ : ℝ) :
    (x0 + 5*δ) + x1 + (x2 - 6*δ) - side = (x0 + 4*δ) + x1 + (x2 - 6*δ) - (side - δ) := by ring

/-- The RAW gap at the virtual parameters: amplifier `a + δ`, width `b - δ`, scale `F - 6δ`. -/
theorem virtual_raw_gap (a q b t B F lam δ : ℝ) (hlam : lam ≠ 0) :
    rawGap (a + δ) q (b - δ) t B (F - 6*δ) lam =
      rawGap a q b t B F lam + δ*(1 + q - 6*q*B/lam) := by
  unfold rawGap; field_simp; ring

/-- The mixed LOW gap in closed form: with `F = 1 - 6a` the virtual gap is
`a(1 - 6qβ) + δ(1 + q - 6qβ) - q(b + (t - B)/λ)` with `β = B/λ`. -/
theorem mixed_gap_closed (a q b t B lam δ : ℝ) (hlam : lam ≠ 0) :
    rawGap (a + δ) q (b - δ) t B ((1 - 6*a) - 6*δ) lam =
      a*(1 - 6*q*(B/lam)) + δ*(1 + q - 6*q*(B/lam)) - q*(b + (t - B)/lam) := by
  unfold rawGap; field_simp; ring

/-- The mixed LOW payment: the virtual gap reaches `r` iff
`a(1 - 6qβ) + δ(1 + q - 6qβ) ≥ q(b + (t - B)/λ) + r`. -/
theorem mixed_payment_iff (a q b t B lam δ r : ℝ) (hlam : lam ≠ 0) :
    r ≤ rawGap (a + δ) q (b - δ) t B ((1 - 6*a) - 6*δ) lam ↔
      q*(b + (t - B)/lam) + r ≤ a*(1 - 6*q*(B/lam)) + δ*(1 + q - 6*q*(B/lam)) := by
  rw [mixed_gap_closed a q b t B lam δ hlam]
  constructor <;> intro h <;> linarith

/-- Collet's exact first-cap identity, at the virtual parameters: the residual's RAW excess plus
its erasure over the residual live width `b - δ - f` is `−(pool gap + δ(1 + q − 6qB/λ))` plus
the same common terms. -/
theorem virtual_erasure_identity (a R E Bc Lc R0c g2 t2 b2 sigma q lam c B d b t f F δ : ℝ)
    (hlam : lam ≠ 0) :
    rawExcess (a + δ) R E Bc Lc R0c g2 t2 b2 sigma +
      q*(((b - δ) - f) - (B*((F - 6*δ) + Lc - R - max (c - d) 0) - (t - c + f))/lam) =
    -(rawGap a q b t B F lam + δ*(1 + q - 6*q*B/lam)) +
      rawCommon R Bc Lc R0c sigma q lam c B d - E - (b2 - g2 + t2) - (q - q/lam)*f := by
  rw [raw_erasure_identity (a + δ) R E Bc Lc R0c g2 t2 b2 sigma q lam c B d (b - δ) t f (F - 6*δ) hlam,
    virtual_raw_gap a q b t B F lam δ hlam]

/-- The HIGH joint excess at the virtual pair `(A - δ, a + δ)`: the amplifier term `a(5 - 6ρ)`
gains `δ(5 - 6ρ)` and the density term `ν A` loses `ν δ`. (In the cofactor coordinates the live
width also drops by `δ`, which cancels the `- ν δ`; the HIGH charge per unit of `δ` is then the
pool's `5 - 6ρ`, as the certificate gates assume.) -/
theorem virtual_high_excess (M A a ν c d p R E Bc Lc R0 b2 g2 t2 δ : ℝ) :
    highJointExcess M (A - δ) (a + δ) ν c d p R E Bc Lc R0 b2 g2 t2 =
      highJointExcess M A a ν c d p R E Bc Lc R0 b2 g2 t2 +
        δ*(5 - 6*LocalMoment.unmarkedDensity ν) - ν*δ := by
  unfold highJointExcess; ring

end
end QRH.MixedStep.Ledger
#print axioms QRH.MixedStep.Ledger.virtual_erasure_identity
#print axioms QRH.MixedStep.Ledger.mixed_payment_iff
