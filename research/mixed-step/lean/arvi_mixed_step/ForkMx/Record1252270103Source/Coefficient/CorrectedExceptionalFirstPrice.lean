/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Coefficient.CorrectedExceptionalFirstPrice
(Hailey Collet). Original note: the actual first common
geometry pays an inverse radical and two-thirds of the chosen common width; centering then pays the
advertised 499/1000 gate.

`node_centered_payment` with two parents and two amplitudes (the MAIN complement twin, design
`L45_DESIGN.md` §3 F6). The first-layer scalar is read at the original volume `A₀`
(`Scalar.left A₀`), the child volume and the MAIN radius at the second-layer volume `Av` with the
radius amplitude `amp` (= `a_v`), and the pool reciprocal at the actual pool amplitude `a`.
With `hshift : amp - a ≤ A₀ - Av + κ` the exponent exceeds Collet's (at `(A₀, a)`) by at most
`3(amp - a) + 2κ` (the design's `+3δ`); the mixed centered gate `T + 9·Amix + fee < 5/6 + 0.499·Lref`
(`MixedGeometry.centered_twin`, `Amix = r + d`) pays it, with the target `-fee - 4·Amix`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedExceptionalFirstPrice

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section

/-- The balanced left side has slope one in the volume. -/
theorem scalar_left_shift_mx (A₀ Av c d R E : ℝ) :
    QRH.Record12518109Assembly.Scalar.left A₀ c d R E =
      QRH.Record12518109Assembly.Scalar.left Av c d R E + (A₀ - Av) := by
  unfold QRH.Record12518109Assembly.Scalar.left
  ring

/-- **Mixed centered node payment.** `Lref = 49/100 - K·b`, `T = t + b`, `fee` the high fee,
`Amix = r + d` the mixed amplifier; `a` the actual pool amplitude, `amp` the MAIN-radius amplitude
of the second layer, `A₀`/`Av` the first/second-layer log volumes. -/
theorem node_centered_payment_mx (Lref fee T Amix a amp κ A₀ Av c d R E p omega loss
    plainError : ℝ)
    (hgate : T + 9*Amix + fee < 5/6 + (499/1000)*Lref) (hc : 0≤c)
    (hcommon : commonPrice c d R E+p≤-2*c/3)
    (hA : A₀≤T+plainError) (hshift : amp-a≤A₀-Av+κ) (hamp : amp≤Amix)
    (herr : plainError+5*omega/6+loss+2*κ≤2*Amix-a) :
    (Av-c)/3+5*(2*Av-1+R+E-c-d+max (d-c) 0+6*amp+omega)/6-
      QRH.Record12518109Assembly.Scalar.left A₀ c d R E+p-
      2*(499/1000)*max (Lref-c) 0-a+loss<
      -fee-4*Amix := by
  rw [scalar_left_shift_mx A₀ Av c d R E]
  have hid := first_exponent_identity Av 1 c d R E amp omega
  have hcenter := centered_common_payment Lref c (499/1000) hc (by norm_num) (by norm_num)
  linarith

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.scalar_left_shift_mx
#print axioms QRH.Record1252270103Source.ExceptionalPrice.node_centered_payment_mx
