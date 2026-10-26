/- The mixed-step face family with a variable cap: the uniform HIGH gate.

As `Family/High3.lean`, with the HIGH parent's cap a polynomial `HC` (the parent's cap
`cp(y − Dy)`) in the cleared samples, instead of the constant `capM`. -/
import Submissions.arvi_mixed_step.Family.Formulas3c
import Submissions.arvi_mixed_step.Family.High3

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite Poly

/-- `gateGDnP` with the HIGH parent's cap a polynomial `HC`. -/
def gateGDnPc (Dn Na NF TD SD : Poly) (fee K : ℚ) (B L HC : Poly) (ν p : ℚ) (k : Branch) : Poly :=
  let bI : Fin 2 → Poly := ![smul (2*p*K) SD, smul p NF]
  let hP : Fin 3 → Poly := ![smul (2*p) SD, mul (smul (2*p) HC) NF, mul (smul (2*p) B) NF]
  let base := add (smul (15 - 6*ν) (sub Na (smul ν TD)))
    (add (smul ν (sub (smul 10 Dn) (smul 60 Na)))
      (add (smul ((15 - 6*ν)*(1 - 2*p)*ν) SD) (add (smul (-10*ν) NF) (smul (-fee*(15 - 6*ν)) Dn))))
  let N := add (smul 10 (mul NF (mul (dIP p k.1) (ePP p L k.2))))
    (smul (5 - 6*ν) (add (smul 2 (mul (ePP p L k.2) (bI k.1))) (mul (dIP p k.1) (hP k.2))))
  add (mul (gateMP ν p L k) base) (smul (ν*(15 - 6*ν)) N)

theorem eval_gateGDnPc (Dn Na NF TD SD : Poly) (fee K : ℚ) (B L HC : Poly) (ν p : ℚ) (k : Branch)
    (y : ℚ) (hD : eval Dn y ≠ 0) :
    eval (gateGDnPc Dn Na NF TD SD fee K B L HC ν p k) y =
      eval Dn y * gateG (eval Na y / eval Dn y) (eval TD y / eval Dn y) (eval SD y / eval Dn y)
        (eval NF y / eval Dn y) fee K (eval B y) (eval L y) (eval HC y) ν p k := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [gateGDnPc, gateMP, dIP, ePP, gPP, gateG, gateM, gateN, dI, eP, gP, bI, hP,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    field_simp <;> ring

namespace Piece
variable (P : Piece) (cp : Poly)

/-- `Dd · highGate3` at the sample `(ν, p)`, variable cap. -/
def valP3c (b : Poly) (k : Branch) (ν p : ℚ) : Poly :=
  let A := P.NdP b
  let D := P.DdP
  let AD := add (smul feeR D) A
  let NF := sub (smul (1 - 6*feeR - feeE) D) (smul 6 A)
  let TD := mul (add (P.tP b) b) D
  let SD := sub (mul (sub b [2*feeE]) D) A
  trim (gateGDnPc D AD NF TD SD feeF 8 P.B0p P.L0p (P.cap0P cp) ν p k)

theorem eval_valP3c (b : Poly) (k : Branch) (ν p y : ℚ)
    (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0) (hL : P.L (y - P.Dy) ≠ 0) :
    eval (P.valP3c cp b k ν p) y =
      P.DdAt y * highGate3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) (P.node3c cp (y - P.Dy)) 8
        (eval b y) ν p k := by
  have hD : P.DdAt y ≠ 0 := mul_ne_zero den_pos.ne' hS
  have hD' : eval P.DdP y ≠ 0 := by simpa using hD
  simp only [valP3c, eval_trim]
  rw [eval_gateGDnPc _ _ _ _ _ _ _ _ _ _ _ _ _ y hD']
  rw [highGate3, sourceAmp3, sourceF3, sourceDc_eq P cp y _ hS hL, sourceT3c_eq]
  simp only [eval_add, eval_sub, eval_smul, eval_mul, eval_tP, eval_NdP, eval_DdP, eval_B0p,
    eval_L0p, eval_cap0P, eval_nil, eval_cons, mul_zero, add_zero]
  have e1 : (feeR * P.DdAt y + P.NdAt y (eval b y)) / P.DdAt y =
      (P.node3c cp y).lowFee + P.NdAt y (eval b y) / P.DdAt y := by
    simp only [node3c]; field_simp
  have e2 : (P.tAt y (eval b y) + eval b y) * P.DdAt y / P.DdAt y =
      P.tAt y (eval b y) + eval b y := by field_simp
  have e3 : ((eval b y - 2 * feeE) * P.DdAt y - P.NdAt y (eval b y)) / P.DdAt y =
      eval b y - 2 * (P.node3c cp y).allowance - P.NdAt y (eval b y) / P.DdAt y := by
    simp only [node3c]; field_simp
  have e4 : ((1 - 6 * feeR - feeE) * P.DdAt y - 6 * P.NdAt y (eval b y)) / P.DdAt y =
      1 - 6 * (P.node3c cp y).lowFee - 6 * (P.NdAt y (eval b y) / P.DdAt y) -
        (P.node3c cp y).allowance := by
    simp only [node3c]; field_simp; ring
  rw [e1, e2, e3, e4]
  rfl

/-- The `(u, p)` coefficients of `S³ · Dd · highGate3` at width endpoint `b`, branch `k`. -/
def highU3c (b : Poly) (k : Branch) (a j : Fin 4) : Poly :=
  cuP (bicubicP (fun ν p => P.valP3c cp b k ν p)) P.alpha3P P.beta3P P.S3P a j

theorem high_pos_of_U3c (b : Poly) (k : Branch) (y : ℚ)
    (hU0 : ∀ u p : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ p → p ≤ 1/2 →
      0 < ∑ i : Fin 4, ∑ j : Fin 4, ((eval (P.highU3c cp b k i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ))
    (hS : 0 < 6 * P.B (y - P.Dy) - P.L (y - P.Dy)) (hL : 0 < P.L (y - P.Dy)) (hq : P.q3 y < 3/4)
    (ν p : ℝ) (hν : ν ∈ Set.Icc ((P.q3 y : ℚ) : ℝ) (3/4)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < highGate3Real (P.node3c cp y) (P.node3c cp (y - P.Dy)) (P.node3c cp (y - P.Dy)) 8
      ((eval b y : ℚ) : ℝ) ν p k := by
  set B0 := P.B (y - P.Dy) with hB0
  set L0 := P.L (y - P.Dy) with hL0
  set S := 6 * B0 - L0 with hSdef
  set c : Fin 4 → Fin 4 → ℚ :=
    highCoeffs3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) (P.node3c cp (y - P.Dy)) 8 (eval b y) k
    with hcdef
  set Dn := P.DdAt y with hDn
  have hDn0 : 0 < Dn := by simp only [hDn, Piece.DdAt]; exact mul_pos den_pos hS
  have hsamp : ∀ i j, eval (bicubicP (fun ν p => P.valP3c cp b k ν p) i j) y = Dn * c i j := by
    intro i j
    rw [eval_bicubicP]
    simp only [eval_valP3c P cp b k _ _ y hS.ne' hL.ne', hcdef, highCoeffs3]
    exact bicubic_smul _ _ i j
  have hU : ∀ a j, eval (P.highU3c cp b k a j) y =
      Dn * cuR c (eval P.alpha3P y) (eval P.beta3P y) (eval P.S3P y) a j := by
    intro a j
    rw [highU3c, eval_cuP]
    simp only [hsamp]
    exact cuR_smul Dn c _ _ _ a j
  have hα : eval P.alpha3P y = (1 - den) * L0 := by
    simp only [alpha3P, eval_smul, eval_L0p]; rfl
  have hS3 : eval P.S3P y = S := by
    simp only [S3P, eval_sub, eval_smul, eval_B0p, eval_L0p]; rfl
  have hβ : eval P.beta3P y = 3/4 * S - (1 - den) * L0 := by
    simp only [beta3P, eval_sub, eval_smul, hS3, hα]
  have hqy : P.q3 y = (1 - den) * L0 / S := rfl
  have hw : (0:ℝ) < 3/4 - (P.q3 y : ℝ) := by
    have : ((P.q3 y : ℚ) : ℝ) < ((3/4 : ℚ) : ℝ) := Rat.cast_lt.mpr hq
    push_cast at this; linarith
  set u : ℝ := (ν - (P.q3 y : ℝ))/(3/4 - (P.q3 y : ℝ)) with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith [hν.1]) hw.le
  have hu1 : u ≤ 1 := (div_le_one hw).mpr (by linarith [hν.2])
  have hSr : (0:ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hνu : ν = (((1 - den) * L0 : ℚ) + u * ((3/4 * S - (1 - den) * L0 : ℚ) : ℝ)) / ((S : ℚ) : ℝ) := by
    have hD0 : ((S : ℚ) : ℝ) ≠ 0 := hSr.ne'
    have hβw : ((3/4 * S - (1 - den) * L0 : ℚ) : ℝ) = (3/4 - (P.q3 y : ℝ)) * ((S : ℚ) : ℝ) := by
      rw [hqy]; push_cast; field_simp
    have hαq : (((1 - den) * L0 : ℚ) : ℝ) = (P.q3 y : ℝ) * ((S : ℚ) : ℝ) := by
      rw [hqy]; push_cast; field_simp
    have huw : u * (3/4 - (P.q3 y : ℝ)) = ν - (P.q3 y : ℝ) := by
      rw [hu]; exact div_mul_cancel₀ _ hw.ne'
    rw [hβw, hαq, eq_div_iff hD0]
    linear_combination (-(((S : ℚ) : ℝ))) * huw
  have hpos := hU0 u p hu0 hu1 hp.1 hp.2
  simp only [hU] at hpos
  rw [highGate3Real_rat]
  have hDnr : (0:ℝ) < (Dn : ℝ) := by exact_mod_cast hDn0
  have key : ((S : ℚ) : ℝ) ^ 3 * ((Dn : ℚ) : ℝ) *
      ∑ i : Fin 4, ∑ j : Fin 4, ((c i j : ℚ) : ℝ) * ν ^ (i:ℕ) * p ^ (j:ℕ) =
      ∑ a : Fin 4, ∑ j : Fin 4,
        ((Dn * cuR c (eval P.alpha3P y) (eval P.beta3P y) (eval P.S3P y) a j : ℚ) : ℝ)
          * u ^ (a:ℕ) * p ^ (j:ℕ) := by
    rw [hα, hβ, hS3, hνu]
    have h6 : ((S : ℚ) : ℝ) ≠ 0 := hSr.ne'
    rw [mul_comm (((S : ℚ) : ℝ) ^ 3) _, mul_assoc,
      cuR_eq (fun i j => ((c i j : ℚ) : ℝ)) _ _ _ u p h6, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    push_cast [cuR_cast]
    ring
  have hfac : (0:ℝ) < ((S : ℚ) : ℝ) ^ 3 * ((Dn : ℚ) : ℝ) := by positivity
  have : 0 < ((S : ℚ) : ℝ) ^ 3 * ((Dn : ℚ) : ℝ) *
      ∑ i : Fin 4, ∑ j : Fin 4, ((c i j : ℚ) : ℝ) * ν ^ (i:ℕ) * p ^ (j:ℕ) := by
    rw [key]; exact hpos
  exact pos_of_mul_pos_right this hfac.le

end Piece

end QRH.RepeatedMarks.Faceless
