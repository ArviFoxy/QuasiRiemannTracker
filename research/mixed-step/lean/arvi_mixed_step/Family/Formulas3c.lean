/- The mixed-step face family with a variable cap: formulas.

As `Family/Formulas3.lean`, with the face cap given by a polynomial `cp` in the grid variable instead
of the constant `capM`: the face at `y` has cap `cp(y)`, its parent (the face at `y − Dy`) has cap
`cp(y − Dy)`. The cap enters the gates only through the parent's cap (scalar gates 6 and 7, the weak
cap, the HIGH parent's cap) and the width endpoint `b = cp(y)`. The selected width, the threshold, the
special sectors and the cell condition do not involve the cap and are reused unchanged. -/
import Submissions.arvi_mixed_step.Family.Formulas3

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite Poly

namespace Piece
variable (P : Piece) (cp : Poly)

/-- The mixed face at `y` with cap `cp(y)`. -/
def node3c (y : ℚ) : Source := ⟨P.B y, P.L y, eval cp y, P.q3 y, feeE, feeR, feeF⟩

theorem crossing3c_eq (y : ℚ) (hH : P.H * P.Dy ≠ 0) (hL : P.L (y - P.Dy) ≠ P.L y) :
    crossing (P.node3c cp y) (P.node3c cp (y - P.Dy)) = P.s y := by
  have h := P.crossing_eq y hH hL
  simp only [crossing, node, node3c] at h ⊢
  exact h

theorem sourceDen3c_eq (y : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) : sourceDen3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) = den := by
  simp only [sourceDen3, node3c, q3]
  field_simp
  ring

theorem sourceT3c_eq (y b : ℚ) : sourceT (P.node3c cp y) b = P.tAt y b := by
  simp [sourceT, node3c, tAt]

theorem sourceDc_eq (y b : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) :
    sourceD (P.node3c cp y) (P.node3c cp (y - P.Dy)) b = P.NdAt y b / P.DdAt y := by
  have hden : den ≠ 0 := den_pos.ne'
  rw [sourceD, sourceDen3c_eq P cp y hS hL]
  simp only [sourceX0, sourceT, node3c, q3, NdAt, DdAt, tAt]
  field_simp
  ring

end Piece

/-! ## The gates as functions of the atoms (parent cap `c0`) -/

/-- `sg3At` with the parent's cap `c0` in place of `capM`. -/
def sg3Atc (A D t b B0 L0 c0 : ℚ) : Fin 18 → ℚ :=
  ![den, b - 2*feeE, feeR, 1/75 - (feeR + A/D),
    (1 - 6*feeR - 6*(A/D)) - (t + b)/2 - 4*feeE,
    B0*(1 - 6*feeR - 6*(A/D)) - t - b - 4*feeE,
    1 - (1 - den)*L0/(6*B0 - L0)*c0,
    feeR - ((1 - den)*L0/(6*B0 - L0)*B0/L0 + (1 - den)*L0/(6*B0 - L0)*c0 + 4)*feeE - 10*feeE,
    feeR - 20*feeE, 49/100 - (9/2)*b,
    1 - (49/100 - (9/2)*b) - 1/2 - (9/2)*b - 10*feeE,
    5/6 + (499/1000)*(49/100 - (9/2)*b) - (t + b) - 9*(feeR + A/D) - feeF,
    1 - (t + b) - 5*(feeR + A/D) - feeF, 1 - 1/50 - (t + b) - 4*(feeR + A/D) - feeF,
    1 - 1/50 - (t + b) - (9/2)*(feeR + A/D) - feeF,
    (49/100 - (9/2)*b) - 7*(feeR + A/D) - feeF,
    b - 2*feeE - A/D, A/D + 1/10^30]

/-- The cleared scalar gates with the parent's cap `c0`. -/
def sg3NAtc (A D t b B0 L0 c0 : ℚ) : Fin 18 → ℚ :=
  let Lr := 49/100 - (9/2)*b
  let T := t + b
  ![den*D, (b - 2*feeE)*D, feeR*D, (1/75 - feeR)*D - A,
    (1 - 6*feeR - 4*feeE - T/2)*D - 6*A,
    B0*((1 - 6*feeR)*D - 6*A) - (T + 4*feeE)*D,
    D - (1 - den)*den*(c0*L0),
    (feeR - 14*feeE)*D - (1 - den)*den*feeE*(B0 + c0*L0),
    (feeR - 20*feeE)*D, Lr*D, (1/100 - 10*feeE)*D,
    (5/6 - 9*feeR - feeF + (499/1000)*Lr - T)*D - 9*A,
    (1 - 5*feeR - feeF - T)*D - 5*A,
    (49/50 - 4*feeR - feeF - T)*D - 4*A,
    (49/50 - (9/2)*feeR - feeF - T)*D - (9/2)*A,
    (Lr - (7*feeR + feeF))*D - 7*A,
    (b - 2*feeE)*D - A, A + (1/10^30)*D]

theorem sg3Atc_mul (A D t b B0 L0 c0 : ℚ) (hS : 6*B0 - L0 ≠ 0) (hL : L0 ≠ 0)
    (hD : D = den*(6*B0 - L0)) (j : Fin 18) :
    sg3Atc A D t b B0 L0 c0 j * D = sg3NAtc A D t b B0 L0 c0 j := by
  have hden : den ≠ 0 := den_pos.ne'
  have hS' : B0*6 - L0 ≠ 0 := by rwa [mul_comm]
  subst hD
  fin_cases j <;> simp [sg3Atc, sg3NAtc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first | (field_simp; ring) | field_simp | ring

/-- The weak cap times `D · L₀`, parent cap `c0`. -/
def weak3NAtc (A D t B0 L0 c0 : ℚ) : ℚ :=
  c0*L0*((1 - 6*feeR)*D - 6*A) - (B0*((1 - 6*feeR)*D - 6*A) - t*D)

theorem weak3c_mul (A D t B0 L0 c0 : ℚ) (hD : D ≠ 0) (hL : L0 ≠ 0) :
    (c0*(1 - 6*feeR - 6*(A/D)) - (B0*(1 - 6*feeR - 6*(A/D)) - t)/L0) * (D * L0) =
      weak3NAtc A D t B0 L0 c0 := by
  simp only [weak3NAtc]; first | (field_simp; ring) | field_simp

namespace Piece
variable (P : Piece) (cp : Poly)

theorem scalarGate3c_at (y b : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) :
    scalarGate3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) b =
      sg3Atc (P.NdAt y b) (P.DdAt y) (P.tAt y b) b (P.B (y - P.Dy)) (P.L (y - P.Dy))
        (eval cp (y - P.Dy)) := by
  funext j
  have hD := sourceDc_eq P cp y b hS hL
  have hden := sourceDen3c_eq P cp y hS hL
  simp only [scalarGate3, sg3Atc, sourceF3, hD, hden, sourceT3c_eq]
  rfl

theorem weakCap3c_at (y b : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) :
    weakCap3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) b =
      eval cp (y - P.Dy)*(1 - 6*feeR - 6*(P.NdAt y b/P.DdAt y)) -
        (P.B (y - P.Dy)*(1 - 6*feeR - 6*(P.NdAt y b/P.DdAt y)) - P.tAt y b)/P.L (y - P.Dy) := by
  simp only [weakCap3, sourceF3, sourceDc_eq P cp y b hS hL, sourceT3c_eq]
  rfl

theorem densityGate3c_at (y b ν : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) (j : Fin 3) :
    densityGate3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) b ν j =
      sec3At (P.NdAt y b) (P.DdAt y) (P.tAt y b) b j ν := by
  have hD := sourceDc_eq P cp y b hS hL
  simp only [densityGate3, sourceAmp3, sourceF3, hD, sourceT3c_eq]
  fin_cases j <;> rfl

theorem sourceF3c_at (y b : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) :
    sourceF3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) b = 1 - 6*feeR - 6*(P.NdAt y b/P.DdAt y) := by
  simp only [sourceF3, sourceDc_eq P cp y b hS hL]
  rfl

/-! ## Polynomials -/

/-- The parent's cap as a polynomial in `y`. -/
def cap0P : Poly := shift cp (-P.Dy)

@[simp] theorem eval_cap0P (y : ℚ) : eval (P.cap0P cp) y = eval cp (y - P.Dy) := by
  simp [cap0P]; ring_nf

/-- The two width endpoints: the crossing `s(y)` and the cap `cp(y)`. -/
def endP3c (e : Fin 2) : Poly := ![P.sp, cp] e

/-- The cap guards: `cp > 0`, `1 − cp > 0`, `cp − s > 0`, `cp(· − Dy) − s > 0`,
`1 − cp(· − Dy) > 0`. -/
def capFieldP : Fin 5 → Poly :=
  ![cp, sub [1] cp, sub cp P.sp, sub (P.cap0P cp) P.sp, sub [1] (P.cap0P cp)]

/-- `sg3NAtc` as a polynomial in `y`. -/
def sg3Nc (b : Poly) (j : Fin 18) : Poly :=
  let A := P.NdP b
  let D := P.DdP
  let B0 := P.B0p
  let L0 := P.L0p
  let C0 := P.cap0P cp
  let T := add (P.tP b) b
  let Lr := LrefP b
  ![smul den D, mul (sub b [2*feeE]) D, smul feeR D, sub (smul (1/75 - feeR) D) A,
    sub (mul (sub [1 - 6*feeR - 4*feeE] (smul (1/2) T)) D) (smul 6 A),
    sub (mul B0 (sub (smul (1 - 6*feeR) D) (smul 6 A))) (mul (add T [4*feeE]) D),
    sub D (smul ((1 - den)*den) (mul C0 L0)),
    sub (smul (feeR - 14*feeE) D) (smul ((1 - den)*den*feeE) (add B0 (mul C0 L0))),
    smul (feeR - 20*feeE) D, mul Lr D, smul (1/100 - 10*feeE) D,
    sub (mul (sub (add [5/6 - 9*feeR - feeF] (smul (499/1000) Lr)) T) D) (smul 9 A),
    sub (mul (sub [1 - 5*feeR - feeF] T) D) (smul 5 A),
    sub (mul (sub [49/50 - 4*feeR - feeF] T) D) (smul 4 A),
    sub (mul (sub [49/50 - (9/2)*feeR - feeF] T) D) (smul (9/2) A),
    sub (mul (sub Lr [7*feeR + feeF]) D) (smul 7 A),
    sub (mul (sub b [2*feeE]) D) A, add A (smul (1/10^30) D)] j

theorem eval_sg3Nc (b : Poly) (y : ℚ) (j : Fin 18) :
    eval (P.sg3Nc cp b j) y = sg3NAtc (P.NdAt y (eval b y)) (P.DdAt y) (P.tAt y (eval b y))
      (eval b y) (P.B (y - P.Dy)) (P.L (y - P.Dy)) (eval cp (y - P.Dy)) j := by
  fin_cases j <;>
    simp [sg3Nc, sg3NAtc, LrefP, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

def weak3Nc (b : Poly) : Poly :=
  let A := P.NdP b
  let D := P.DdP
  let FD := sub (smul (1 - 6*feeR) D) (smul 6 A)
  sub (mul (P.cap0P cp) (mul P.L0p FD)) (sub (mul P.B0p FD) (mul (P.tP b) D))

theorem eval_weak3Nc (b : Poly) (y : ℚ) :
    eval (P.weak3Nc cp b) y = weak3NAtc (P.NdAt y (eval b y)) (P.DdAt y) (P.tAt y (eval b y))
      (P.B (y - P.Dy)) (P.L (y - P.Dy)) (eval cp (y - P.Dy)) := by
  simp [weak3Nc, weak3NAtc]; ring

end Piece

end QRH.RepeatedMarks.Faceless
