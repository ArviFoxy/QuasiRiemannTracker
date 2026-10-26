/- The mixed-step face family: formulas.

The pieces are those of the faceless family (`Faceless.Piece`: `s = σ + H y`, the envelope
polynomial `E(y)`, the secant faces `B(y), L(y)` over one grid step `Dy`). For the mixed step the
threshold is set from the previous face,

  `q(y) = (1 − den) L₀/(6 B₀ − L₀)`,   `B₀ = B(y − Dy)`, `L₀ = L(y − Dy)`,

so the mixed LOW denominator `den3 = 1 + q − 6 q B₀/L₀` is `den` at every step, and the selected
width is `δ = Nd/Dd` with

  `Nd = (1 − den)(L₀ b + t − B₀ + 6 B₀ r)`,  `Dd = den (6 B₀ − L₀)`.

Every gate of `SourceValid3` for the step `node3 (y − Dy) → node3 y`, times `Dd`, is a polynomial in
the atoms `Nd, Dd, t, b, B₀, L₀`. This file has the identities and the polynomials in `y`. -/
import Submissions.arvi_mixed_step.Finite.HighGate3
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Faceless.Validity
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Faceless.TreeZ

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite Poly

/-- The common cap of the mixed faces. -/
def capM : ℚ := 3/40

theorem den_pos : (0:ℚ) < den := by norm_num [den]

namespace Piece
variable (P : Piece)

/-- The mixed threshold. -/
def q3 (y : ℚ) : ℚ := (1 - den) * P.L (y - P.Dy) / (6 * P.B (y - P.Dy) - P.L (y - P.Dy))

/-- The mixed face at `y`. -/
def node3 (y : ℚ) : Source := ⟨P.B y, P.L y, capM, P.q3 y, feeE, feeR, feeF⟩

theorem crossing3_eq (y : ℚ) (hH : P.H * P.Dy ≠ 0) (hL : P.L (y - P.Dy) ≠ P.L y) :
    crossing (P.node3 y) (P.node3 (y - P.Dy)) = P.s y := by
  have h := P.crossing_eq y hH hL
  simp only [crossing, node, node3] at h ⊢
  exact h

theorem sourceDen3_eq (y : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) : sourceDen3 (P.node3 y) (P.node3 (y - P.Dy)) = den := by
  simp only [sourceDen3, node3, q3]
  field_simp
  ring

theorem sourceT3_eq (y b : ℚ) : sourceT (P.node3 y) b = P.tAt y b := by
  simp [sourceT, node3, tAt]

/-- The numerator of the selected width. -/
def NdAt (y b : ℚ) : ℚ :=
  (1 - den) * (P.L (y - P.Dy) * b + P.tAt y b - P.B (y - P.Dy) + 6 * feeR * P.B (y - P.Dy))

/-- The denominator of the selected width. -/
def DdAt (y : ℚ) : ℚ := den * (6 * P.B (y - P.Dy) - P.L (y - P.Dy))

theorem sourceD_eq (y b : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) :
    sourceD (P.node3 y) (P.node3 (y - P.Dy)) b = P.NdAt y b / P.DdAt y := by
  have hden : den ≠ 0 := den_pos.ne'
  rw [sourceD, sourceDen3_eq P y hS hL]
  simp only [sourceX0, sourceT, node3, q3, NdAt, DdAt, tAt]
  field_simp
  ring

/-! ### Polynomial versions -/

def NdP (b : Poly) : Poly :=
  smul (1 - den) (add (add (mul P.L0p b) (sub (P.tP b) P.B0p)) (smul (6 * feeR) P.B0p))

def DdP : Poly := smul den (sub (smul 6 P.B0p) P.L0p)

@[simp] theorem eval_NdP (b : Poly) (y : ℚ) : eval (P.NdP b) y = P.NdAt y (eval b y) := by
  simp only [NdP, NdAt, eval_smul, eval_add, eval_mul, eval_sub, eval_tP, eval_B0p, eval_L0p]
  ring

@[simp] theorem eval_DdP (y : ℚ) : eval P.DdP y = P.DdAt y := by
  simp only [DdP, DdAt, eval_smul, eval_sub, eval_B0p, eval_L0p]

end Piece

/-! ## The gates as functions of the atoms -/

/-- The 18 gates of `scalarGate3` with `δ = A/D`, `sourceT = t`, `q = (1 − den) L₀/(6 B₀ − L₀)`. -/
def sg3At (A D t b B0 L0 : ℚ) : Fin 18 → ℚ :=
  ![den, b - 2*feeE, feeR, 1/75 - (feeR + A/D),
    (1 - 6*feeR - 6*(A/D)) - (t + b)/2 - 4*feeE,
    B0*(1 - 6*feeR - 6*(A/D)) - t - b - 4*feeE,
    1 - (1 - den)*L0/(6*B0 - L0)*capM,
    feeR - ((1 - den)*L0/(6*B0 - L0)*B0/L0 + (1 - den)*L0/(6*B0 - L0)*capM + 4)*feeE - 10*feeE,
    feeR - 20*feeE, 49/100 - (9/2)*b,
    1 - (49/100 - (9/2)*b) - 1/2 - (9/2)*b - 10*feeE,
    5/6 + (499/1000)*(49/100 - (9/2)*b) - (t + b) - 9*(feeR + A/D) - feeF,
    1 - (t + b) - 5*(feeR + A/D) - feeF, 1 - 1/50 - (t + b) - 4*(feeR + A/D) - feeF,
    1 - 1/50 - (t + b) - (9/2)*(feeR + A/D) - feeF,
    (49/100 - (9/2)*b) - 7*(feeR + A/D) - feeF,
    b - 2*feeE - A/D, A/D + 1/10^30]

/-- The cleared scalar gates `sg3At · D` (with `D = den (6 B₀ − L₀)`, so `q D = (1 − den) den L₀`). -/
def sg3NAt (A D t b B0 L0 : ℚ) : Fin 18 → ℚ :=
  let Lr := 49/100 - (9/2)*b
  let T := t + b
  ![den*D, (b - 2*feeE)*D, feeR*D, (1/75 - feeR)*D - A,
    (1 - 6*feeR - 4*feeE - T/2)*D - 6*A,
    B0*((1 - 6*feeR)*D - 6*A) - (T + 4*feeE)*D,
    D - (1 - den)*den*capM*L0,
    (feeR - 14*feeE)*D - (1 - den)*den*feeE*(B0 + capM*L0),
    (feeR - 20*feeE)*D, Lr*D, (1/100 - 10*feeE)*D,
    (5/6 - 9*feeR - feeF + (499/1000)*Lr - T)*D - 9*A,
    (1 - 5*feeR - feeF - T)*D - 5*A,
    (49/50 - 4*feeR - feeF - T)*D - 4*A,
    (49/50 - (9/2)*feeR - feeF - T)*D - (9/2)*A,
    (Lr - (7*feeR + feeF))*D - 7*A,
    (b - 2*feeE)*D - A, A + (1/10^30)*D]

theorem sg3At_mul (A D t b B0 L0 : ℚ) (hS : 6*B0 - L0 ≠ 0) (hL : L0 ≠ 0)
    (hD : D = den*(6*B0 - L0)) (j : Fin 18) :
    sg3At A D t b B0 L0 j * D = sg3NAt A D t b B0 L0 j := by
  have hden : den ≠ 0 := den_pos.ne'
  have hS' : B0*6 - L0 ≠ 0 := by rwa [mul_comm]
  subst hD
  fin_cases j <;> simp [sg3At, sg3NAt, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first | (field_simp; ring) | field_simp | ring

/-- The weak cap times `D · L₀`. -/
def weak3NAt (A D t B0 L0 : ℚ) : ℚ :=
  capM*L0*((1 - 6*feeR)*D - 6*A) - (B0*((1 - 6*feeR)*D - 6*A) - t*D)

theorem weak3_mul (A D t B0 L0 : ℚ) (hD : D ≠ 0) (hL : L0 ≠ 0) :
    (capM*(1 - 6*feeR - 6*(A/D)) - (B0*(1 - 6*feeR - 6*(A/D)) - t)/L0) * (D * L0) =
      weak3NAt A D t B0 L0 := by
  simp only [weak3NAt]; first | (field_simp; ring) | field_simp

/-- The special sectors of `densityGate3` (`fixed, core, tiny`) with `δ = A/D`. -/
def sec3At (A D t b : ℚ) (j : Fin 3) (ν : ℚ) : ℚ :=
  ![((feeR + A/D) - ν*(t + b))*(15 - 6*ν) + (10 - 60*(feeR + A/D))*ν +
      (ν*(1 - 6*feeR - 6*(A/D) - feeE)/2 - (1 - ν)*b - feeF)*(15 - 6*ν),
    ((feeR + A/D) - ν*(t + b))*(15 - 6*ν) + (10 - 60*(feeR + A/D))*ν +
      ((5/6)*(1 - 6*feeR - 6*(A/D) - feeE) - (1 - ν)*b - feeF)*(15 - 6*ν) -
      10*ν*(1 - 6*feeR - 6*(A/D) - feeE),
    ((feeR + A/D) - ν*(t + b))*(15 - 6*ν) + (10 - 60*(feeR + A/D))*ν +
      (ν*((1 - 6*feeR - 6*(A/D) - feeE) - 1/50)/2 - (1 - ν)*b - feeF)*(15 - 6*ν) -
      10*ν*(1/50)] j

/-- `D · sec3At`, cleared. -/
def sec3NAt (A D t b : ℚ) (j : Fin 3) (ν : ℚ) : ℚ :=
  let AD := feeR*D + A
  let FD := (1 - 6*feeR - feeE)*D - 6*A
  let tt := 15 - 6*ν
  let HD := (AD - ν*((t + b)*D))*tt + (10*D - 60*AD)*ν
  ![HD + (ν/2*FD - (1 - ν)*(b*D) - feeF*D)*tt,
    HD + ((5/6)*FD - (1 - ν)*(b*D) - feeF*D)*tt - 10*ν*FD,
    HD + (ν/2*(FD - D/50) - (1 - ν)*(b*D) - feeF*D)*tt - 10*ν/50*D] j

theorem sec3At_mul (A D t b : ℚ) (hD : D ≠ 0) (j : Fin 3) (ν : ℚ) :
    sec3At A D t b j ν * D = sec3NAt A D t b j ν := by
  fin_cases j <;> simp [sec3At, sec3NAt, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first | (field_simp; ring) | field_simp | ring

namespace Piece
variable (P : Piece)

/-! ## The gates of the family in terms of the atoms -/

theorem scalarGate3_at (y b : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) :
    scalarGate3 (P.node3 y) (P.node3 (y - P.Dy)) b =
      sg3At (P.NdAt y b) (P.DdAt y) (P.tAt y b) b (P.B (y - P.Dy)) (P.L (y - P.Dy)) := by
  funext j
  have hD := sourceD_eq P y b hS hL
  have hden := sourceDen3_eq P y hS hL
  simp only [scalarGate3, sg3At, sourceF3, hD, hden, sourceT3_eq]
  rfl

theorem weakCap3_at (y b : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) :
    weakCap3 (P.node3 y) (P.node3 (y - P.Dy)) b =
      capM*(1 - 6*feeR - 6*(P.NdAt y b/P.DdAt y)) -
        (P.B (y - P.Dy)*(1 - 6*feeR - 6*(P.NdAt y b/P.DdAt y)) - P.tAt y b)/P.L (y - P.Dy) := by
  simp only [weakCap3, sourceF3, sourceD_eq P y b hS hL, sourceT3_eq]
  rfl

theorem densityGate3_at (y b ν : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) (j : Fin 3) :
    densityGate3 (P.node3 y) (P.node3 (y - P.Dy)) b ν j =
      sec3At (P.NdAt y b) (P.DdAt y) (P.tAt y b) b j ν := by
  have hD := sourceD_eq P y b hS hL
  simp only [densityGate3, sourceAmp3, sourceF3, hD, sourceT3_eq]
  fin_cases j <;> rfl

theorem sourceF3_at (y b : ℚ) (hS : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) :
    sourceF3 (P.node3 y) (P.node3 (y - P.Dy)) b = 1 - 6*feeR - 6*(P.NdAt y b/P.DdAt y) := by
  simp only [sourceF3, sourceD_eq P y b hS hL]
  rfl

/-! ## Polynomials of the atoms -/

/-- The two width endpoints: the crossing `s(y)` and the cap. -/
def endP3 (e : Fin 2) : Poly := ![P.sp, [capM]] e

/-- The field guards: `B > 0`, `1 − B > 0`, `L − 1 > 0`, `q ≥ 1/2`, `q < 3/4`, `L₀ − L > 0`,
`B₀ ≥ 22/23`, `1 − B₀ > 0`, `L₀ − 1 > 0`. -/
def field3P : Fin 9 → Poly :=
  ![P.Bp, sub [1] P.Bp, sub P.Lp [1], sub (smul (3/2 - den) P.L0p) (smul 3 P.B0p),
    sub (smul (9/2) P.B0p) (smul (7/4 - den) P.L0p), sub P.L0p P.Lp, sub P.B0p [22/23],
    sub [1] P.B0p, sub P.L0p [1]]

/-- `sg3NAt` as a polynomial in `y`. -/
def sg3N (b : Poly) (j : Fin 18) : Poly :=
  let A := P.NdP b
  let D := P.DdP
  let B0 := P.B0p
  let L0 := P.L0p
  let T := add (P.tP b) b
  let Lr := LrefP b
  ![smul den D, mul (sub b [2*feeE]) D, smul feeR D, sub (smul (1/75 - feeR) D) A,
    sub (mul (sub [1 - 6*feeR - 4*feeE] (smul (1/2) T)) D) (smul 6 A),
    sub (mul B0 (sub (smul (1 - 6*feeR) D) (smul 6 A))) (mul (add T [4*feeE]) D),
    sub D (smul ((1 - den)*den*capM) L0),
    sub (smul (feeR - 14*feeE) D) (smul ((1 - den)*den*feeE) (add B0 (smul capM L0))),
    smul (feeR - 20*feeE) D, mul Lr D, smul (1/100 - 10*feeE) D,
    sub (mul (sub (add [5/6 - 9*feeR - feeF] (smul (499/1000) Lr)) T) D) (smul 9 A),
    sub (mul (sub [1 - 5*feeR - feeF] T) D) (smul 5 A),
    sub (mul (sub [49/50 - 4*feeR - feeF] T) D) (smul 4 A),
    sub (mul (sub [49/50 - (9/2)*feeR - feeF] T) D) (smul (9/2) A),
    sub (mul (sub Lr [7*feeR + feeF]) D) (smul 7 A),
    sub (mul (sub b [2*feeE]) D) A, add A (smul (1/10^30) D)] j

theorem eval_sg3N (b : Poly) (y : ℚ) (j : Fin 18) :
    eval (P.sg3N b j) y = sg3NAt (P.NdAt y (eval b y)) (P.DdAt y) (P.tAt y (eval b y)) (eval b y)
      (P.B (y - P.Dy)) (P.L (y - P.Dy)) j := by
  fin_cases j <;>
    simp [sg3N, sg3NAt, LrefP, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

def weak3N (b : Poly) : Poly :=
  let A := P.NdP b
  let D := P.DdP
  let FD := sub (smul (1 - 6*feeR) D) (smul 6 A)
  sub (smul capM (mul P.L0p FD)) (sub (mul P.B0p FD) (mul (P.tP b) D))

theorem eval_weak3N (b : Poly) (y : ℚ) :
    eval (P.weak3N b) y = weak3NAt (P.NdAt y (eval b y)) (P.DdAt y) (P.tAt y (eval b y))
      (P.B (y - P.Dy)) (P.L (y - P.Dy)) := by
  simp [weak3N, weak3NAt]; ring

/-- `sec3NAt` as a polynomial in `y`. -/
def sec3N (b : Poly) (j : Fin 3) (ν : ℚ) : Poly :=
  let A := P.NdP b
  let D := P.DdP
  let AD := add (smul feeR D) A
  let FD := sub (smul (1 - 6*feeR - feeE) D) (smul 6 A)
  let tt := 15 - 6*ν
  let HD := add (smul tt (sub AD (smul ν (mul (add (P.tP b) b) D))))
    (smul ν (sub (smul 10 D) (smul 60 AD)))
  let bD := mul b D
  ![add HD (smul tt (sub (sub (smul (ν/2) FD) (smul (1 - ν) bD)) (smul feeF D))),
    sub (add HD (smul tt (sub (sub (smul (5/6) FD) (smul (1 - ν) bD)) (smul feeF D))))
      (smul (10*ν) FD),
    sub (add HD (smul tt (sub (sub (smul (ν/2) (sub FD (smul (1/50) D))) (smul (1 - ν) bD))
      (smul feeF D)))) (smul (10*ν/50) D)] j

theorem eval_sec3N (b : Poly) (j : Fin 3) (ν y : ℚ) :
    eval (P.sec3N b j ν) y =
      sec3NAt (P.NdAt y (eval b y)) (P.DdAt y) (P.tAt y (eval b y)) (eval b y) j ν := by
  fin_cases j <;> simp [sec3N, sec3NAt, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

/-- The threshold `q = α/S` and `3/4 − q = β/S` as polynomials. -/
def alpha3P : Poly := smul (1 - den) P.L0p
def S3P : Poly := sub (smul 6 P.B0p) P.L0p
def beta3P : Poly := sub (smul (3/4) P.S3P) P.alpha3P

/-- `S³ · Dd · cubicBernstein (special sector j)` on `[q, 3/4]`, as polynomials in `y`. -/
def sec3B (b : Poly) (j : Fin 3) (i : Fin 4) : Poly :=
  let c := cubic4P (fun ν => P.sec3N b j ν)
  let N := P.alpha3P
  let β := P.beta3P
  let S := P.S3P
  let a0 := add (add (mul (c 0) (pow S 3)) (mul (c 1) (mul N (pow S 2))))
    (add (mul (c 2) (mul (pow N 2) S)) (mul (c 3) (pow N 3)))
  let a1 := mul β (add (add (mul (c 1) (pow S 2)) (smul 2 (mul (c 2) (mul N S))))
    (smul 3 (mul (c 3) (pow N 2))))
  let a2 := mul (pow β 2) (add (mul (c 2) S) (smul 3 (mul (c 3) N)))
  let a3 := mul (pow β 3) (c 3)
  ![a0, add a0 (smul (1/3) a1), add (add a0 (smul (2/3) a1)) (smul (1/3) a2),
    add (add a0 a1) (add a2 a3)] i

theorem eval_sec3B (b : Poly) (j : Fin 3) (i : Fin 4) (y : ℚ) :
    eval (P.sec3B b j i) y = cubBern (fun k => cubic4 (fun ν => eval (P.sec3N b j ν) y) k)
      (eval P.alpha3P y) (eval P.beta3P y) (eval P.S3P y) i := by
  fin_cases i <;> simp [sec3B, cubBern, eval_cubic4P, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring

/-- The cell condition `2 (b − 2e) ≤ F' − e`, times `D`. -/
def cell3N (b : Poly) : Poly :=
  sub (sub (smul (1 - 6*feeR - feeE) P.DdP) (smul 6 (P.NdP b))) (smul 2 (mul (sub b [2*feeE]) P.DdP))

theorem eval_cell3N (b : Poly) (y : ℚ) :
    eval (P.cell3N b) y = (1 - 6*feeR - feeE)*P.DdAt y - 6*P.NdAt y (eval b y) -
      2*((eval b y - 2*feeE)*P.DdAt y) := by
  simp [cell3N]

end Piece

end QRH.RepeatedMarks.Faceless
