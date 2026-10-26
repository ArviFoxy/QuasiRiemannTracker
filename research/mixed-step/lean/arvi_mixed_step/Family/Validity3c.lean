/- The mixed-step face family with a variable cap: validity of every step of a piece.

As `Family/Validity3.lean`: from the certificates of a piece whose face at `y` has cap `cp(y)`,
every step `P.node3c cp (y − Dy) → P.node3c cp y` with `y ∈ [0, 1]` satisfies `SourceValid3` and
`SourceValid3X`, with the previous face as LOW and HIGH parent. The cap guards (`capFieldP`) replace
the constant-cap condition `sig + H ≤ capM`. -/
import Submissions.arvi_mixed_step.Family.Packed3c
import Submissions.arvi_mixed_step.Family.Validity3X

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite Poly

namespace Piece
variable (P : Piece) (cp : Poly)

/-- The certificates of a mixed piece with cap `cp`. -/
structure Certs3c : Prop where
  sig0 : 0 ≤ P.sig
  H0 : 0 < P.H
  Dy0 : 0 < P.Dy
  field : ∀ i, ∃ l, pos1I (P.field3P i) l = true
  capField : ∀ i, ∃ l, pos1I (P.capFieldP cp i) l = true
  scal : ∀ e j, ∃ l, pos1I (P.sg3Nc cp (P.endP3c cp e) j) l = true
  weak : ∀ e, ∃ l, pos1I (P.weak3Nc cp (P.endP3c cp e)) l = true
  sec : ∀ e (j : Fin 3) i, PosOn01 (P.sec3B (P.endP3c cp e) j i)
  cell : ∀ e, ∃ l, pos1I (P.cell3N (P.endP3c cp e)) l = true
  high : ∀ e k, HighCoeffPos (P.highU3c cp (P.endP3c cp e) k)

variable {P cp}

theorem Certs3c.fieldPos (C : P.Certs3c cp) {y : ℚ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < P.B y ∧ P.B y < 1 ∧ 1 < P.L y ∧ 3 * P.B (y - P.Dy) < (3/2 - den) * P.L (y - P.Dy) ∧
    (7/4 - den) * P.L (y - P.Dy) < 9/2 * P.B (y - P.Dy) ∧ P.L y < P.L (y - P.Dy) ∧
    22/23 < P.B (y - P.Dy) ∧ P.B (y - P.Dy) < 1 ∧ 1 < P.L (y - P.Dy) := by
  have f := fun i => Certs.pos (C.field i) hy0 hy1
  have f0 := f 0; have f1 := f 1; have f2 := f 2; have f3 := f 3; have f4 := f 4
  have f5 := f 5; have f6 := f 6; have f7 := f 7; have f8 := f 8
  simp only [field3P, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, eval_sub,
    eval_smul, eval_Bp, eval_Lp, eval_B0p, eval_L0p, eval_cons, eval_nil, mul_zero, add_zero] at f0 f1 f2 f3 f4 f5 f6 f7 f8
  refine ⟨f0, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

theorem Certs3c.capPos (C : P.Certs3c cp) {y : ℚ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < eval cp y ∧ eval cp y < 1 ∧ P.s y < eval cp y ∧ P.s y < eval cp (y - P.Dy) ∧
    eval cp (y - P.Dy) < 1 := by
  have f := fun i => Certs.pos (C.capField i) hy0 hy1
  have f0 := f 0; have f1 := f 1; have f2 := f 2; have f3 := f 3; have f4 := f 4
  simp only [capFieldP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, eval_sub,
    eval_sp, eval_cap0P, eval_cons, eval_nil, mul_zero, add_zero] at f0 f1 f2 f3 f4
  refine ⟨f0, by linarith, by linarith, by linarith, by linarith⟩

theorem Certs3c.valid (C : P.Certs3c cp) (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    SourceValid3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) (P.node3c cp (y - P.Dy)) := by
  obtain ⟨hB, hB1, hL1, hqh, hq34, hLd, hB0, hB01, hL01⟩ := C.fieldPos hy0 hy1
  obtain ⟨hc0, hc1, hsc, hsc0, hcp1⟩ := C.capPos hy0 hy1
  have hB0p : 0 < P.B (y - P.Dy) := by linarith
  have hL0p : 0 < P.L (y - P.Dy) := by linarith
  have hSp : 0 < 6 * P.B (y - P.Dy) - P.L (y - P.Dy) := by
    have hdenv : den = 1/2^15 := rfl
    rw [hdenv] at hq34
    linarith
  have hL0n : P.L (y - P.Dy) ≠ 0 := hL0p.ne'
  have hSn : 6 * P.B (y - P.Dy) - P.L (y - P.Dy) ≠ 0 := hSp.ne'
  have hHD : P.H * P.Dy ≠ 0 := (mul_pos C.H0 C.Dy0).ne'
  have hcross : crossing (P.node3c cp y) (P.node3c cp (y - P.Dy)) = P.s y :=
    P.crossing3c_eq cp y hHD hLd.ne'
  have hDn : 0 < P.DdAt y := mul_pos den_pos hSp
  have hq : P.q3 y = (1 - den) * P.L (y - P.Dy) / (6 * P.B (y - P.Dy) - P.L (y - P.Dy)) := rfl
  have hq1 : 1/2 ≤ P.q3 y := by rw [hq, le_div_iff₀ hSp]; linarith
  have hq2 : P.q3 y < 3/4 := by rw [hq, div_lt_iff₀ hSp]; linarith
  have hs0 : 0 ≤ P.s y := by simp only [s]; have := C.sig0; have := C.H0; positivity
  have hcp0 : 0 < eval cp (y - P.Dy) := lt_of_le_of_lt hs0 hsc0
  -- endpoint facts
  have hend : ∀ e : Fin 2, eval (P.endP3c cp e) y = ![P.s y, eval cp y] e := by
    intro e; fin_cases e <;> simp [endP3c]
  have hbs : ∀ b ∈ [crossing (P.node3c cp y) (P.node3c cp (y - P.Dy)), (P.node3c cp y).cap],
      ∃ e : Fin 2, b = eval (P.endP3c cp e) y := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact ⟨0, by rw [hcross, hend]; rfl⟩
    · exact ⟨1, by rw [hend]; rfl⟩
  -- scalar gates
  have hscal : ∀ e : Fin 2, ∀ j,
      0 < scalarGate3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) (eval (P.endP3c cp e) y) j := by
    intro e j
    have hp := Certs.pos (C.scal e j) hy0 hy1
    rw [eval_sg3Nc, ← sg3Atc_mul _ (P.DdAt y) _ _ _ _ _ hSn hL0n rfl,
      ← scalarGate3c_at P cp y _ hSn hL0n] at hp
    exact pos_of_mul_pos_left hp hDn.le
  have hweak : ∀ e : Fin 2,
      0 < weakCap3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) (eval (P.endP3c cp e) y) := by
    intro e
    have hp := Certs.pos (C.weak e) hy0 hy1
    rw [eval_weak3Nc, ← weak3c_mul _ _ _ _ _ _ hDn.ne' hL0n, ← weakCap3c_at P cp y _ hSn hL0n] at hp
    exact pos_of_mul_pos_left hp (by positivity)
  have hdens : ∀ e : Fin 2, ∀ j : Fin 3, ∀ i : Fin 4, 0 < cubicBernstein
      (fun ν => densityGate3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) (eval (P.endP3c cp e) y) ν j)
        (P.node3c cp y).q (3/4) i := by
    intro e j i
    have hp := C.sec e j i y hy0 hy1
    rw [eval_sec3B] at hp
    have hfun : (fun ν => densityGate3 (P.node3c cp y) (P.node3c cp (y - P.Dy))
        (eval (P.endP3c cp e) y) ν j) =
        fun ν => sec3At (P.NdAt y (eval (P.endP3c cp e) y)) (P.DdAt y)
          (P.tAt y (eval (P.endP3c cp e) y)) (eval (P.endP3c cp e) y) j ν := by
      funext ν; exact densityGate3c_at P cp y _ ν hSn hL0n j
    have hsec : ∀ ν, eval (P.sec3N (P.endP3c cp e) j ν) y =
        P.DdAt y * sec3At (P.NdAt y (eval (P.endP3c cp e) y)) (P.DdAt y)
          (P.tAt y (eval (P.endP3c cp e) y)) (eval (P.endP3c cp e) y) j ν := by
      intro ν
      rw [eval_sec3N, ← sec3At_mul _ _ _ _ hDn.ne' j ν]; ring
    have hS3 : eval P.S3P y = 6 * P.B (y - P.Dy) - P.L (y - P.Dy) := by
      simp only [S3P, eval_sub, eval_smul, eval_B0p, eval_L0p]
    have hcb := cubicBernstein_mul (fun ν => sec3At (P.NdAt y (eval (P.endP3c cp e) y)) (P.DdAt y)
      (P.tAt y (eval (P.endP3c cp e) y)) (eval (P.endP3c cp e) y) j ν) (P.DdAt y) (eval P.alpha3P y)
      (eval P.beta3P y) (eval P.S3P y) (by rw [hS3]; exact hSn)
      (by simp only [beta3P, eval_sub, eval_smul]) i
    have hqq : (P.node3c cp y).q = eval P.alpha3P y / eval P.S3P y := by
      rw [hS3]; simp only [node3c, q3, alpha3P, eval_smul, eval_L0p]
    rw [hfun, hqq]
    have hcc : (fun k => cubicCoeffs (fun ν => P.DdAt y * sec3At (P.NdAt y (eval (P.endP3c cp e) y))
        (P.DdAt y) (P.tAt y (eval (P.endP3c cp e) y)) (eval (P.endP3c cp e) y) j ν) k) =
        fun k => cubic4 (fun ν => eval (P.sec3N (P.endP3c cp e) j ν) y) k := by
      funext k; simp only [hsec]; rfl
    rw [hcc] at hcb
    rw [← hcb] at hp
    have hSpos : 0 < eval P.S3P y := by rw [hS3]; exact hSp
    exact pos_of_mul_pos_left hp (by positivity)
  have hcell : ∀ e : Fin 2, 2 * (eval (P.endP3c cp e) y - 2 * feeE) ≤
      sourceF3 (P.node3c cp y) (P.node3c cp (y - P.Dy)) (eval (P.endP3c cp e) y) - feeE := by
    intro e
    have hp := Certs.pos (C.cell e) hy0 hy1
    rw [eval_cell3N] at hp
    rw [sourceF3c_at P cp y _ hSn hL0n]
    have : 0 < ((1 - 6*feeR - 6 * (P.NdAt y (eval (P.endP3c cp e) y) / P.DdAt y)) - feeE -
        2 * (eval (P.endP3c cp e) y - 2 * feeE)) * P.DdAt y := by
      have := hDn.ne'; field_simp; linarith
    have := pos_of_mul_pos_left this hDn.le
    linarith
  -- the HIGH gate at both endpoints, then on the whole cell
  have hhigh : ∀ e : Fin 2, ∀ ν ∈ Set.Icc ((P.q3 y : ℚ) : ℝ) (3/4), ∀ p ∈ Set.Icc (0:ℝ) (1/2),
      ∀ k, 0 < highGate3Real (P.node3c cp y) (P.node3c cp (y - P.Dy)) (P.node3c cp (y - P.Dy)) 8
        ((eval (P.endP3c cp e) y : ℚ) : ℝ) ν p k := by
    intro e ν hν p hp k
    exact P.high_pos_of_U3c cp (P.endP3c cp e) k y
      (fun u p hu0 hu1 hp0 hp1 => C.high e k y hy0 hy1 u p hu0 hu1 hp0 hp1) hSp hL0p hq2 ν p hν hp
  refine ⟨?_, ?_, ?_⟩
  · -- SourceValidC3
    refine ⟨hB, hB1.le, hL1, hc0.le, hc1, hq1, hq2, hLd, ?_, ?_, ?_,
      ⟨hB0.le, hB01.le, hL01, hcp0.le, hcp1⟩, ?_⟩
    · rw [hcross]; exact hs0
    · rw [hcross]; exact hsc.le
    · rw [hcross]; exact hsc0.le
    · intro b hb
      obtain ⟨e, rfl⟩ := hbs b hb
      exact ⟨hscal e, (hweak e).le, hdens e⟩
  · -- HighPos3R
    intro b hb ν hν p hp k
    have h0 := hhigh 0 ν hν p hp k
    have h1 := hhigh 1 ν hν p hp k
    rw [hend] at h0 h1
    have hb' : b ∈ Set.Icc ((P.s y : ℚ) : ℝ) ((eval cp y : ℚ) : ℝ) := by
      rw [hcross] at hb; simpa [node3c] using hb
    exact width_affine_positive (highGate3Real_affine _ _ _ 8 ν p k) hb' (by simpa using h0)
      (by simpa using h1)
  · -- CellRatio3
    intro b hb
    obtain ⟨e, rfl⟩ := hbs b hb
    simpa [node3c] using hcell e

/-- Collet's LOW denominator is negative at every step (as `Certs3.validX`). -/
theorem Certs3c.validX (C : P.Certs3c cp) (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    SourceValid3X (P.node3c cp y) (P.node3c cp (y - P.Dy)) := by
  obtain ⟨_, _, _, _, hq34, _, hB0, hB01, hL01⟩ := C.fieldPos hy0 hy1
  have hSp : 0 < 6 * P.B (y - P.Dy) - P.L (y - P.Dy) := by
    have hdenv : den = 1/2^15 := rfl
    rw [hdenv] at hq34
    linarith
  have hL0p : 0 < P.L (y - P.Dy) := by linarith
  have hden : den = 1/2^15 := rfl
  unfold SourceValid3X
  simp only [node3c, q3]
  have key : 6 * ((1 - den) * P.L (y - P.Dy) / (6 * P.B (y - P.Dy) - P.L (y - P.Dy))) *
      P.B (y - P.Dy) - P.L (y - P.Dy) =
      P.L (y - P.Dy) * (P.L (y - P.Dy) - 6 * den * P.B (y - P.Dy)) /
        (6 * P.B (y - P.Dy) - P.L (y - P.Dy)) := by
    field_simp
    ring
  rw [key]
  apply div_pos _ hSp
  apply mul_pos hL0p
  rw [hden]
  linarith

end Piece

end QRH.RepeatedMarks.Faceless
