/- The mixed-step face family: packed certificates.

The HIGH coefficients `highU3` and the special-sector Bernstein coefficients `sec3B` mirrored on
packed big numbers (as `Faceless/Packed.lean` and `Faceless/ScalarZ.lean` for `SourceValid2`): the
packed result is read back once and compared with literal integer data, and positivity is checked on
the data. -/
import Submissions.arvi_mixed_step.Family.High3

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite Poly

namespace Pk

open IPoly

section formula3
variable (X Δ eIn : ℕ)

/-- `Piece.valP3` on packed polynomials. -/
def valPZ3 (P : Piece) (b : Poly) (k : Branch) (ν p : ℚ) : PZ :=
  gateGDnZ Δ (ofPoly X Δ P.DdP eIn)
    (add Δ (smul Δ feeR (ofPoly X Δ P.DdP eIn)) (ofPoly X Δ (P.NdP b) eIn))
    (sub Δ (smul Δ (1 - 6*feeR - feeE) (ofPoly X Δ P.DdP eIn)) (smul Δ 6 (ofPoly X Δ (P.NdP b) eIn)))
    (mul (add Δ (ofPoly X Δ (P.tP b) eIn) (ofPoly X Δ b eIn)) (ofPoly X Δ P.DdP eIn))
    (sub Δ (mul (sub Δ (ofPoly X Δ b eIn) (const Δ (2*feeE))) (ofPoly X Δ P.DdP eIn))
      (ofPoly X Δ (P.NdP b) eIn))
    feeF 8 (ofPoly X Δ P.B0p eIn) (ofPoly X Δ P.L0p eIn) capM ν p k

/-- `Piece.highU3` on packed polynomials. -/
def highUZ3 (P : Piece) (b : Poly) (k : Branch) (a j : Fin 4) : PZ :=
  cuZ Δ (bicubicZ Δ (fun ν p => valPZ3 X Δ eIn P b k ν p)) (ofPoly X Δ P.alpha3P eIn)
    (ofPoly X Δ P.beta3P eIn) (ofPoly X Δ P.S3P eIn) a j

/-- `Piece.sec3N` on packed polynomials. -/
def sec3NZ (P : Piece) (b : Poly) (j : Fin 3) (ν : ℚ) : PZ :=
  let A := ofPoly X Δ (P.NdP b) eIn
  let D := ofPoly X Δ P.DdP eIn
  let AD := add Δ (smul Δ feeR D) A
  let FD := sub Δ (smul Δ (1 - 6*feeR - feeE) D) (smul Δ 6 A)
  let tt := 15 - 6*ν
  let HD := add Δ (smul Δ tt (sub Δ AD (smul Δ ν (mul (add Δ (ofPoly X Δ (P.tP b) eIn)
    (ofPoly X Δ b eIn)) D)))) (smul Δ ν (sub Δ (smul Δ 10 D) (smul Δ 60 AD)))
  let bD := mul (ofPoly X Δ b eIn) D
  ![add Δ HD (smul Δ tt (sub Δ (sub Δ (smul Δ (ν/2) FD) (smul Δ (1 - ν) bD)) (smul Δ feeF D))),
    sub Δ (add Δ HD (smul Δ tt (sub Δ (sub Δ (smul Δ (5/6) FD) (smul Δ (1 - ν) bD)) (smul Δ feeF D))))
      (smul Δ (10*ν) FD),
    sub Δ (add Δ HD (smul Δ tt (sub Δ (sub Δ (smul Δ (ν/2) (sub Δ FD (smul Δ (1/50) D)))
      (smul Δ (1 - ν) bD)) (smul Δ feeF D)))) (smul Δ (10*ν/50) D)] j

/-- `Piece.sec3B` on packed polynomials. -/
def sec3BZ (P : Piece) (b : Poly) (j : Fin 3) (i : Fin 4) : PZ :=
  let c := cubic4Z Δ (fun ν => sec3NZ X Δ eIn P b j ν)
  let N := ofPoly X Δ P.alpha3P eIn
  let β := ofPoly X Δ P.beta3P eIn
  let S := ofPoly X Δ P.S3P eIn
  let a0 := add Δ (add Δ (mul (c 0) (pow S 3)) (mul (c 1) (mul N (pow S 2))))
    (add Δ (mul (c 2) (mul (pow N 2) S)) (mul (c 3) (pow N 3)))
  let a1 := mul β (add Δ (add Δ (mul (c 1) (pow S 2)) (smul Δ 2 (mul (c 2) (mul N S))))
    (smul Δ 3 (mul (c 3) (pow N 2))))
  let a2 := mul (pow β 2) (add Δ (mul (c 2) S) (smul Δ 3 (mul (c 3) N)))
  let a3 := mul (pow β 3) (c 3)
  ![a0, add Δ a0 (smul Δ (1/3) a1), add Δ (add Δ a0 (smul Δ (2/3) a1)) (smul Δ (1/3) a2),
    add Δ (add Δ a0 a1) (add Δ a2 a3)] i

end formula3

section reps3
variable {X Δ : ℕ}

theorem rep_valPZ3 (eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (ν p : ℚ) :
    Rep X Δ (valPZ3 X Δ eIn P b k ν p) (P.valP3 b k ν p) := by
  unfold valPZ3 Piece.valP3
  apply rep_trim
  exact rep_gateGDnZ (rep_ofPoly _ _) (rep_add (rep_smul _ (rep_ofPoly _ _)) (rep_ofPoly _ _))
    (rep_sub (rep_smul _ (rep_ofPoly _ _)) (rep_smul _ (rep_ofPoly _ _)))
    (rep_mul (rep_add (rep_ofPoly _ _) (rep_ofPoly _ _)) (rep_ofPoly _ _))
    (rep_sub (rep_mul (rep_sub (rep_ofPoly _ _) (rep_const _)) (rep_ofPoly _ _)) (rep_ofPoly _ _))
    (rep_ofPoly _ _) (rep_ofPoly _ _) _ _ _ _ _ k

theorem rep_highUZ3 (eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (a j : Fin 4) :
    Rep X Δ (highUZ3 X Δ eIn P b k a j) (P.highU3 b k a j) := by
  unfold highUZ3 Piece.highU3
  exact rep_cuZ (rep_bicubicZ (fun ν p => rep_valPZ3 eIn P b k ν p)) (rep_ofPoly _ _)
    (rep_ofPoly _ _) (rep_ofPoly _ _) a j

theorem rep_sec3NZ (eIn : ℕ) (P : Piece) (b : Poly) (j : Fin 3) (ν : ℚ) :
    Rep X Δ (sec3NZ X Δ eIn P b j ν) (P.sec3N b j ν) := by
  have hA : Rep X Δ (ofPoly X Δ (P.NdP b) eIn) (P.NdP b) := rep_ofPoly _ _
  have hD : Rep X Δ (ofPoly X Δ P.DdP eIn) P.DdP := rep_ofPoly _ _
  have ht : Rep X Δ (ofPoly X Δ (P.tP b) eIn) (P.tP b) := rep_ofPoly _ _
  have hb : Rep X Δ (ofPoly X Δ b eIn) b := rep_ofPoly _ _
  have hAD := rep_add (rep_smul feeR hD) hA
  have hFD := rep_sub (rep_smul (1 - 6*feeR - feeE) hD) (rep_smul 6 hA)
  have hHD := rep_add (rep_smul (15 - 6*ν) (rep_sub hAD (rep_smul ν (rep_mul (rep_add ht hb) hD))))
    (rep_smul ν (rep_sub (rep_smul 10 hD) (rep_smul 60 hAD)))
  have hbD := rep_mul hb hD
  unfold sec3NZ Piece.sec3N
  exact rep_vec3
    (rep_add hHD (rep_smul _ (rep_sub (rep_sub (rep_smul _ hFD) (rep_smul _ hbD)) (rep_smul _ hD))))
    (rep_sub (rep_add hHD (rep_smul _ (rep_sub (rep_sub (rep_smul _ hFD) (rep_smul _ hbD))
      (rep_smul _ hD)))) (rep_smul _ hFD))
    (rep_sub (rep_add hHD (rep_smul _ (rep_sub (rep_sub
      (rep_smul _ (rep_sub hFD (rep_smul _ hD))) (rep_smul _ hbD)) (rep_smul _ hD)))) (rep_smul _ hD))
    j

theorem rep_sec3BZ (eIn : ℕ) (P : Piece) (b : Poly) (j : Fin 3) (i : Fin 4) :
    Rep X Δ (sec3BZ X Δ eIn P b j i) (P.sec3B b j i) := by
  have hc := rep_cubic4Z (X := X) (Δ := Δ) (fun ν => rep_sec3NZ eIn P b j ν)
  have hN : Rep X Δ (ofPoly X Δ P.alpha3P eIn) P.alpha3P := rep_ofPoly _ _
  have hβ : Rep X Δ (ofPoly X Δ P.beta3P eIn) P.beta3P := rep_ofPoly _ _
  have hS : Rep X Δ (ofPoly X Δ P.S3P eIn) P.S3P := rep_ofPoly _ _
  have ha0 := rep_add (rep_add (rep_mul (hc 0) (rep_pow hS 3)) (rep_mul (hc 1) (rep_mul hN (rep_pow hS 2))))
    (rep_add (rep_mul (hc 2) (rep_mul (rep_pow hN 2) hS)) (rep_mul (hc 3) (rep_pow hN 3)))
  have ha1 := rep_mul hβ (rep_add (rep_add (rep_mul (hc 1) (rep_pow hS 2))
    (rep_smul 2 (rep_mul (hc 2) (rep_mul hN hS)))) (rep_smul 3 (rep_mul (hc 3) (rep_pow hN 2))))
  have ha2 := rep_mul (rep_pow hβ 2) (rep_add (rep_mul (hc 2) hS) (rep_smul 3 (rep_mul (hc 3) hN)))
  have ha3 := rep_mul (rep_pow hβ 3) (hc 3)
  exact rep_vec4 ha0 (rep_add ha0 (rep_smul _ ha1))
    (rep_add (rep_add ha0 (rep_smul _ ha1)) (rep_smul _ ha2)) (rep_add (rep_add ha0 ha1) (rep_add ha2 ha3)) i

end reps3

/-! ## The packed HIGH certificate -/

/-- The 16 coefficient polynomials of `highU3`, packed, aligned to the common power `Δ^E`. -/
def alignedK3 (X Δ eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (a j : Fin 4) : PZ :=
  scale Δ (highUZ3 X Δ eIn P b k a j)
    (maxE16 (fun a j => highUZ3 X Δ eIn P b k a j) - (highUZ3 X Δ eIn P b k a j).e)

/-- Phase 1: the packed coefficients, read back at base `X`, are `g` times the data `cK`. -/
def decKgX3 (Δ eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (g X : ℕ) (cK : Fin 4 → Fin 4 → IPoly) :
    Bool :=
  decide (0 < Δ) && decide (0 < g) &&
  ((List.finRange 4).all fun a => (List.finRange 4).all fun j =>
    (alignedK3 X Δ eIn P b k a j).ok && decide ((alignedK3 X Δ eIn P b k a j).pos1 < X) &&
      decide ((alignedK3 X Δ eIn P b k a j).neg1 < X) &&
      decide (unpack X (alignedK3 X Δ eIn P b k a j) = IPoly.smul g (cK a j)))

theorem coeffPos_of_decKgX3_of (Δ eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (g X : ℕ)
    (cK : Fin 4 → Fin 4 → IPoly) (hd : decKgX3 Δ eIn P b k g X cK = true)
    (hpos : ∀ y : ℚ, 0 ≤ y → y ≤ 1 → ∀ u p : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ p → p ≤ 1/2 →
      0 < ∑ i : Fin 4, ∑ j : Fin 4, ((IPoly.eval (cK i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ)) :
    HighCoeffPos (P.highU3 b k) := by
  intro y hy0 hy1 u p hu0 hu1 hp0 hp1
  simp only [decKgX3, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at hd
  obtain ⟨⟨hΔ, hg⟩, hall⟩ := hd
  have h := hpos y hy0 hy1 u p hu0 hu1 hp0 hp1
  set E := maxE16 (fun a j => highUZ3 X Δ eIn P b k a j) with hE
  have heq : ∀ i j, (g : ℝ) * ((IPoly.eval (cK i j) y : ℚ) : ℝ) =
      ((Δ : ℝ) ^ E) * ((Poly.eval (P.highU3 b k i j) y : ℚ) : ℝ) := by
    intro i j
    have hrep : Rep X Δ (alignedK3 X Δ eIn P b k i j) (P.highU3 b k i j) :=
      rep_scale _ (rep_highUZ3 eIn P b k i j)
    obtain ⟨⟨⟨hok, hp⟩, hn⟩, hcK⟩ := hall i j
    have h1 := eval_unpack hrep hok hp hn y
    rw [hcK, IPoly.eval_smul] at h1
    have he : (alignedK3 X Δ eIn P b k i j).e = E := by
      have := le_maxE16 (fun a j => highUZ3 X Δ eIn P b k a j) i j
      simp only [alignedK3, scale, ← hE] at this ⊢; omega
    rw [he] at h1
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at h2 ⊢
    exact h2
  have hgpos : (0:ℝ) < g := by exact_mod_cast hg
  have hsum : (g : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4, ((IPoly.eval (cK i j) y : ℚ) : ℝ) *
      u ^ (i:ℕ) * p ^ (j:ℕ) = ((Δ : ℝ) ^ E) * ∑ i : Fin 4, ∑ j : Fin 4,
        ((Poly.eval (P.highU3 b k i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ) := by
    simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, heq i j]
  have hΔE : (0:ℝ) < (Δ : ℝ) ^ E := by positivity
  have hprod : 0 < (g : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4, ((IPoly.eval (cK i j) y : ℚ) : ℝ) *
      u ^ (i:ℕ) * p ^ (j:ℕ) := mul_pos hgpos (by simpa using h)
  rw [hsum] at hprod
  exact pos_of_mul_pos_right hprod hΔE.le

/-- Phases 1 and 2 with both bases as data: `decKgX3` and the packed tree check `IPoly.checkZ`. -/
theorem coeffPos_of_decKgXZ3 (Δ eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (g X : ℕ)
    (cK : Fin 4 → Fin 4 → IPoly) (XZ L : ℕ) (T : IPoly.UTreeI)
    (hd : decKgX3 Δ eIn P b k g X cK = true) (ht : IPoly.checkZ cK XZ L T = true) :
    HighCoeffPos (P.highU3 b k) :=
  coeffPos_of_decKgX3_of Δ eIn P b k g X cK hd (IPoly.checkZ_sound cK XZ L T ht)

/-! ## The packed sector certificate -/

/-- Phase 1 for one sector coefficient: the packed polynomial, read back at base `X`, is `g` times
the data `cS`. -/
def decS3 (Δ eIn : ℕ) (P : Piece) (b : Poly) (j : Fin 3) (i : Fin 4) (g X : ℕ) (cS : IPoly) : Bool :=
  decide (0 < Δ) && decide (0 < g) && (sec3BZ X Δ eIn P b j i).ok &&
    decide ((sec3BZ X Δ eIn P b j i).pos1 < X) && decide ((sec3BZ X Δ eIn P b j i).neg1 < X) &&
    decide (unpack X (sec3BZ X Δ eIn P b j i) = IPoly.smul g cS)

/-- Phases 1 and 2: `g · cS = Δ^e · sec3B`, and `cS` is positive on `[0, 1]`. -/
theorem secPos_of_decS3 (Δ eIn : ℕ) (P : Piece) (b : Poly) (j : Fin 3) (i : Fin 4) (g X : ℕ)
    (cS : IPoly) (l : List (ℕ × ℕ)) (hd : decS3 Δ eIn P b j i g X cS = true)
    (hp : (!l.isEmpty && IPoly.posOn cS 0 0 l) = true) : PosOn01 (P.sec3B b j i) := by
  intro y hy0 hy1
  simp only [decS3, Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨⟨⟨⟨⟨hΔ, hg⟩, hok⟩, hp1⟩, hn1⟩, hcS⟩ := hd
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨hne, hpos⟩ := hp
  have h := IPoly.posOn_sound _ 0 0 l hpos y (by simpa using hy0) hy1
    (by intro h'; rw [h'] at hne; simp at hne)
  have h1 := eval_unpack (rep_sec3BZ eIn P b j i) hok hp1 hn1 y
  rw [hcS, IPoly.eval_smul] at h1
  have hgq : (0:ℚ) < g := by exact_mod_cast hg
  have hΔq : (0:ℚ) < (Δ:ℚ) ^ (sec3BZ X Δ eIn P b j i).e := by positivity
  have : 0 < (Δ:ℚ) ^ (sec3BZ X Δ eIn P b j i).e * eval (P.sec3B b j i) y := by
    rw [← h1]; exact mul_pos hgq h
  exact pos_of_mul_pos_right this hΔq.le

end Pk

end QRH.RepeatedMarks.Faceless
