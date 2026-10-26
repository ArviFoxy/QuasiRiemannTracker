/- The mixed-step face family with a variable cap: packed certificates.

As `Family/Packed3.lean`, with the HIGH parent's cap the packed polynomial `cp(y − Dy)` in the
cleared samples (`gateGDnZc`). The sector certificates do not involve the cap and are reused from
`Family/Packed3.lean`. -/
import Submissions.arvi_mixed_step.Family.High3c
import Submissions.arvi_mixed_step.Family.Packed3

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite Poly

namespace Pk

open IPoly

section formula3c
variable (X Δ eIn : ℕ)

/-- `gateGDnPc` on packed polynomials. -/
def gateGDnZc (Dn Na NF TD SD : PZ) (fee K : ℚ) (B L HC : PZ) (ν p : ℚ) (k : Branch) : PZ :=
  let bI : Fin 2 → PZ := ![smul Δ (2*p*K) SD, smul Δ p NF]
  let hP : Fin 3 → PZ := ![smul Δ (2*p) SD, mul (smul Δ (2*p) HC) NF, mul (smul Δ (2*p) B) NF]
  let base := add Δ (smul Δ (15 - 6*ν) (sub Δ Na (smul Δ ν TD)))
    (add Δ (smul Δ ν (sub Δ (smul Δ 10 Dn) (smul Δ 60 Na)))
      (add Δ (smul Δ ((15 - 6*ν)*(1 - 2*p)*ν) SD) (add Δ (smul Δ (-10*ν) NF) (smul Δ (-fee*(15 - 6*ν)) Dn))))
  let N := add Δ (smul Δ 10 (mul NF (mul (dIZ Δ p k.1) (ePZ Δ p L k.2))))
    (smul Δ (5 - 6*ν) (add Δ (smul Δ 2 (mul (ePZ Δ p L k.2) (bI k.1))) (mul (dIZ Δ p k.1) (hP k.2))))
  add Δ (mul (gateMZ Δ ν p L k) base) (smul Δ (ν*(15 - 6*ν)) N)

/-- `Piece.valP3c` on packed polynomials. -/
def valPZ3c (P : Piece) (cp b : Poly) (k : Branch) (ν p : ℚ) : PZ :=
  gateGDnZc Δ (ofPoly X Δ P.DdP eIn)
    (add Δ (smul Δ feeR (ofPoly X Δ P.DdP eIn)) (ofPoly X Δ (P.NdP b) eIn))
    (sub Δ (smul Δ (1 - 6*feeR - feeE) (ofPoly X Δ P.DdP eIn)) (smul Δ 6 (ofPoly X Δ (P.NdP b) eIn)))
    (mul (add Δ (ofPoly X Δ (P.tP b) eIn) (ofPoly X Δ b eIn)) (ofPoly X Δ P.DdP eIn))
    (sub Δ (mul (sub Δ (ofPoly X Δ b eIn) (const Δ (2*feeE))) (ofPoly X Δ P.DdP eIn))
      (ofPoly X Δ (P.NdP b) eIn))
    feeF 8 (ofPoly X Δ P.B0p eIn) (ofPoly X Δ P.L0p eIn) (ofPoly X Δ (P.cap0P cp) eIn) ν p k

/-- `Piece.highU3c` on packed polynomials. -/
def highUZ3c (P : Piece) (cp b : Poly) (k : Branch) (a j : Fin 4) : PZ :=
  cuZ Δ (bicubicZ Δ (fun ν p => valPZ3c X Δ eIn P cp b k ν p)) (ofPoly X Δ P.alpha3P eIn)
    (ofPoly X Δ P.beta3P eIn) (ofPoly X Δ P.S3P eIn) a j

end formula3c

section reps3c
variable {X Δ : ℕ}

theorem rep_gateGDnZc {Dn Na NF TD SD B L HC : PZ} {Dn' Na' NF' TD' SD' B' L' HC' : Poly}
    (hDn : Rep X Δ Dn Dn') (hNa : Rep X Δ Na Na') (hNF : Rep X Δ NF NF') (hTD : Rep X Δ TD TD')
    (hSD : Rep X Δ SD SD') (hB : Rep X Δ B B') (hL : Rep X Δ L L') (hHC : Rep X Δ HC HC')
    (fee K ν p : ℚ) (k : Branch) :
    Rep X Δ (gateGDnZc Δ Dn Na NF TD SD fee K B L HC ν p k)
      (gateGDnPc Dn' Na' NF' TD' SD' fee K B' L' HC' ν p k) := by
  unfold gateGDnZc gateGDnPc
  exact rep_add (rep_mul (rep_gateMZ ν p hL k)
      (rep_add (rep_smul _ (rep_sub hNa (rep_smul _ hTD)))
        (rep_add (rep_smul _ (rep_sub (rep_smul _ hDn) (rep_smul _ hNa)))
          (rep_add (rep_smul _ hSD) (rep_add (rep_smul _ hNF) (rep_smul _ hDn))))))
    (rep_smul _ (rep_add (rep_smul _ (rep_mul hNF (rep_mul (rep_dIZ p k.1) (rep_ePZ p hL k.2))))
      (rep_smul _ (rep_add (rep_smul _ (rep_mul (rep_ePZ p hL k.2)
          (rep_vec2 (rep_smul _ hSD) (rep_smul _ hNF) k.1)))
        (rep_mul (rep_dIZ p k.1)
          (rep_vec3 (rep_smul _ hSD) (rep_mul (rep_smul _ hHC) hNF) (rep_mul (rep_smul _ hB) hNF)
            k.2))))))

theorem rep_valPZ3c (eIn : ℕ) (P : Piece) (cp b : Poly) (k : Branch) (ν p : ℚ) :
    Rep X Δ (valPZ3c X Δ eIn P cp b k ν p) (P.valP3c cp b k ν p) := by
  unfold valPZ3c Piece.valP3c
  apply rep_trim
  exact rep_gateGDnZc (rep_ofPoly _ _) (rep_add (rep_smul _ (rep_ofPoly _ _)) (rep_ofPoly _ _))
    (rep_sub (rep_smul _ (rep_ofPoly _ _)) (rep_smul _ (rep_ofPoly _ _)))
    (rep_mul (rep_add (rep_ofPoly _ _) (rep_ofPoly _ _)) (rep_ofPoly _ _))
    (rep_sub (rep_mul (rep_sub (rep_ofPoly _ _) (rep_const _)) (rep_ofPoly _ _)) (rep_ofPoly _ _))
    (rep_ofPoly _ _) (rep_ofPoly _ _) (rep_ofPoly _ _) _ _ _ _ k

theorem rep_highUZ3c (eIn : ℕ) (P : Piece) (cp b : Poly) (k : Branch) (a j : Fin 4) :
    Rep X Δ (highUZ3c X Δ eIn P cp b k a j) (P.highU3c cp b k a j) := by
  unfold highUZ3c Piece.highU3c
  exact rep_cuZ (rep_bicubicZ (fun ν p => rep_valPZ3c eIn P cp b k ν p)) (rep_ofPoly _ _)
    (rep_ofPoly _ _) (rep_ofPoly _ _) a j

end reps3c

/-! ## The packed HIGH certificate -/

/-- The 16 coefficient polynomials of `highU3c`, packed, aligned to the common power `Δ^E`. -/
def alignedK3c (X Δ eIn : ℕ) (P : Piece) (cp b : Poly) (k : Branch) (a j : Fin 4) : PZ :=
  scale Δ (highUZ3c X Δ eIn P cp b k a j)
    (maxE16 (fun a j => highUZ3c X Δ eIn P cp b k a j) - (highUZ3c X Δ eIn P cp b k a j).e)

/-- Phase 1: the packed coefficients, read back at base `X`, are `g` times the data `cK`. -/
def decKgX3c (Δ eIn : ℕ) (P : Piece) (cp b : Poly) (k : Branch) (g X : ℕ)
    (cK : Fin 4 → Fin 4 → IPoly) : Bool :=
  decide (0 < Δ) && decide (0 < g) &&
  ((List.finRange 4).all fun a => (List.finRange 4).all fun j =>
    (alignedK3c X Δ eIn P cp b k a j).ok && decide ((alignedK3c X Δ eIn P cp b k a j).pos1 < X) &&
      decide ((alignedK3c X Δ eIn P cp b k a j).neg1 < X) &&
      decide (unpack X (alignedK3c X Δ eIn P cp b k a j) = IPoly.smul g (cK a j)))

theorem coeffPos_of_decKgX3c_of (Δ eIn : ℕ) (P : Piece) (cp b : Poly) (k : Branch) (g X : ℕ)
    (cK : Fin 4 → Fin 4 → IPoly) (hd : decKgX3c Δ eIn P cp b k g X cK = true)
    (hpos : ∀ y : ℚ, 0 ≤ y → y ≤ 1 → ∀ u p : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ p → p ≤ 1/2 →
      0 < ∑ i : Fin 4, ∑ j : Fin 4, ((IPoly.eval (cK i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ)) :
    HighCoeffPos (P.highU3c cp b k) := by
  intro y hy0 hy1 u p hu0 hu1 hp0 hp1
  simp only [decKgX3c, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at hd
  obtain ⟨⟨hΔ, hg⟩, hall⟩ := hd
  have h := hpos y hy0 hy1 u p hu0 hu1 hp0 hp1
  set E := maxE16 (fun a j => highUZ3c X Δ eIn P cp b k a j) with hE
  have heq : ∀ i j, (g : ℝ) * ((IPoly.eval (cK i j) y : ℚ) : ℝ) =
      ((Δ : ℝ) ^ E) * ((Poly.eval (P.highU3c cp b k i j) y : ℚ) : ℝ) := by
    intro i j
    have hrep : Rep X Δ (alignedK3c X Δ eIn P cp b k i j) (P.highU3c cp b k i j) :=
      rep_scale _ (rep_highUZ3c eIn P cp b k i j)
    obtain ⟨⟨⟨hok, hp⟩, hn⟩, hcK⟩ := hall i j
    have h1 := eval_unpack hrep hok hp hn y
    rw [hcK, IPoly.eval_smul] at h1
    have he : (alignedK3c X Δ eIn P cp b k i j).e = E := by
      have := le_maxE16 (fun a j => highUZ3c X Δ eIn P cp b k a j) i j
      simp only [alignedK3c, scale, ← hE] at this ⊢; omega
    rw [he] at h1
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at h2 ⊢
    exact h2
  have hgpos : (0:ℝ) < g := by exact_mod_cast hg
  have hsum : (g : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4, ((IPoly.eval (cK i j) y : ℚ) : ℝ) *
      u ^ (i:ℕ) * p ^ (j:ℕ) = ((Δ : ℝ) ^ E) * ∑ i : Fin 4, ∑ j : Fin 4,
        ((Poly.eval (P.highU3c cp b k i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ) := by
    simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, heq i j]
  have hΔE : (0:ℝ) < (Δ : ℝ) ^ E := by positivity
  have hprod : 0 < (g : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4, ((IPoly.eval (cK i j) y : ℚ) : ℝ) *
      u ^ (i:ℕ) * p ^ (j:ℕ) := mul_pos hgpos (by simpa using h)
  rw [hsum] at hprod
  exact pos_of_mul_pos_right hprod hΔE.le

/-- Phases 1 and 2 with both bases as data: `decKgX3c` and the packed tree check `IPoly.checkZ`. -/
theorem coeffPos_of_decKgXZ3c (Δ eIn : ℕ) (P : Piece) (cp b : Poly) (k : Branch) (g X : ℕ)
    (cK : Fin 4 → Fin 4 → IPoly) (XZ L : ℕ) (T : IPoly.UTreeI)
    (hd : decKgX3c Δ eIn P cp b k g X cK = true) (ht : IPoly.checkZ cK XZ L T = true) :
    HighCoeffPos (P.highU3c cp b k) :=
  coeffPos_of_decKgX3c_of Δ eIn P cp b k g X cK hd (IPoly.checkZ_sound cK XZ L T ht)

end Pk

end QRH.RepeatedMarks.Faceless
