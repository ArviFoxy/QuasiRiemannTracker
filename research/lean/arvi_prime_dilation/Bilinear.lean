/-
Bilinear forms `∑_s ∑_q u(s) v(q) conj (q^2 / s)_6` against the sextic row
`rowValue (q^2) s`, bounded by the unconditional optimal sextic large sieve
`SieveOptimal.optimal_bound` after a single Cauchy--Schwarz in the `q` variable.

* `bilinear_cs` : the pure Cauchy--Schwarz step (no arithmetic input).
* `sq_injective`, `powerFree_six_sq` : squaring is injective on ideals of `O`, and `q^2` is
  sixth-power-free as soon as `q` is cube-free (in particular when `q` is squarefree).
* `bilinear_sieve`, `bilinear_sieve_squarefree` : the sieve bound, with a constant depending
  only on `ε`.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SieveOptimal

set_option autoImplicit false
namespace QRH.ArviPrimeDilation
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve
open Candidate.FourthPower Candidate.FourthPower.SexticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- Pure Cauchy--Schwarz in the `q` variable. No arithmetic input. -/
theorem bilinear_cs (Ss Qs : Finset Id) (u v : Id → ℂ) :
    ‖∑ s ∈ Ss, ∑ q ∈ Qs, u s * v q * star (rowValue (q^2) s)‖^2 ≤
      (∑ q ∈ Qs, ‖v q‖^2) *
        ∑ q ∈ Qs, ‖∑ s ∈ Ss, star (u s) * rowValue (q^2) s‖^2 := by
  have h1 : ∑ s ∈ Ss, ∑ q ∈ Qs, u s * v q * star (rowValue (q^2) s) =
      ∑ q ∈ Qs, v q * star (∑ s ∈ Ss, star (u s) * rowValue (q^2) s) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [star_mul, star_star]
    ring
  rw [h1]
  set w : Id → ℂ := fun q => ∑ s ∈ Ss, star (u s) * rowValue (q^2) s
  have ht : ‖∑ q ∈ Qs, v q * star (w q)‖ ≤ ∑ q ∈ Qs, ‖v q‖ * ‖w q‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro q _
    rw [norm_mul, norm_star]
  have hs := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
    (fun q _ => mul_nonneg (norm_nonneg (v q)) (norm_nonneg (w q))))).mpr ht
  exact hs.trans (Finset.sum_mul_sq_le_sq_mul_sq Qs (fun q => ‖v q‖) (fun q => ‖w q‖))

/-- Squaring is injective on ideals of the Dedekind domain `O` (unique factorization). -/
theorem sq_injective {A B : Id} (h : A^2 = B^2) : A = B := by
  have h1 : A ∣ B :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (two_ne_zero : (2 : ℕ) ≠ 0)).mp (h ▸ dvd_refl _)
  have h2 : B ∣ A :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (two_ne_zero : (2 : ℕ) ≠ 0)).mp (h ▸ dvd_refl _)
  exact le_antisymm (Ideal.dvd_iff_le.mp h2) (Ideal.dvd_iff_le.mp h1)

/-- `q^2` is sixth-power-free as soon as `q` is cube-free. -/
theorem powerFree_six_sq {q : Id} (hq : PowerFree 3 q) : PowerFree 6 (q^2) := by
  intro P hP hd
  apply hq P hP
  have h6 : (P^3)^2 = P^6 := (pow_mul P 3 2).symm
  rw [← h6] at hd
  exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (two_ne_zero : (2 : ℕ) ≠ 0)).mp hd

/-- Squarefree `q` (`PowerFree 2 q`) has sixth-power-free square. -/
theorem powerFree_six_sq_of_squarefree {q : Id} (hq : PowerFree 2 q) : PowerFree 6 (q^2) :=
  powerFree_six_sq (powerFree_mono (by norm_num) hq)

/-- The sieve form. The constant depends on `ε` only. The `q`-side ideals enter through
their squares `q^2`, which must be supported and sixth-power-free (for instance because `q` is
supported and squarefree, see `powerFree_six_sq_of_squarefree`); `P2` bounds `N(q^2)` and `X`
bounds `N(s)`. -/
theorem bilinear_sieve (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P2 X : ℝ) (Ss Qs : Finset Id) (u v : Id → ℂ),
      (∀ q ∈ Qs, Supported q ∧ PowerFree 6 (q^2) ∧ (Ideal.absNorm (q^2) : ℝ) ≤ P2) →
      (∀ s ∈ Ss, Supported s ∧ PowerFree 6 s ∧ (Ideal.absNorm s : ℝ) ≤ X) →
      ‖∑ s ∈ Ss, ∑ q ∈ Qs, u s * v q * star (rowValue (q^2) s)‖^2 ≤
        C * (P2 * X)^ε * majorant P2 X * (∑ q ∈ Qs, ‖v q‖^2) * ∑ s ∈ Ss, ‖u s‖^2 := by
  obtain ⟨C, hC, hb⟩ := SieveOptimal.optimal_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro P2 X Ss Qs u v hQ hS
  by_cases hQe : Qs = ∅
  · subst hQe
    simp
  by_cases hSe : Ss = ∅
  · subst hSe
    simp
  obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hQe
  obtain ⟨s₀, hs₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
  have hnorm_pos : ∀ I : Id, I ≠ 0 → (1 : ℝ) ≤ Ideal.absNorm I := fun I hI =>
    Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  have hP2 : 1 ≤ P2 := by
    obtain ⟨hs, -, hn⟩ := hQ q₀ hq₀
    exact (hnorm_pos _ (pow_ne_zero 2 hs.1)).trans hn
  have hX : 1 ≤ X := by
    obtain ⟨hs, -, hn⟩ := hS s₀ hs₀
    exact (hnorm_pos _ hs.1).trans hn
  have hinj : Set.InjOn (fun q : Id => q^2) (Qs : Set Id) := fun a _ b _ h => sq_injective h
  have hE : ∑ q ∈ Qs, ‖∑ s ∈ Ss, star (u s) * rowValue (q^2) s‖^2 =
      energy (Qs.image (fun q : Id => q^2)) Ss (fun s => star (u s)) := by
    unfold energy
    rw [Finset.sum_image hinj]
  have hrows : ∀ R ∈ Qs.image (fun q : Id => q^2),
      Supported R ∧ PowerFree 6 R ∧ (Ideal.absNorm R : ℝ) ≤ P2 := by
    intro R hR
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨h1, h2, h3⟩ := hQ q hq
    exact ⟨(supported_sq_iff q).mpr h1, h2, h3⟩
  have hopt := hb P2 X hP2 hX _ Ss hrows hS (fun s => star (u s))
  have hmass : coefficientMass Ss (fun s => star (u s)) = ∑ s ∈ Ss, ‖u s‖^2 := by
    unfold coefficientMass
    simp only [norm_star]
  rw [hmass] at hopt
  refine (bilinear_cs Ss Qs u v).trans ?_
  rw [hE]
  calc
    _ ≤ (∑ q ∈ Qs, ‖v q‖^2) * (C * (P2 * X)^ε * majorant P2 X * ∑ s ∈ Ss, ‖u s‖^2) :=
      mul_le_mul_of_nonneg_left hopt (Finset.sum_nonneg (fun q _ => sq_nonneg _))
    _ = _ := by ring

/-- The same bound for squarefree `q` (`PowerFree 2 q`), with `N(q)^2 ≤ P2`. -/
theorem bilinear_sieve_squarefree (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P2 X : ℝ) (Ss Qs : Finset Id) (u v : Id → ℂ),
      (∀ q ∈ Qs, Supported q ∧ PowerFree 2 q ∧ (Ideal.absNorm q : ℝ)^2 ≤ P2) →
      (∀ s ∈ Ss, Supported s ∧ PowerFree 6 s ∧ (Ideal.absNorm s : ℝ) ≤ X) →
      ‖∑ s ∈ Ss, ∑ q ∈ Qs, u s * v q * star (rowValue (q^2) s)‖^2 ≤
        C * (P2 * X)^ε * majorant P2 X * (∑ q ∈ Qs, ‖v q‖^2) * ∑ s ∈ Ss, ‖u s‖^2 := by
  obtain ⟨C, hC, hb⟩ := bilinear_sieve ε hε
  refine ⟨C, hC, ?_⟩
  intro P2 X Ss Qs u v hQ hS
  refine hb P2 X Ss Qs u v ?_ hS
  intro q hq
  obtain ⟨h1, h2, h3⟩ := hQ q hq
  refine ⟨h1, powerFree_six_sq_of_squarefree h2, ?_⟩
  rw [map_pow, Nat.cast_pow]
  exact h3

end
end QRH.ArviPrimeDilation

#print axioms QRH.ArviPrimeDilation.bilinear_cs
#print axioms QRH.ArviPrimeDilation.bilinear_sieve
#print axioms QRH.ArviPrimeDilation.bilinear_sieve_squarefree
