/- Copyright (c) 2026 Sil. Apache-2.0.
Seam 0, analytic half: the SUMMED smoothed-window energy (CF §4).

OAI `smoothed_window_energy_from_height` turns one height-uniform Gauss energy bound into a
bound for the smoothed log-window energy of that one column family. CF keeps the first
artificial-divisor sum `∑_u` inside the Cauchy inequality, so the side contract only bounds
the SUM over `u ∈ Us` of the height energies. The window integral is then taken jointly on the
row type `Us × O`: the same proof, with the finite row family indexed by pairs `(u, z)`.
This file is generic (OAI only); the cube-free raw energies are plugged in downstream. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy

set_option autoImplicit false
namespace QRH.SilDensitySplit.CubeFree.First
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy CenteredMomentSmoothedWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

/-- A sum over the joint finite row type `Us × rows` is the iterated finset sum. -/
theorem sum_joint_rows {κ ρ : Type*} (Us : Finset κ) (rows : Finset ρ) (F : κ → ρ → ℝ) :
    (∑ p : Us × rows, F p.1 p.2) = ∑ k ∈ Us, ∑ z ∈ rows, F k z := by
  rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort Us]
  exact Finset.sum_congr rfl (fun k _ => Finset.sum_coe_sort rows (F k))

/-- The finite sum over `Us` of the (real) Gauss energies is the sum of the pointwise sums. -/
theorem summed_gaussEnergy_hasSum_re {κ α : Type*} (Us : Finset κ) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : κ → α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    HasSum (fun z : O => ∑ k ∈ Us, ‖gaussPolynomial S a ha (c k) z‖^2*
      (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
      (∑ k ∈ Us, (gaussEnergy S a ha (c k) U K).re) :=
  hasSum_sum (fun k _ => gaussEnergy_hasSum_re S a ha (c k) U K hK)

/-- Joint (row type `Us × O`) form of OAI `smoothed_window_energy_from_shifted`: a bound on
the SUM over `Us` of the shifted height energies bounds the SUM of the window energies. -/
theorem summed_smoothed_window_energy_from_shifted {κ α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (Us : Finset κ) (S : Finset α) (a : α → O) (ha : ∀ i, Supported (Ideal.span {a i}))
    (β : κ → α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0 < X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hU : ∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ w : ℝ, (∑ k ∈ Us, (gaussEnergy S a ha
      (fun i => β k i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K).re) ≤
        E*(1+‖w‖)^(2*J)) :
    (∑ k ∈ Us, (gaussEnergy S a ha (fun i => β k i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ)
        U K).re) ≤
      E*(∫ w : ℝ, (1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun z : O => (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re
  let c := fun k i => β k i*heightCoeff τ t (Ideal.span {a i})*
    CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ
  have hnorm (z : O) (x : ℂ) : ‖(Real.sqrt (u z):ℂ)*x‖^2 = u z*‖x‖^2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (hU z)]
  have hfin (rows : Finset O) :
      (∑ z ∈ rows, ∑ k ∈ Us, ‖gaussPolynomial S a ha (c k) z‖^2*u z) ≤
        E*(∫ w : ℝ, (1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun p : Us × rows => fun w : ℝ => (Real.sqrt (u p.2):ℂ)*
      (logPhase (θ-w) (Real.log X)*gaussPolynomial S a ha
        (fun i => β p.1 i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) p.2)
    have hi (p : Us × rows) : Integrable (fun w => columnDensity V hVc hVs w*φ p w) := by
      have h := (gauss_column_integrable S a ha (β p.1) τ t θ X hX V hVc hVs p.2).const_mul
        (Real.sqrt (u p.2):ℂ)
      convert h using 1
      funext w
      dsimp only [φ]
      ring
    have hb (w : ℝ) : (∑ p : Us × rows, ‖φ p w‖^2) ≤ E*((1+‖w‖)^J)^2 := by
      let g := fun (k : κ) (z : O) => ‖gaussPolynomial S a ha
        (fun i => β k i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2*u z
      have hφ (p : Us × rows) : ‖φ p w‖^2 = g p.1 p.2 := by
        dsimp only [φ, g]
        rw [hnorm, norm_mul, logPhase_norm]
        ring
      calc
        (∑ p : Us × rows, ‖φ p w‖^2) = ∑ p : Us × rows, g p.1 p.2 :=
          Finset.sum_congr rfl (fun p _ => hφ p)
        _ = ∑ k ∈ Us, ∑ z ∈ rows, g k z := sum_joint_rows Us rows g
        _ ≤ ∑ k ∈ Us, (gaussEnergy S a ha
            (fun i => β k i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K).re :=
          Finset.sum_le_sum (fun k _ => finite_weighted_le_gaussEnergy S a ha _ U K hK hU rows)
        _ ≤ E*(1+‖w‖)^(2*J) := henergy w
        _ = E*((1+‖w‖)^J)^2 := by rw [← pow_mul, Nat.mul_comm]
    have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
      (fun w => (1+‖w‖)^J) (by intro w; positivity) E hE (columnDensity_moments V hVc hVs J) hi hb
    have he (p : Us × rows) : (∫ w : ℝ, columnDensity V hVc hVs w*φ p w) =
        (Real.sqrt (u p.2):ℂ)*gaussPolynomial S a ha (c p.1) p.2 := by
      rw [show gaussPolynomial S a ha (c p.1) p.2 = _ from
        gauss_column_integral S a ha (β p.1) τ t θ X hX V hVc hVs p.2, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    calc
      (∑ z ∈ rows, ∑ k ∈ Us, ‖gaussPolynomial S a ha (c k) z‖^2*u z) =
          ∑ k ∈ Us, ∑ z ∈ rows, ‖gaussPolynomial S a ha (c k) z‖^2*u z := Finset.sum_comm
      _ = ∑ p : Us × rows, ‖gaussPolynomial S a ha (c p.1) p.2‖^2*u p.2 :=
        (sum_joint_rows Us rows (fun k z => ‖gaussPolynomial S a ha (c k) z‖^2*u z)).symm
      _ = ∑ p : Us × rows, ‖∫ w : ℝ, columnDensity V hVc hVs w*φ p w‖^2 :=
        Finset.sum_congr rfl (fun p _ => by rw [he p, hnorm]; ring)
      _ ≤ _ := hh
  have hs := summed_gaussEnergy_hasSum_re Us S a ha c U K hK
  rw [← hs.tsum_eq]
  exact Real.tsum_le_of_sum_le
    (fun z => Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (hU z))) hfin

/-- Summed form of OAI `smoothed_window_energy_from_height` (design:
`summed_window_energy_from_height`): `∀ v, ∑_u gaussEnergy_u(v) ≤ E(1+|v|)^{2J}` bounds the
summed smoothed window energies, with the same constant as the single-family lemma. -/
theorem summed_window_energy_from_height {κ α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (Us : Finset κ) (S : Finset α) (a : α → O) (ha : ∀ i, Supported (Ideal.span {a i}))
    (β : κ → α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0 < X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hU : ∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ v : ℝ, (∑ k ∈ Us, (gaussEnergy S a ha
      (fun i => β k i*heightCoeff τ v (Ideal.span {a i})) U K).re) ≤ E*(1+‖v‖)^(2*J)) :
    (∑ k ∈ Us, (gaussEnergy S a ha (fun i => β k i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ)
        U K).re) ≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ, (1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply summed_smoothed_window_energy_from_shifted V hVc hVs J Us S a ha β τ t θ X hX U K hK hU
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow, mul_assoc]

end
end QRH.SilDensitySplit.CubeFree.First
