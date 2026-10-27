/- Copyright (c) 2026 Sil. Apache-2.0.
Truncated Euler products over prime ideals of the Eisenstein integers.

For a finite set `S` of nonzero prime ideals of `HeckeFamily.O` with `N P ≤ X`
for every `P ∈ S` (and `X ≥ 3`) we prove the Mertens-type bound
  `∑_{P ∈ S} 1 / N P ≤ 6 log log X + 6 log 768`,
and deduce `∏_{P ∈ S} (1 + A / N P + r P) ≤ exp (6 A log 768 + R) (log X)^(6 A)`
when `∑ r P ≤ R`, together with the subpower form `≤ X^δ` for large `X`.

Proof: with `s = 1 + 1 / log X`, `1 / N P ≤ e N P^{-s}`; `x / 2 ≤ log (1 + x)`
on `[0, 1]`; `∏ (1 + N P^{-s})` is a sum over distinct squarefree products of
the primes in `S` (distinct by primality and maximality); and any finite sum of
`N I^{-s}` over nonzero ideals is `≤ 768 log X` by a dyadic decomposition using
the baseline ideal count `#{I : N I ≤ H} ≤ 128 H`.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.Family
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.FiniteEulerFactors
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Field.GeomSum

set_option autoImplicit false

namespace QRH.DensitySplitThird.PrimeHarmonic

noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths

local notation "O" => HeckeFamily.O

/-! ### Ideal counting and the dyadic Dirichlet-series bound -/

/-- Baseline count: at most `128 H` nonzero ideals of norm `≤ H`. -/
theorem ideal_count (F : Finset (Ideal O)) (H : ℝ) (hH : 1 ≤ H)
    (hpos : ∀ I ∈ F, I ≠ ⊥) (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ H) :
    (F.card : ℝ) ≤ 128 * H := by
  have hs : F ⊆ ConcretePrimeRowBridge.idealsUpTo ⌊H⌋₊ := by
    intro I hI
    apply ConcretePrimeRowBridge.mem_idealsUpTo.mpr
    refine ⟨?_, Nat.le_floor (hN I hI)⟩
    exact Nat.one_le_iff_ne_zero.mpr (fun h => hpos I hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hc := (Finset.card_le_card hs).trans (CompactScaleBridge.idealsUpTo_card_le ⌊H⌋₊)
  have hfloor : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hr : (F.card : ℝ) ≤ 64 * ((⌊H⌋₊ : ℝ) + 1) := by exact_mod_cast hc
  linarith

/-- Dyadic decomposition: every finite partial Dirichlet sum at `1 + t` is
bounded by `256 / (1 - 2^{-t})`. -/
theorem dyadic_mass (F : Finset (Ideal O)) (hF : ∀ I ∈ F, I ≠ ⊥) (t : ℝ) (ht : 0 < t) :
    ∑ I ∈ F, (Ideal.absNorm I : ℝ) ^ (-(1 + t)) ≤ 256 / (1 - (2 : ℝ) ^ (-t)) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (2 : ℝ) ^ (-t) := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 ≤ r := hr ▸ Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := hr ▸ Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h2r : (2 : ℝ) * (2 : ℝ) ^ (-(1 + t)) = r := by
    rw [hr, show -t = 1 + (-(1 + t)) by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  let k : Ideal O → ℕ := fun I => Nat.log 2 (Ideal.absNorm I)
  let M : ℕ := F.sup (fun I => Ideal.absNorm I) + 1
  have hmaps : ∀ I ∈ F, k I ∈ Finset.range M := by
    intro I hI
    rw [Finset.mem_range]
    have h1 : Nat.log 2 (Ideal.absNorm I) ≤ Ideal.absNorm I := Nat.log_le_self 2 _
    have h2 : Ideal.absNorm I ≤ F.sup (fun I => Ideal.absNorm I) :=
      Finset.le_sup (f := fun I => Ideal.absNorm I) hI
    change Nat.log 2 (Ideal.absNorm I) < F.sup (fun I => Ideal.absNorm I) + 1
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ Finset.range M,
      ∑ I ∈ F with k I = j, (Ideal.absNorm I : ℝ) ^ (-(1 + t)) ≤ 256 * r ^ j := by
    intro j _
    have hlow : ∀ I ∈ F.filter (fun I => k I = j), (2 : ℝ) ^ j ≤ (Ideal.absNorm I : ℝ) := by
      intro I hI
      obtain ⟨hIF, hk⟩ := Finset.mem_filter.mp hI
      have hn : Ideal.absNorm I ≠ 0 := fun h => hF I hIF (Ideal.absNorm_eq_zero_iff.mp h)
      have h := Nat.pow_log_le_self 2 hn
      change Nat.log 2 (Ideal.absNorm I) = j at hk
      rw [hk] at h
      exact_mod_cast h
    have hup : ∀ I ∈ F.filter (fun I => k I = j),
        (Ideal.absNorm I : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
      intro I hI
      obtain ⟨_, hk⟩ := Finset.mem_filter.mp hI
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Ideal.absNorm I)
      change Nat.log 2 (Ideal.absNorm I) = j at hk
      rw [hk] at h
      exact_mod_cast h.le
    have hcard : ((F.filter (fun I => k I = j)).card : ℝ) ≤ 128 * (2 : ℝ) ^ (j + 1) :=
      ideal_count _ _ (one_le_pow₀ (by norm_num))
        (fun I hI => hF I (Finset.mem_filter.mp hI).1) hup
    have hterm : ∀ I ∈ F.filter (fun I => k I = j),
        (Ideal.absNorm I : ℝ) ^ (-(1 + t)) ≤ ((2 : ℝ) ^ j) ^ (-(1 + t)) :=
      fun I hI => Real.rpow_le_rpow_of_nonpos (by positivity) (hlow I hI) (by linarith)
    have hpow : (2 : ℝ) ^ (j + 1) * ((2 : ℝ) ^ j) ^ (-(1 + t)) = 2 * r ^ j := by
      rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), pow_succ, ← h2r, mul_pow]
      ring
    calc
      ∑ I ∈ F with k I = j, (Ideal.absNorm I : ℝ) ^ (-(1 + t))
          ≤ ∑ _I ∈ F with k _I = j, ((2 : ℝ) ^ j) ^ (-(1 + t)) := Finset.sum_le_sum hterm
      _ = ((F.filter (fun I => k I = j)).card : ℝ) * ((2 : ℝ) ^ j) ^ (-(1 + t)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (128 * (2 : ℝ) ^ (j + 1)) * ((2 : ℝ) ^ j) ^ (-(1 + t)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 256 * r ^ j := by rw [mul_assoc, hpow]; ring
  calc
    _ ≤ ∑ j ∈ Finset.range M, 256 * r ^ j := Finset.sum_le_sum hfib
    _ = 256 * ∑ j ∈ Finset.Ico 0 M, r ^ j := by rw [← Finset.mul_sum, Finset.range_eq_Ico]
    _ ≤ 256 * (r ^ 0 / (1 - r)) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) (by norm_num)
    _ = 256 / (1 - r) := by rw [pow_zero]; ring

/-- `1 / (1 - 2^{-t}) ≤ 3 / t` for `0 < t ≤ 1`. -/
theorem inv_one_sub_two_rpow_le (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    1 / (1 - (2 : ℝ) ^ (-t)) ≤ 3 / t := by
  have hl := Real.log_two_gt_d9
  have hl' := Real.log_two_lt_d9
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = t * Real.log 2 := ⟨_, rfl⟩
  have hu0 : 0 < u := hu ▸ mul_pos ht (by linarith)
  have hr : (2 : ℝ) ^ (-t) = Real.exp (-u) := by
    rw [Real.rpow_def_of_pos (by norm_num), hu]
    congr 1
    ring
  rw [hr]
  have he : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
  have hexp : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hepos := Real.exp_pos (-u)
  have hr1 : Real.exp (-u) * (1 + u) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left he hepos.le
    linarith
  have htu : t * Real.log 2 ≤ Real.log 2 := by nlinarith
  have hkey : 0 ≤ t * (3 * Real.log 2 - 1 - u) := mul_nonneg ht.le (by linarith)
  have hmain : 3 * Real.exp (-u) * (1 + u) ≤ (3 - t) * (1 + u) := by
    nlinarith
  have h3 : 3 * Real.exp (-u) ≤ 3 - t := le_of_mul_le_mul_right hmain (by linarith)
  have hpos : 0 < 1 - Real.exp (-u) := by nlinarith
  rw [div_le_div_iff₀ hpos ht]
  linarith

theorem one_le_log_of_three_le {X : ℝ} (hX : 3 ≤ X) : 1 ≤ Real.log X := by
  have hX0 : 0 < X := by linarith
  have he := Real.exp_one_lt_d9
  apply Real.exp_le_exp.mp
  rw [Real.exp_log hX0]
  norm_num at he
  linarith

/-- Any finite Dirichlet partial sum at `s = 1 + 1 / log X` is `≤ 768 log X`. -/
theorem mass_le_log (X : ℝ) (hX : 3 ≤ X) (F : Finset (Ideal O)) (hF : ∀ I ∈ F, I ≠ ⊥) :
    ∑ I ∈ F, (Ideal.absNorm I : ℝ) ^ (-(1 + 1 / Real.log X)) ≤ 768 * Real.log X := by
  have hL := one_le_log_of_three_le hX
  have ht : 0 < 1 / Real.log X := div_pos one_pos (by linarith)
  have ht1 : 1 / Real.log X ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hL
  calc
    _ ≤ 256 / (1 - (2 : ℝ) ^ (-(1 / Real.log X))) := dyadic_mass F hF _ ht
    _ = 256 * (1 / (1 - (2 : ℝ) ^ (-(1 / Real.log X)))) := by ring
    _ ≤ 256 * (3 / (1 / Real.log X)) :=
      mul_le_mul_of_nonneg_left (inv_one_sub_two_rpow_le _ ht ht1) (by norm_num)
    _ = 768 * Real.log X := by rw [one_div, div_inv_eq_mul]; ring

/-! ### Squarefree Euler products over distinct prime ideals -/

theorem subset_of_prod_eq {S T T' : Finset (Ideal O)} (hS : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥)
    (hT : T ⊆ S) (hT' : T' ⊆ S) (h : ∏ P ∈ T, P = ∏ P ∈ T', P) : T ⊆ T' := by
  intro Q hQ
  have hQp := (hS Q (hT hQ)).1
  have hle : ∏ P ∈ T', P ≤ Q := by
    rw [← h]
    exact Ideal.prod_le_inf.trans (Finset.inf_le (f := fun P : Ideal O => P) hQ)
  obtain ⟨P, hP, hPQ⟩ := (Ideal.IsPrime.prod_le hQp).mp hle
  have hPm : P.IsMaximal := Ideal.IsPrime.isMaximal (hS P (hT' hP)).1 (hS P (hT' hP)).2
  have hPQ' : P = Q := hPm.eq_of_le hQp.ne_top hPQ
  rw [← hPQ']
  exact hP

/-- `∏_{P ∈ S} (1 + N P^{-σ})` is a sum of `N I^{-σ}` over distinct ideals `I`. -/
theorem euler_squarefree (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥)
    (σ : ℝ) :
    ∏ P ∈ S, (1 + (Ideal.absNorm P : ℝ) ^ (-σ)) =
      ∑ I ∈ S.powerset.image (fun T => ∏ P ∈ T, P), (Ideal.absNorm I : ℝ) ^ (-σ) := by
  rw [Finset.prod_one_add, Finset.sum_image]
  · refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [map_prod, Nat.cast_prod]
    exact Real.finsetProd_rpow T _ (fun P _ => Nat.cast_nonneg _) _
  · intro T hT T' hT' h
    have hT1 : T ⊆ S := by simpa using hT
    have hT2 : T' ⊆ S := by simpa using hT'
    exact subset_antisymm (subset_of_prod_eq hS hT1 hT2 h)
      (subset_of_prod_eq hS hT2 hT1 h.symm)

theorem image_ne_bot (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥) :
    ∀ I ∈ S.powerset.image (fun T => ∏ P ∈ T, P), I ≠ ⊥ := by
  intro I hI hI0
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hI
  have hT1 : T ⊆ S := Finset.mem_powerset.mp hT
  have h0 : Ideal.absNorm (∏ P ∈ T, P) = 0 := Ideal.absNorm_eq_zero_iff.mpr hI0
  rw [map_prod] at h0
  obtain ⟨P, hP, hP0⟩ := Finset.prod_eq_zero_iff.mp h0
  exact (hS P (hT1 hP)).2 (Ideal.absNorm_eq_zero_iff.mp hP0)

/-! ### The Mertens-type bound -/

/-- Explicit Mertens-type bound over prime ideals of norm at most `X`. -/
theorem prime_harmonic_explicit (X : ℝ) (hX : 3 ≤ X) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥) (hSX : ∀ P ∈ S, (Ideal.absNorm P : ℝ) ≤ X) :
    ∑ P ∈ S, 1 / (Ideal.absNorm P : ℝ) ≤
      6 * Real.log (Real.log X) + 6 * Real.log 768 := by
  have hX0 : 0 < X := by linarith
  have hL := one_le_log_of_three_le hX
  have hL0 : 0 < Real.log X := by linarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 1 + 1 / Real.log X := ⟨_, rfl⟩
  have hσ0 : 0 ≤ σ := by rw [hσ]; have := div_pos one_pos hL0; linarith
  have hNpos : ∀ P ∈ S, (1 : ℝ) ≤ (Ideal.absNorm P : ℝ) := by
    intro P hP
    have h : Ideal.absNorm P ≠ 0 := fun h => (hS P hP).2 (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
  have ha0 : ∀ P ∈ S, 0 ≤ (Ideal.absNorm P : ℝ) ^ (-σ) :=
    fun P _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have ha1 : ∀ P ∈ S, (Ideal.absNorm P : ℝ) ^ (-σ) ≤ 1 :=
    fun P hP => Real.rpow_le_one_of_one_le_of_nonpos (hNpos P hP) (by linarith)
  -- `1 / N P ≤ e N P^{-σ}`
  have hA : ∀ P ∈ S, 1 / (Ideal.absNorm P : ℝ) ≤ 3 * (Ideal.absNorm P : ℝ) ^ (-σ) := by
    intro P hP
    have hN0 : 0 < (Ideal.absNorm P : ℝ) := by linarith [hNpos P hP]
    have he := Real.exp_one_lt_d9
    norm_num at he
    have h1 : (Ideal.absNorm P : ℝ) ^ (1 / Real.log X) ≤ 3 := by
      calc
        (Ideal.absNorm P : ℝ) ^ (1 / Real.log X) ≤ X ^ (1 / Real.log X) :=
          Real.rpow_le_rpow hN0.le (hSX P hP) (div_pos one_pos hL0).le
        _ = Real.exp 1 := by
          rw [Real.rpow_def_of_pos hX0, mul_one_div_cancel hL0.ne']
        _ ≤ 3 := by linarith
    have h2 : 1 / (Ideal.absNorm P : ℝ) =
        (Ideal.absNorm P : ℝ) ^ (1 / Real.log X) * (Ideal.absNorm P : ℝ) ^ (-σ) := by
      rw [← Real.rpow_add hN0, hσ, show 1 / Real.log X + -(1 + 1 / Real.log X) = (-1 : ℝ) by ring,
        Real.rpow_neg_one, one_div]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (ha0 P hP)
  -- `x / 2 ≤ log (1 + x)` on `[0, 1]`
  have hB : ∀ P ∈ S, (Ideal.absNorm P : ℝ) ^ (-σ) / 2 ≤
      Real.log (1 + (Ideal.absNorm P : ℝ) ^ (-σ)) := by
    intro P hP
    have h0 := ha0 P hP
    have h1 := ha1 P hP
    have hlog := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + (Ideal.absNorm P : ℝ) ^ (-σ))
    have h3 : (Ideal.absNorm P : ℝ) ^ (-σ) / 2 ≤ 1 - (1 + (Ideal.absNorm P : ℝ) ^ (-σ))⁻¹ := by
      have hpos : 0 < 1 + (Ideal.absNorm P : ℝ) ^ (-σ) := by linarith
      have hinv : (1 + (Ideal.absNorm P : ℝ) ^ (-σ))⁻¹ * (1 + (Ideal.absNorm P : ℝ) ^ (-σ)) = 1 :=
        inv_mul_cancel₀ hpos.ne'
      have hi0 : 0 < (1 + (Ideal.absNorm P : ℝ) ^ (-σ))⁻¹ := inv_pos.mpr hpos
      nlinarith
    linarith
  -- the Euler product is a partial Dirichlet sum
  have hprod : ∏ P ∈ S, (1 + (Ideal.absNorm P : ℝ) ^ (-σ)) ≤ 768 * Real.log X := by
    rw [euler_squarefree S hS σ, hσ]
    exact mass_le_log X hX _ (image_ne_bot S hS)
  have hprodpos : 0 < ∏ P ∈ S, (1 + (Ideal.absNorm P : ℝ) ^ (-σ)) :=
    Finset.prod_pos (fun P hP => by linarith [ha0 P hP])
  have hlogprod : ∑ P ∈ S, Real.log (1 + (Ideal.absNorm P : ℝ) ^ (-σ)) ≤
      Real.log 768 + Real.log (Real.log X) := by
    rw [← Real.log_prod (fun P hP => by linarith [ha0 P hP]), ← Real.log_mul (by norm_num) hL0.ne']
    exact Real.log_le_log hprodpos hprod
  have hsum : ∑ P ∈ S, (Ideal.absNorm P : ℝ) ^ (-σ) ≤
      2 * (Real.log 768 + Real.log (Real.log X)) := by
    have := Finset.sum_le_sum hB
    rw [← Finset.sum_div] at this
    linarith
  calc
    ∑ P ∈ S, 1 / (Ideal.absNorm P : ℝ) ≤ ∑ P ∈ S, 3 * (Ideal.absNorm P : ℝ) ^ (-σ) :=
      Finset.sum_le_sum hA
    _ = 3 * ∑ P ∈ S, (Ideal.absNorm P : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ 3 * (2 * (Real.log 768 + Real.log (Real.log X))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

/-- Target (1): Mertens-type bound `∑_{P ∈ S} 1 / N P ≤ c log log X + C`. -/
theorem prime_harmonic :
    ∃ c C : ℝ, 0 ≤ c ∧ 0 ≤ C ∧ ∀ X : ℝ, 3 ≤ X → ∀ S : Finset (Ideal O),
      (∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥) → (∀ P ∈ S, (Ideal.absNorm P : ℝ) ≤ X) →
      ∑ P ∈ S, 1 / (Ideal.absNorm P : ℝ) ≤ c * Real.log (Real.log X) + C :=
  ⟨6, 6 * Real.log 768, by norm_num,
    mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)),
    fun X hX S hS hSX => prime_harmonic_explicit X hX S hS hSX⟩

/-! ### Euler-product consequences -/

/-- Target (2), with a remainder: if `0 ≤ f P ≤ 1 + A / N P + r P` on `S` and
`∑_{P ∈ S} r P ≤ R`, then `∏_{P ∈ S} f P ≤ exp (6 A log 768 + R) (log X)^(6 A)`. -/
theorem euler_product_bound (A R : ℝ) (hA : 0 ≤ A) (X : ℝ) (hX : 3 ≤ X)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥)
    (hSX : ∀ P ∈ S, (Ideal.absNorm P : ℝ) ≤ X)
    (f r : Ideal O → ℝ) (hf0 : ∀ P ∈ S, 0 ≤ f P)
    (hf : ∀ P ∈ S, f P ≤ 1 + A / (Ideal.absNorm P : ℝ) + r P)
    (hR : ∑ P ∈ S, r P ≤ R) :
    ∏ P ∈ S, f P ≤ Real.exp (A * (6 * Real.log 768) + R) * Real.log X ^ (A * 6) := by
  have hL0 : 0 < Real.log X := by linarith [one_le_log_of_three_le hX]
  have hH := prime_harmonic_explicit X hX S hS hSX
  calc
    ∏ P ∈ S, f P ≤ ∏ P ∈ S, Real.exp (A * (1 / (Ideal.absNorm P : ℝ)) + r P) := by
      apply Finset.prod_le_prod₀ hf0
      intro P hP
      have := Real.add_one_le_exp (A * (1 / (Ideal.absNorm P : ℝ)) + r P)
      have he : A / (Ideal.absNorm P : ℝ) = A * (1 / (Ideal.absNorm P : ℝ)) := by ring
      linarith [hf P hP]
    _ = Real.exp (A * ∑ P ∈ S, 1 / (Ideal.absNorm P : ℝ) + ∑ P ∈ S, r P) := by
      rw [← Real.exp_sum, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ Real.exp (A * (6 * Real.log (Real.log X) + 6 * Real.log 768) + R) :=
      Real.exp_le_exp.mpr (add_le_add (mul_le_mul_of_nonneg_left hH hA) hR)
    _ = _ := by
      rw [show A * (6 * Real.log (Real.log X) + 6 * Real.log 768) + R =
          (A * (6 * Real.log 768) + R) + Real.log (Real.log X) * (A * 6) by ring,
        Real.exp_add, Real.rpow_def_of_pos hL0]

/-- Target (2), plain form: `∏_{P ∈ S} (1 + A / N P) ≤ exp (6 A log 768) (log X)^(6 A)`. -/
theorem euler_product_bound_plain (A : ℝ) (hA : 0 ≤ A) (X : ℝ) (hX : 3 ≤ X)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥)
    (hSX : ∀ P ∈ S, (Ideal.absNorm P : ℝ) ≤ X) :
    ∏ P ∈ S, (1 + A / (Ideal.absNorm P : ℝ)) ≤
      Real.exp (A * (6 * Real.log 768)) * Real.log X ^ (A * 6) := by
  have h := euler_product_bound A 0 hA X hX S hS hSX
    (fun P => 1 + A / (Ideal.absNorm P : ℝ)) (fun _ => 0)
    (fun P _ => add_nonneg zero_le_one (div_nonneg hA (Nat.cast_nonneg _)))
    (fun P _ => by simp) (by simp)
  simpa using h

/-- Target (2), existential form with the constants of target (1). -/
theorem euler_product_bound_exists :
    ∃ c C : ℝ, 0 ≤ c ∧ 0 ≤ C ∧ ∀ A R : ℝ, 0 ≤ A → ∀ X : ℝ, 3 ≤ X →
      ∀ S : Finset (Ideal O), (∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥) →
      (∀ P ∈ S, (Ideal.absNorm P : ℝ) ≤ X) →
      ∀ f r : Ideal O → ℝ, (∀ P ∈ S, 0 ≤ f P) →
      (∀ P ∈ S, f P ≤ 1 + A / (Ideal.absNorm P : ℝ) + r P) → ∑ P ∈ S, r P ≤ R →
      ∏ P ∈ S, f P ≤ Real.exp (A * C + R) * Real.log X ^ (A * c) :=
  ⟨6, 6 * Real.log 768, by norm_num,
    mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)),
    fun A R hA X hX S hS hSX f r hf0 hf hR =>
      euler_product_bound A R hA X hX S hS hSX f r hf0 hf hR⟩

/-- Target (3): the Euler product is subpower in `X`, uniformly in the prime set. -/
theorem euler_product_subpower (A R δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ X0 : ℝ, 3 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X → ∀ S : Finset (Ideal O),
      (∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥) → (∀ P ∈ S, (Ideal.absNorm P : ℝ) ≤ X) →
      ∀ f r : Ideal O → ℝ, (∀ P ∈ S, 0 ≤ f P) →
      (∀ P ∈ S, f P ≤ 1 + A / (Ideal.absNorm P : ℝ) + r P) → ∑ P ∈ S, r P ≤ R →
      ∏ P ∈ S, f P ≤ X ^ δ := by
  set K : ℝ := Real.exp (A * (6 * Real.log 768) + R) with hK
  have hK0 : 0 < K := Real.exp_pos _
  have ho := (isLittleO_log_rpow_rpow_atTop (A * 6) hδ).bound (one_div_pos.mpr hK0)
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp ho
  refine ⟨max X1 3, le_max_right _ _, ?_⟩
  intro X hX S hS hSX f r hf0 hf hR
  have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
  have hb := hX1 X ((le_max_left _ _).trans hX)
  have hXd : 0 ≤ X ^ δ := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg hXd] at hb
  have hle : Real.log X ^ (A * 6) ≤ 1 / K * X ^ δ := (Real.le_norm_self _).trans hb
  calc
    ∏ P ∈ S, f P ≤ K * Real.log X ^ (A * 6) :=
      euler_product_bound A R hA X hX3 S hS hSX f r hf0 hf hR
    _ ≤ K * (1 / K * X ^ δ) := mul_le_mul_of_nonneg_left hle hK0.le
    _ = X ^ δ := by field_simp

end

end QRH.DensitySplitThird.PrimeHarmonic
