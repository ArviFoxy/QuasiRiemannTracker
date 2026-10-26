/- Mixed source step, L3 (collisions): new in this submission; uses Collet's and the
transfer's definitions by import.

Splitting the collision part of a source by its exact collision pattern.

* `patMask J Q σ v`: every slot `j ∈ Q` divides the plain `σ j`, and the remaining
  selected slots `J \ Q` are coprime to the ordinary pair.
* `colPart_patterns`: on the box, `colPart J tc = Σ_{(Q,σ), Q ≠ ∅} tc · patMask J Q σ`
  (for nonzero tuples the pattern is unique: the plains are squarefree).
* `pattern_sum`: the tuples of a pattern are exactly the collision tuples
  `collTuple Q σ u a`, `u ∈ selBox Q`, `a` in the family box (`Finset.sum_bij_ne_zero`).
* `coll_factor_mask`: on them `tc · patMask = selWeight(u) · noColPart (J∖Q) tc_fam`. -/
import Submissions.arvi_mixed_step.Collision.CollTuple

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Collision
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103TwoIdeal
open QRH.Record1252270103Source.High QRH.MixedStep.Transfer
local notation "O" => ActualEisensteinCubic.O

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The exact collision pattern `(Q, σ)` of a tuple relative to the block `J`. -/
def patMask (J Q : Finset κ) (σ : Q → Fin 2) (v : Tuple κ) : ℂ :=
  if (∀ j : Q, v (Sum.inl j.val) ∣ v (Sum.inr (σ j))) ∧
      IsCoprime (∏ j ∈ J \ Q, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1)) then 1 else 0

/-- Nonempty collision patterns inside `J`. -/
def patterns (J : Finset κ) : Finset (Σ Q : Finset κ, Q → Fin 2) :=
  (J.powerset.filter (fun Q => Q.Nonempty)).sigma (fun _ => Finset.univ)

def collSet (J : Finset κ) (v : Tuple κ) : Finset κ :=
  J.filter (fun j => v (Sum.inl j) ∣ v (Sum.inr 0) * v (Sum.inr 1))

def collSide (v : Tuple κ) (j : κ) : Fin 2 := if v (Sum.inl j) ∣ v (Sum.inr 0) then 0 else 1

theorem coprime_or_dvd {P I : Ideal O} (hP : Prime P) : IsCoprime P I ∨ P ∣ I := by
  by_cases h : P ∣ I
  · exact Or.inr h
  · exact Or.inl (coprime_of_prime_not_dvd hP h)

theorem not_coprime_of_dvd {P I : Ideal O} (hP : Prime P) (h : P ∣ I) : ¬IsCoprime P I := by
  intro hc
  exact hP.not_isUnit (isUnit_of_dvd_one ((hc.isUnit_of_dvd' (dvd_refl P) h).dvd))

theorem patMask_eq (J Q : Finset κ) (hQJ : Q ⊆ J) (σ : Q → Fin 2) (v : Tuple κ)
    (hp : ∀ j ∈ J, Prime (v (Sum.inl j))) (hsq : Squarefree (v (Sum.inr 0) * v (Sum.inr 1))) :
    patMask J Q σ v =
      if Q = collSet J v ∧ ∀ j : Q, σ j = collSide v j.val then 1 else 0 := by
  unfold patMask
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    have hside : ∀ j : Q, σ j = collSide v j.val := by
      intro j
      have hj := h1 j
      unfold collSide
      by_cases h0 : v (Sum.inl j.val) ∣ v (Sum.inr 0)
      · simp only [h0, ↓reduceIte]
        by_contra hne
        have hs1 : σ j = 1 := (fin2_ne_zero_iff _).mp hne
        rw [hs1] at hj
        have hpj := hp j.val (hQJ j.property)
        exact hpj.not_isUnit (hsq _ (mul_dvd_mul h0 hj))
      · simp only [h0, ↓reduceIte]
        by_contra hne
        have hs0 : σ j = 0 := by
          by_contra h'
          exact hne ((fin2_ne_zero_iff _).mp h')
        rw [hs0] at hj
        exact h0 hj
    refine ⟨?_, hside⟩
    ext j
    simp only [collSet, Finset.mem_filter]
    constructor
    · intro hj
      refine ⟨hQJ hj, ?_⟩
      have h := h1 ⟨j, hj⟩
      have hc : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
      rcases hc (σ ⟨j, hj⟩) with h0 | h0
      · rw [h0] at h
        exact h.trans (dvd_mul_right _ _)
      · rw [h0] at h
        exact h.trans (dvd_mul_left _ _)
    · rintro ⟨hjJ, hdvd⟩
      by_contra hjQ
      have hmem : j ∈ J \ Q := Finset.mem_sdiff.mpr ⟨hjJ, hjQ⟩
      have hc : IsCoprime (v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1)) :=
        h2.of_isCoprime_of_dvd_left (Finset.dvd_prod_of_mem _ hmem)
      exact not_coprime_of_dvd (hp j hjJ) hdvd hc
  · rintro ⟨hQ, hσ⟩
    refine ⟨?_, ?_⟩
    · intro j
      have hjc : j.val ∈ collSet J v := hQ ▸ j.property
      have hd := (Finset.mem_filter.mp hjc).2
      rw [hσ j]
      unfold collSide
      by_cases h0 : v (Sum.inl j.val) ∣ v (Sum.inr 0)
      · simp only [h0, ↓reduceIte]
      · simp only [h0, ↓reduceIte]
        rcases (hp j.val (hQJ j.property)).dvd_or_dvd hd with h | h
        · exact absurd h h0
        · exact h
    · apply IsCoprime.prod_left
      intro j hj
      obtain ⟨hjJ, hjQ⟩ := Finset.mem_sdiff.mp hj
      rcases coprime_or_dvd (I := v (Sum.inr 0) * v (Sum.inr 1)) (hp j hjJ) with h | h
      · exact h
      · exfalso
        apply hjQ
        rw [hQ]
        exact Finset.mem_filter.mpr ⟨hjJ, h⟩

/-- Exactly one nonempty pattern matches a colliding nonzero tuple. -/
theorem pattern_count (J : Finset κ) (v : Tuple κ) (hp : ∀ j ∈ J, Prime (v (Sum.inl j)))
    (hsq : Squarefree (v (Sum.inr 0) * v (Sum.inr 1))) :
    ∑ p ∈ patterns J, patMask J p.1 p.2 v = if (collSet J v).Nonempty then 1 else 0 := by
  unfold patterns
  rw [Finset.sum_sigma]
  have hinner : ∀ Q ∈ J.powerset.filter (fun Q => Q.Nonempty),
      ∑ σ ∈ (Finset.univ : Finset (Q → Fin 2)), patMask J Q σ v =
        if Q = collSet J v then 1 else 0 := by
    intro Q hQ
    have hQJ : Q ⊆ J := Finset.mem_powerset.mp (Finset.mem_filter.mp hQ).1
    rw [Finset.sum_congr rfl (fun σ _ => patMask_eq J Q hQJ σ v hp hsq)]
    by_cases hc : Q = collSet J v
    · simp only [hc, true_and, ↓reduceIte]
      have h1 : ∀ σ : Q → Fin 2, (∀ j : Q, σ j = collSide v j.val) ↔
          σ = fun j => collSide v j.val := fun σ => ⟨fun h => funext h, fun h j => by rw [h]⟩
      simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    · simp only [hc, false_and, ↓reduceIte, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
  congr 1
  apply propext
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨Finset.filter_subset _ _, h⟩⟩

/-- **The collision part splits by exact pattern.** -/
theorem colPart_patterns (J : Finset κ) (β : Tuple κ → ℂ) (v : Tuple κ)
    (hβ : β v ≠ 0 → (∀ j ∈ J, Prime (v (Sum.inl j))) ∧
      Squarefree (v (Sum.inr 0) * v (Sum.inr 1))) :
    colPart J β v = ∑ p ∈ patterns J, β v * patMask J p.1 p.2 v := by
  by_cases hz : β v = 0
  · simp only [colPart, hz, zero_mul, Finset.sum_const_zero]
  obtain ⟨hp, hsq⟩ := hβ hz
  rw [← Finset.mul_sum, pattern_count J v hp hsq]
  unfold colPart noColMask
  congr 1
  have hiff : IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1)) ↔
      ¬(collSet J v).Nonempty := by
    rw [Finset.not_nonempty_iff_eq_empty]
    unfold collSet
    rw [Finset.filter_eq_empty_iff]
    constructor
    · intro h j hj hd
      exact not_coprime_of_dvd (hp j hj) hd
        (h.of_isCoprime_of_dvd_left (Finset.dvd_prod_of_mem _ hj))
    · intro h
      apply IsCoprime.prod_left
      intro j hj
      rcases coprime_or_dvd (I := v (Sum.inr 0) * v (Sum.inr 1)) (hp j hj) with hc | hd
      · exact hc
      · exact absurd hd (h hj)
  by_cases hne : (collSet J v).Nonempty
  · have hc : ¬IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1)) :=
      fun h => hiff.mp h hne
    simp only [hc, hne, ↓reduceIte, sub_zero]
  · have hc : IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1)) := hiff.mpr hne
    simp only [hc, hne, ↓reduceIte, sub_self]

/-- Nonzero tuple coefficients give prime slots and squarefree plains. -/
theorem tc_structure (s : Input κ) (J : Finset κ) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
    (v : Tuple κ) (hv : v ∈ Fintype.piFinset s.pools)
    (hne : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0) :
    (∀ j ∈ J, Prime (v (Sum.inl j))) ∧ Squarefree (v (Sum.inr 0) * v (Sum.inr 1)) := by
  have hmod := left_ne_zero_of_mul hne
  refine ⟨fun j _ => s.prime j _ (Fintype.mem_piFinset.mp hv (Sum.inl j)), ?_⟩
  exact (markedSourceModifier_nonzero A₁ A₂ Dc K F v hmod).2

/-- Distinct marked slots of a squarefree marked product are coprime. -/
theorem marked_coprime (v : Tuple κ) (hsq : Squarefree (markedProduct v)) (i j : κ)
    (hij : i ≠ j) : IsCoprime (v (Sum.inl i)) (v (Sum.inl j)) := by
  have h : v (Sum.inl i) * v (Sum.inl j) ∣ markedProduct v := by
    unfold markedProduct
    rw [← Finset.mul_prod_erase Finset.univ (fun k => v (Sum.inl k)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => v (Sum.inl k))
        (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩), ← mul_assoc]
    exact dvd_mul_right _ _
  exact isCoprime_of_isRelPrime (squarefree_mul_iff.mp (Squarefree.squarefree_of_dvd h hsq)).1

/-- The proof that the side products of a selected assignment are nonzero. -/
theorem collH (s : Input κ) (Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q})
    (k : Fin 2) : sideProd σ x.1 k ≠ 0 :=
  sideProd_ne_zero σ x.1
    (fun j => (s.prime j.val (x.1 j) (Fintype.mem_piFinset.mp x.2 j)).ne_zero) k

/-- The family box of a selected assignment. -/
def collBox (s : Input κ) (Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q}) :
    Finset (Tuple {i // i ∉ Q}) :=
  Fintype.piFinset (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1)).pools

/-- **The tuples of a pattern are the collision tuples.** -/
theorem pattern_sum (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (Φ : Tuple κ → ℂ) :
    ∑ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v *
          patMask J Q σ v * Φ v =
      ∑ x ∈ (selBox s Q).attach, ∑ a ∈ collBox s Q σ x,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
            (collTuple Q σ x.1 a) * patMask J Q σ (collTuple Q σ x.1 a) *
          Φ (collTuple Q σ x.1 a) := by
  rw [Finset.sum_sigma']
  symm
  apply Finset.sum_bij_ne_zero (fun p _ _ => collTuple Q σ p.1.1 p.2)
  · intro p hp _
    obtain ⟨_, ha⟩ := Finset.mem_sigma.mp hp
    exact collTuple_mem s Q σ p.1.1 _ _ p.1.2 p.2 ha
  · intro p hp _ q hq _ hpq
    have hx : p.1.1 = q.1.1 := by
      have h1 := collTuple_sel Q σ p.1.1 p.2
      have h2 := collTuple_sel Q σ q.1.1 q.2
      rw [← h1, ← h2]
      exact congrArg (selPart Q) hpq
    obtain ⟨⟨x, hxm⟩, a⟩ := p
    obtain ⟨⟨y, hym⟩, b⟩ := q
    change x = y at hx
    change collTuple Q σ x a = collTuple Q σ y b at hpq
    subst hx
    have hab : a = b := by
      funext z
      cases z with
      | inl i =>
        have h := congrFun hpq (Sum.inl i.val)
        unfold collTuple at h
        rwa [joinTuple_inl_not_mem Q _ _ i.val i.property,
          joinTuple_inl_not_mem Q _ _ i.val i.property] at h
      | inr k =>
        have h := congrFun hpq (Sum.inr k)
        rw [collTuple_inr, collTuple_inr] at h
        exact mul_left_cancel₀ (collH s Q σ ⟨x, hxm⟩ k) h
    subst hab
    rfl
  · intro v hv hne
    have htc : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 :=
      left_ne_zero_of_mul (left_ne_zero_of_mul hne)
    have hpat : patMask J Q σ v ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
    have hpat' : (∀ j : Q, v (Sum.inl j.val) ∣ v (Sum.inr (σ j))) := by
      unfold patMask at hpat
      by_contra hn
      apply hpat
      simp only [hn, false_and, ↓reduceIte]
    have hsqm := (markedSourceModifier_nonzero A₁ A₂ Dc K F v (left_ne_zero_of_mul htc)).1
    have hv' := (mem_pools_iff s v).mp (Fintype.mem_piFinset.mp hv)
    have hsel : selPart Q v ∈ selBox s Q :=
      Fintype.mem_piFinset.mpr (fun j => hv'.1 j.val)
    let x : {u // u ∈ selBox s Q} := ⟨selPart Q v, hsel⟩
    have hdiv : ∀ k : Fin 2, sideProd σ (selPart Q v) k ∣ v (Sum.inr k) := by
      intro k
      unfold sideProd
      apply Finset.prod_dvd_of_coprime
      · intro i _ j _ hij
        exact marked_coprime v hsqm i.val j.val (fun h => hij (Subtype.ext h))
      · intro j hj
        have h := hpat' j
        rwa [(Finset.mem_filter.mp hj).2] at h
    let a : Tuple {i // i ∉ Q} :=
      Sum.elim (fun i => v (Sum.inl i.val)) (fun k => Classical.choose (hdiv k))
    have hspec : ∀ k : Fin 2, v (Sum.inr k) = sideProd σ (selPart Q v) k * a (Sum.inr k) :=
      fun k => Classical.choose_spec (hdiv k)
    have hcoll : collTuple Q σ (selPart Q v) a = v := by
      funext z
      cases z with
      | inl i =>
        by_cases hi : i ∈ Q
        · unfold collTuple
          rw [joinTuple_inl_mem Q _ _ i hi]
          rfl
        · unfold collTuple
          rw [joinTuple_inl_not_mem Q _ _ i hi]
          rfl
      | inr k => rw [collTuple_inr, ← hspec k]
    have hamem : a ∈ collBox s Q σ x := by
      apply Fintype.mem_piFinset.mpr
      apply (mem_pools_iff _ a).mpr
      refine ⟨fun i => hv'.1 i.val, ?_, ?_⟩
      · apply (mem_shortenPlains_plain₁ (s.restrict Q) _ _ _ _ _).mpr
        change sideProd σ (selPart Q v) 0 * a (Sum.inr 0) ∈ s.plain₁
        rw [← hspec 0]
        exact hv'.2.1
      · apply (mem_shortenPlains_plain₂ (s.restrict Q) _ _ _ _ _).mpr
        change sideProd σ (selPart Q v) 1 * a (Sum.inr 1) ∈ s.plain₂
        rw [← hspec 1]
        exact hv'.2.2
    refine ⟨⟨x, a⟩, Finset.mem_sigma.mpr ⟨Finset.mem_attach _ _, hamem⟩, ?_, hcoll⟩
    change CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
        (collTuple Q σ (selPart Q v) a) * patMask J Q σ (collTuple Q σ (selPart Q v) a) *
        Φ (collTuple Q σ (selPart Q v) a) ≠ 0
    rw [hcoll]
    exact hne
  · intro p _ _
    rfl

/-- The family coprimality of a nonzero family coefficient. -/
theorem profile_coprime {μ : Type*} [Fintype μ] (s : Input μ) (modifier : Tuple μ → ℂ)
    (R L : Ideal O) (w : Tuple μ)
    (hne : CoupledFirst.tupleCoefficient s modifier R L w ≠ 0) :
    IsCoprime (finiteTupleProduct w) R := by
  have hp := CoupledFirst.tuple_nonzero s modifier R L w hne
  by_contra hn
  apply hp
  simp only [profileCoefficient, hn, ↓reduceIte, mul_zero, zero_mul]

/-- The remaining selected block, read on the residual slots. -/
def restBlock (J Q : Finset κ) : Finset {i // i ∉ Q} := J.subtype (fun i => i ∉ Q)

theorem restBlock_prod (J Q : Finset κ) (f : κ → Ideal O) :
    ∏ j ∈ restBlock J Q, f j.val = ∏ j ∈ J \ Q, f j := by
  unfold restBlock
  rw [Finset.prod_subtype_eq_prod_filter, Finset.sdiff_eq_filter]

/-- **Factorization with the pattern mask.** -/
theorem coll_factor_mask (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (u : Q → Ideal O)
    (h₀ : sideProd σ u 0 ≠ 0) (h₁ : sideProd σ u 1 ≠ 0) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (a : Tuple {i // i ∉ Q}) (hL : IsCoprime L (selProduct Q u))
    (hF : F (Dc * (selProduct Q u ^ 2 * finiteTupleProduct a)) = F (Dc * finiteTupleProduct a)) :
    CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (collTuple Q σ u a) *
        patMask J Q σ (collTuple Q σ u a) =
      selWeight s Q K R u *
        noColPart (restBlock J Q)
          (CoupledFirst.tupleCoefficient (collInput s Q σ u h₀ h₁)
            (markedSourceModifier (A₁ * sideProd σ u 0) (A₂ * sideProd σ u 1) Dc K F)
            (R * selProduct Q u) L) a := by
  rw [coll_factor s Q σ u h₀ h₁ A₁ A₂ Dc K R L F a hL hF]
  unfold noColPart
  set tf := CoupledFirst.tupleCoefficient (collInput s Q σ u h₀ h₁)
    (markedSourceModifier (A₁ * sideProd σ u 0) (A₂ * sideProd σ u 1) Dc K F)
    (R * selProduct Q u) L a with htf
  by_cases hz : tf = 0
  · rw [hz]
    ring
  have hcopD : IsCoprime (finiteTupleProduct a) (selProduct Q u) :=
    (profile_coprime _ _ _ _ a hz).of_isCoprime_of_dvd_right (dvd_mul_left _ _)
  have hmD : IsCoprime (∏ j ∈ restBlock J Q, a (Sum.inl j)) (selProduct Q u) := by
    apply hcopD.of_isCoprime_of_dvd_left
    rw [finiteTupleProduct_split a]
    exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)).trans
      (dvd_mul_right _ _)
  have hmask : patMask J Q σ (collTuple Q σ u a) = noColMask (restBlock J Q) a := by
    unfold patMask noColMask
    have hfirst : ∀ j : Q, collTuple Q σ u a (Sum.inl j.val) ∣ collTuple Q σ u a (Sum.inr (σ j)) := by
      intro j
      unfold collTuple
      rw [joinTuple_inl_mem Q _ _ j.val j.property]
      change u ⟨j.val, j.property⟩ ∣ sideProd σ u (σ j) * a (Sum.inr (σ j))
      apply Dvd.dvd.mul_right
      exact Finset.dvd_prod_of_mem u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
    have hprod : ∏ j ∈ J \ Q, collTuple Q σ u a (Sum.inl j) =
        ∏ j ∈ restBlock J Q, a (Sum.inl j) := by
      rw [← restBlock_prod J Q (fun j => collTuple Q σ u a (Sum.inl j))]
      apply Finset.prod_congr rfl
      intro j _
      unfold collTuple
      rw [joinTuple_inl_not_mem Q _ _ j.val j.property]
      rfl
    have hplain : collTuple Q σ u a (Sum.inr 0) * collTuple Q σ u a (Sum.inr 1) =
        selProduct Q u * (a (Sum.inr 0) * a (Sum.inr 1)) := by
      rw [collTuple_inr, collTuple_inr, ← sideProd_mul σ u]
      ring
    rw [hprod, hplain]
    have hiff : IsCoprime (∏ j ∈ restBlock J Q, a (Sum.inl j))
        (selProduct Q u * (a (Sum.inr 0) * a (Sum.inr 1))) ↔
        IsCoprime (∏ j ∈ restBlock J Q, a (Sum.inl j)) (a (Sum.inr 0) * a (Sum.inr 1)) := by
      rw [IsCoprime.mul_right_iff]
      exact ⟨fun h => h.2, fun h => ⟨hmD, h⟩⟩
    simp only [hfirst, implies_true, true_and, hiff]
  rw [hmask]
  ring

end
end QRH.MixedStep.Collision

#print axioms QRH.MixedStep.Collision.colPart_patterns
#print axioms QRH.MixedStep.Collision.pattern_sum
#print axioms QRH.MixedStep.Collision.coll_factor_mask
