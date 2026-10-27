/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M2, item 2 (slots): reindexing the slots of a residual source.

`GData` fixes the slot type `Fin N`, while the selected residual (`Concrete.restSource`) lives on
`Rest J = {i // i ∉ J}`. For an equivalence `e : ι ≃ κ` of slot types:
* `tmap e`: tuples on `ι ⊕ Fin 2` ↦ tuples on `κ ⊕ Fin 2` (ordinary entries unchanged);
* `originalColumn_reindex`, `finiteColumns_reindex`: the literal column coefficients and the
  column set of the slot data transported along `e` are those of the original data;
* `reindexSource`: the FP source with transported slot data, with
  `sourceColumns_reindex`, `sourceCoefficient_reindex` (equal column sets and coefficients);
* `labelEnergy_reindex`: the literal label energy of transported canonical slot data is the
  original one. Hence Seam B for slot type `Fin N` applies to a residual on `Rest J` with
  `N = |Rest J|` (apply Seam B for each `N ≤ N_root`: a finite family of structural data). -/
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedFrame
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedPrincipalWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP QRH.SilDensitySplit.CubeFree.Packet.Reduce

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedTupleRows
open MixedHeightEnergy MixedCommonAllocation MixedPrincipalPair MixedPrincipalAllocations
open MixedPrincipalWindow
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _

section Tuples
variable {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)

/-- Transport of a tuple along a slot equivalence. -/
def tmap (v : Tuple ι) : Tuple κ := fun t => v (Sum.map e.symm id t)

/-- The inverse transport. -/
def tunmap (v : Tuple κ) : Tuple ι := fun t => v (Sum.map e id t)

theorem tunmap_tmap (v : Tuple ι) : tunmap e (tmap e v) = v := by
  funext t; rcases t with i | j <;> simp [tmap, tunmap]

theorem tmap_tunmap (v : Tuple κ) : tmap e (tunmap e v) = v := by
  funext t; rcases t with k | j <;> simp [tmap, tunmap]

@[simp] theorem tmap_inl (v : Tuple ι) (k : κ) : tmap e v (Sum.inl k) = v (Sum.inl (e.symm k)) :=
  rfl

@[simp] theorem tmap_inr (v : Tuple ι) (j : Fin 2) : tmap e v (Sum.inr j) = v (Sum.inr j) := rfl

theorem finiteTupleProduct_tmap (v : Tuple ι) : finiteTupleProduct (tmap e v) = finiteTupleProduct v := by
  unfold finiteTupleProduct
  exact (Fintype.prod_equiv (Equiv.sumCongr e (Equiv.refl (Fin 2))) (fun t => v t)
    (fun t => tmap e v t) (fun t => by rcases t with i | j <;> simp [tmap])).symm

theorem slotProduct_tmap (v : Tuple ι) : slotProduct (tmap e v) = slotProduct v := by
  unfold slotProduct
  exact (Fintype.prod_equiv e (fun i => v (Sum.inl i)) (fun k => tmap e v (Sum.inl k))
    (fun i => by simp [tmap])).symm

theorem tupleWeight_tmap (Hp : Id) (v : Tuple ι) : tupleWeight Hp (tmap e v) = tupleWeight Hp v := by
  have hinj : Function.Injective (fun k => tmap e v (Sum.inl k)) ↔
      Function.Injective (fun i => v (Sum.inl i)) := by
    have : (fun k => tmap e v (Sum.inl k)) = (fun i => v (Sum.inl i)) ∘ e.symm := by
      funext k; rfl
    rw [this]
    exact EquivLike.injective_comp e.symm _
  have hp : tupleRestriction Hp (tmap e v) ↔ tupleRestriction Hp v := by
    unfold tupleRestriction
    rw [slotProduct_tmap, tmap_inr, tmap_inr, hinj]
  unfold tupleWeight
  by_cases h : tupleRestriction Hp v
  · rw [if_pos h, if_pos (hp.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hp.mp h'))]

theorem profileCoefficient_tmap (R : Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Id) (v : Tuple ι) :
    profileCoefficient R (fun k => ν (e.symm k)) (fun k => Wslot (e.symm k)) (fun k => P (e.symm k))
        W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (tmap e v) =
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  unfold profileCoefficient
  rw [finiteTupleProduct_tmap, tmap_inr, tmap_inr]
  congr 3
  exact (Fintype.prod_equiv e
    (fun i => ν i (v (Sum.inl i)) * Wslot i ((Ideal.absNorm (v (Sum.inl i)) : ℝ) / P i))
    (fun k => ν (e.symm k) (tmap e v (Sum.inl k)) *
      Wslot (e.symm k) ((Ideal.absNorm (tmap e v (Sum.inl k)) : ℝ) / P (e.symm k)))
    (fun i => by simp [tmap])).symm

theorem mem_pools_tmap (pool : ι → Finset Id) (A B : Finset Id) (v : Tuple ι) :
    (∀ t, tmap e v t ∈ pools (fun k => pool (e.symm k)) A B t) ↔ (∀ t, v t ∈ pools pool A B t) := by
  constructor
  · intro h t
    rcases t with i | j
    · have := h (Sum.inl (e i))
      simpa [tmap, pools] using this
    · simpa [tmap, pools] using h (Sum.inr j)
  · intro h t
    rcases t with k | j
    · simpa [tmap, pools] using h (Sum.inl (e.symm k))
    · simpa [tmap, pools] using h (Sum.inr j)

theorem mem_pools_tunmap (pool : ι → Finset Id) (A B : Finset Id) (v : Tuple κ) :
    (∀ t, tunmap e v t ∈ pools pool A B t) ↔ (∀ t, v t ∈ pools (fun k => pool (e.symm k)) A B t) := by
  rw [← mem_pools_tmap e pool A B, tmap_tunmap]

theorem tmap_injective : Function.Injective (tmap (κ := κ) e) := by
  intro v w h
  rw [← tunmap_tmap e v, ← tunmap_tmap e w, h]

/-- **Reindexed column set.** -/
theorem finiteColumns_reindex (pool : ι → Finset Id) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (b X₁ X₂ Y₁ Y₂ : ℝ) :
    finiteColumns (Fintype.piFinset (sourcePools (fun k => pool (e.symm k)) d hd b X₁ X₂ Y₁ Y₂)) =
      finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂)) := by
  unfold finiteColumns sourcePools
  ext I
  simp only [Finset.mem_image, Fintype.mem_piFinset]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨tunmap e v, (mem_pools_tunmap e _ _ _ v).mpr hv, by
      rw [← finiteTupleProduct_tmap e, tmap_tunmap]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨tmap e v, (mem_pools_tmap e _ _ _ v).mpr hv, finiteTupleProduct_tmap e v⟩

/-- **Reindexed column coefficient.** -/
theorem originalColumn_reindex (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (d : Id × Id)
    (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (R seed : Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    originalColumn S H (fun k => pool (e.symm k)) d hd R seed (fun k => ν (e.symm k))
        (fun k => Wslot (e.symm k)) (fun k => P (e.symm k)) W₁ W₂ b X₁ X₂ Y₁ Y₂ =
      originalColumn S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  funext I
  unfold originalColumn finiteColumnCoefficient sourcePools
  apply Finset.sum_nbij' (tunmap e) (tmap e)
  · intro v hv
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hv ⊢
    exact ⟨(mem_pools_tunmap e _ _ _ v).mpr hv.1, by
      rw [← finiteTupleProduct_tmap e, tmap_tunmap]; exact hv.2⟩
  · intro v hv
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hv ⊢
    exact ⟨(mem_pools_tmap e _ _ _ v).mpr hv.1, by rw [finiteTupleProduct_tmap]; exact hv.2⟩
  · intro v _
    exact tmap_tunmap e v
  · intro v _
    exact tunmap_tmap e v
  · intro v _
    have h1 := tupleWeight_tmap e (punctureProduct S H) (tunmap e v)
    have h2 := profileCoefficient_tmap e R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed (tunmap e v)
    rw [tmap_tunmap] at h1 h2
    rw [h1, h2]

end Tuples

/-! ### Reindexing an FP source -/

section Source
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {a b : ℝ}

/-- The FP source with slots transported along `e`. -/
def reindexSource (s : Source ι a b) (e : ι ≃ κ) : Source κ a b where
  S := s.S
  H := s.H
  pool := fun k => s.pool (e.symm k)
  d := s.d
  hd := s.hd
  B := tmap e s.B
  hB := fun t => s.hB _
  G := s.G
  R := s.R
  Fhole := s.Fhole
  hprod := by rw [finiteTupleProduct_tmap]; exact s.hprod
  hR := s.hR
  hFhole := s.hFhole
  ν := fun k => s.ν (e.symm k)
  Wslot := fun k => s.Wslot (e.symm k)
  P := fun k => s.P (e.symm k)
  M := fun k => s.M (e.symm k)
  W₁ := s.W₁
  W₂ := s.W₂
  hs₁ := s.hs₁
  hs₂ := s.hs₂
  t₁ := s.t₁
  t₂ := s.t₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  U₁ := s.U₁
  U₂ := s.U₂
  T := s.T
  L := s.L
  hL := s.hL
  hX₁ := s.hX₁
  hX₂ := s.hX₂
  hY₁ := s.hY₁
  hY₂ := s.hY₂
  hXU₁ := s.hXU₁
  hXU₂ := s.hXU₂
  hYU₁ := s.hYU₁
  hYU₂ := s.hYU₂
  hpX := s.hpX
  hpY := s.hpY
  hP := fun k => s.hP _
  hM := fun k => s.hM _
  hpool := fun k => s.hpool _
  hp := fun k => s.hp _
  hpn := fun k => s.hpn _
  hν := fun k => s.hν _
  hWnorm := fun k => s.hWnorm _
  hW := fun k => s.hW _
  hS := s.hS
  hH := s.hH
  henclose := s.henclose

theorem sourceColumns_reindex (s : Source ι a b) (e : ι ≃ κ) :
    sourceColumns (reindexSource s e) = sourceColumns s :=
  finiteColumns_reindex e s.pool s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂

theorem sourceCoefficient_reindex (s : Source ι a b) (e : ι ≃ κ) (ha : 0 < a) (seed : Id) :
    sourceCoefficient (reindexSource s e) ha seed = sourceCoefficient s ha seed :=
  originalColumn_reindex e s.S s.H s.pool s.d s.hd s.R seed s.ν s.Wslot s.P _ _ b
    s.X₁ s.X₂ s.Y₁ s.Y₂

end Source

/-! ### The literal label energy under reindexing -/

/-- **The label energy only depends on the slot data up to reindexing.** -/
theorem labelEnergy_reindex (M : Ideal O) [NeZero M] (Hray : Subgroup (O ⧸ M)ˣ)
    (hHray : RayOrthogonality.globalUnits M ≤ Hray) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (W : ℝ → ℂ) (η₀ : Character) (θ : ι → RayQuotient.Characters M Hray) (Z : ℝ)
    (w σ freq : ι → ℝ) (t : ℝ) (R₀ : ι → Finset Id) (τ : Character) (Q : Id) (n : Fin 4 → ℤ)
    (Cap Lcap : ℝ) (R G : Id) (hG : G ≠ 0) (seed D : Id) (H : Finset PrimeIdeal)
    (W₁ W₂ : ℝ → ℂ) (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (v : ℝ) :
    labelEnergy M Hray hHray W η₀ (fun k => θ (e.symm k)) Z (fun k => w (e.symm k))
        (fun k => σ (e.symm k)) (fun k => freq (e.symm k)) t (fun k => R₀ (e.symm k)) τ Q n Cap
        Lcap R G hG seed D H W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v =
      labelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀ τ Q n Cap Lcap R G hG seed D H
        W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v := by
  unfold labelEnergy
  have hcols := finiteColumns_reindex e
    (fun i => NativeInjectiveEnergy.supportedPool
      (CenteredMomentPrimeSlot.primePool M Hray 2 (Z^(w i)))) d hd b X₁ X₂ Y₁ Y₂
  have hcoef := originalColumn_reindex e (ReferencePrimeEnclosure.enclosure (Cap*Z^Lcap)) H
    (fun i => NativeInjectiveEnergy.supportedPool
      (CenteredMomentPrimeSlot.primePool M Hray 2 (Z^(w i)))) d hd R seed
    (MixedCanonicalSource.slotCoefficient
      (fun i => CenteredMomentNaturalFixedRaySource.relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
    (fun i => MixedCanonicalSource.slotProfile W (σ i) (freq i)) (fun i => Z^(w i))
    (ReferencePrimeEnclosure.phaseProfile W₁ t₁) (ReferencePrimeEnclosure.phaseProfile W₂ t₂)
    b X₁ X₂ Y₁ Y₂
  have hslot : (fun k => MixedCanonicalSource.slotCoefficient
      (fun i => CenteredMomentNaturalFixedRaySource.relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
      (e.symm k)) =
      MixedCanonicalSource.slotCoefficient
        (fun k => CenteredMomentNaturalFixedRaySource.relativeCharacter M Hray hHray η₀
          (θ (e.symm k))) (fun k => R₀ (e.symm k)) t := by
    funext k I
    rfl
  rw [hslot] at hcoef
  congr 1
  · exact hcols ▸ rfl
  · funext I
    rw [hcoef]

/-! ### The frame source of a canonical FP source -/

section Canonical
open QRH.SilDensitySplit.CubeFree.Packet.Grouped
open CenteredMomentRestrictedSource CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentNaturalFixedRaySource

/-- `normPowerProfile W t = phaseProfile W (t/2π)`. -/
theorem normPowerProfile_eq_phase (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ (W : ℝ → ℂ)) (t : ℝ) :
    ((CenteredMomentLattice.normPowerProfile W a b ha hs hW t : 𝓢(ℝ,ℂ)) : ℝ → ℂ) =
      ReferencePrimeEnclosure.phaseProfile W (t / (2 * Real.pi)) := by
  funext x
  rw [CenteredMomentLattice.normPowerProfile_apply]
  unfold ReferencePrimeEnclosure.phaseProfile
  by_cases hx : (W : ℝ → ℂ) x = 0
  · rw [hx, mul_zero, zero_mul]
  · rw [CenteredMomentLattice.logPhase_eq_normPower t x (lt_of_lt_of_le ha (hs hx).1)]
    ring

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- **The frame source of a canonical FP source on `Fin N`**: its slot data, profiles
(`t_i ↦ t_i/2π`), lengths, packed first twist `V₀` and Gauss log-scale. -/
def srcOf (s : Source (Fin θ.N) θ.a θ.b) (hZ : 1 < Z)
    (χ : Fin θ.N → RayQuotient.Characters θ.rayM θ.Hray) (w σ freq : Fin θ.N → ℝ) (t Vf : ℝ)
    (R₀ : Fin θ.N → Finset Id) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hσ : ∀ i, σ i = 33/50) (hVf : 0 ≤ Vf) (hfreq : ∀ i, |freq i| ≤ Vf)
    (hR₀ : ∀ i, (R₀ i).card ≤ θ.Holes)
    (hX₁L : s.X₁ ≤ Z^L) (hX₂L : s.X₂ ≤ Z^L) (hY₁L : s.Y₁ ≤ Z^L) (hY₂L : s.Y₂ ≤ Z^L)
    (V₀ : O) (hV₀ : V₀ ≠ 0) (kLog : ℝ) : GSrc θ mesh Z where
  hZ := hZ
  χ := χ
  w := w
  σ := σ
  freq := freq
  t := t
  Vf := Vf
  R₀ := R₀
  hw := hw
  hwm := hwm
  hσ := hσ
  hVf := hVf
  hfreq := hfreq
  hR₀ := hR₀
  W₁ := s.W₁
  W₂ := s.W₂
  hs₁ := s.hs₁
  hs₂ := s.hs₂
  t₁ := s.t₁ / (2 * Real.pi)
  t₂ := s.t₂ / (2 * Real.pi)
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  hX₁ := s.hL.trans_le s.hX₁
  hX₂ := s.hL.trans_le s.hX₂
  hY₁ := s.hL.trans_le s.hY₁
  hY₂ := s.hL.trans_le s.hY₂
  hX₁L := hX₁L
  hX₂L := hX₂L
  hY₁L := hY₁L
  hY₂L := hY₂L
  hXY := s.hpX.trans s.hpY.symm
  V₀ := V₀
  hV₀ := hV₀
  kLog := kLog

/-- The canonical form of an FP source relative to frame slot data and label data. -/
structure Canonical (s : Source (Fin θ.N) θ.a θ.b) (Z : ℝ)
    (χ : Fin θ.N → RayQuotient.Characters θ.rayM θ.Hray) (w σ freq : Fin θ.N → ℝ) (t : ℝ)
    (R₀ : Fin θ.N → Finset Id) (H : Finset PrimeIdeal) (R : Id) (d : Id × Id) : Prop where
  S : s.S = ReferencePrimeEnclosure.enclosure (θ.Cap * Z^θ.Lcap)
  H : s.H = H
  pool : ∀ i, s.pool i =
    NativeInjectiveEnergy.supportedPool (CenteredMomentPrimeSlot.primePool θ.rayM θ.Hray 2 (Z^(w i)))
  ν : ∀ i, s.ν i = MixedCanonicalSource.slotCoefficient
    (fun i => CenteredMomentNaturalFixedRaySource.relativeCharacter θ.rayM θ.Hray θ.hH θ.η₀ (χ i))
    R₀ t i
  Wslot : ∀ i, s.Wslot i = MixedCanonicalSource.slotProfile θ.W (σ i) (freq i)
  P : ∀ i, s.P i = Z^(w i)
  R : s.R = R
  d : s.d = d

/-- **The frame energy of a label on the frame source of a canonical FP source is the literal
second-step energy of that FP source**: the restricted energy over its residual columns
`I` (`G·I` a column, `(G, I) = 1`, `t₂ ∣ I`) of its literal column coefficient with seed. -/
theorem rawEnergy_srcOf (η : Character) (s : Source (Fin θ.N) θ.a θ.b) (hZ : 1 < Z)
    (χ : Fin θ.N → RayQuotient.Characters θ.rayM θ.Hray) (w σ freq : Fin θ.N → ℝ) (t Vf : ℝ)
    (R₀ : Fin θ.N → Finset Id) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hσ : ∀ i, σ i = 33/50) (hVf : 0 ≤ Vf) (hfreq : ∀ i, |freq i| ≤ Vf)
    (hR₀ : ∀ i, (R₀ i).card ≤ θ.Holes)
    (hX₁L : s.X₁ ≤ Z^L) (hX₂L : s.X₂ ≤ Z^L) (hY₁L : s.Y₁ ≤ Z^L) (hY₂L : s.Y₂ ≤ Z^L)
    (V₀ : O) (hV₀ : V₀ ≠ 0) (kLog : ℝ) (x : GLabel θ mesh Z)
    (h : Fits η (srcOf s hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀ hX₁L hX₂L hY₁L hY₂L V₀ hV₀
      kLog) x)
    (hcan : Canonical s Z χ w σ freq t R₀ x.holesH x.R x.d) (v : ℝ) :
    rawEnergy η (srcOf s hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀ hX₁L hX₂L hY₁L hY₂L V₀ hV₀
        kLog) x h v =
      sourceRestrictedEnergy
        (canonicalRadial (x.char (srcOf s hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀ hX₁L hX₂L
          hY₁L hY₂L V₀ hV₀ kLog)) (internalQ θ.Q θ.η₀) x.n).keep
        (residualPool x.G h.G_ne (sourceColumns s))
        (fun I => if IsCoprime x.G I ∧ x.D ∣ I then sourceCoefficient s θ.ha0 x.seed (x.G * I)
          else 0)
        (heightCoeff (x.char (srcOf s hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀ hX₁L hX₂L
          hY₁L hY₂L V₀ hV₀ kLog)) v) ballProfile (dyadicScale (x.n 1)) := by
  obtain ⟨hS, hH, hpool, hν, hWs, hP, hR, hd⟩ := hcan
  have hpool' := funext hpool
  have hν' := funext hν
  have hWs' := funext hWs
  have hP' := funext hP
  unfold rawEnergy labelEnergy sourceColumns sourceCoefficient tuplePools
  rw [normPowerProfile_eq_phase, normPowerProfile_eq_phase]
  cases s
  simp only at hS hH hpool' hν' hWs' hP' hR hd ⊢
  subst hS hH hpool' hν' hWs' hP' hR hd
  rfl

end Canonical

end
end QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
