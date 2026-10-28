/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M (a), part 3: the selected expansion of a live source's Gauss polynomial.

`seedRest u D = ∏_{P ∣ u, D ⊄ P} P` is the part of the squarefree artificial divisor `u` not
dividing `D`; `u ∣ D n ↔ seedRest u D ∣ n` (`dvd_mul_iff_seedRest`). Hence (`selected_expansion`)
  `∑_I c_u(I) h_τ(I) g(I; k) = ∑_y sel(y) · ∑_{I ∈ rest} c^{rest}_{seedRest u D_y}(I)
      [(D_y, I) = 1] h_τ(I) g(D_y I; k)`,
with the residual coefficient that of `restSource` with seed `seedRest u D_y`, depending on the
selected assignment only through `D_y`. -/
import Submissions.density_split_fourth.CubeFree.Second.ConcreteResidual2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSourceEnergy CenteredMomentLiveDomain
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiteralAllocation
open MixedCommonRestriction MixedCommonCoefficient MixedCommonAllocation MixedOriginalSecondZero
open MixedTupleRows MixedFirstLiveSource MixedRestrictedDictionary
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-! ### The seed outside a selected product -/

def seedRest (u D : Id) : Id :=
  ∏ P ∈ (IdealMobiusDivisorSum.primeSupport u).filter (fun P => ¬ D ≤ P), P

theorem seedRest_subset (u D : Id) :
    (IdealMobiusDivisorSum.primeSupport u).filter (fun P => ¬ D ≤ P) ⊆
      IdealMobiusDivisorSum.primeSupport u := Finset.filter_subset _ _

theorem seedRest_squarefree (u D : Id) : Squarefree (seedRest u D) :=
  IdealMobiusDivisorSum.squarefree_support_product (seedRest_subset u D)

theorem seedRest_support (u D : Id) :
    IdealMobiusDivisorSum.primeSupport (seedRest u D) =
      (IdealMobiusDivisorSum.primeSupport u).filter (fun P => ¬ D ≤ P) := by
  have h := IdealMobiusDivisorSum.factors_support_product (seedRest_subset u D)
  change (UniqueFactorizationMonoid.normalizedFactors (seedRest u D)).toFinset = _
  rw [seedRest, h, Finset.val_toFinset]

theorem mem_support_iff {X P : Id} (hX : X ≠ 0) :
    P ∈ IdealMobiusDivisorSum.primeSupport X ↔ P.IsPrime ∧ X ≤ P :=
  FirstDivisor.mem_primeSupport_iff hX

theorem dvd_iff_support {u X : Id} (hu : Squarefree u) (hX : X ≠ 0) :
    u ∣ X ↔ IdealMobiusDivisorSum.primeSupport u ⊆ IdealMobiusDivisorSum.primeSupport X :=
  FirstDivisor.squarefree_dvd_iff_support hu hX

/-- `u ∣ D n ↔ seedRest u D ∣ n` for squarefree `u`. -/
theorem dvd_mul_iff_seedRest {u D n : Id} (hu : Squarefree u) (hD : D ≠ 0) (hn : n ≠ 0) :
    u ∣ D * n ↔ seedRest u D ∣ n := by
  rw [dvd_iff_support hu (mul_ne_zero hD hn), dvd_iff_support (seedRest_squarefree u D) hn,
    seedRest_support]
  constructor
  · intro h P hP
    obtain ⟨hPu, hDP⟩ := Finset.mem_filter.mp hP
    have h1 := (mem_support_iff (mul_ne_zero hD hn)).mp (h hPu)
    rw [mem_support_iff hn]
    exact ⟨h1.1, ((h1.1.mul_le).mp h1.2).resolve_left hDP⟩
  · intro h P hP
    have hu0 : u ≠ 0 := hu.ne_zero
    have hPp := ((mem_support_iff hu0).mp hP).1
    rw [mem_support_iff (mul_ne_zero hD hn)]
    by_cases hDP : D ≤ P
    · exact ⟨hPp, Ideal.mul_le_left.trans hDP⟩
    · have hn' := (mem_support_iff hn).mp (h (Finset.mem_filter.mpr ⟨hP, hDP⟩))
      exact ⟨hPp, Ideal.mul_le_right.trans hn'.2⟩

/-! ### The selected expansion -/

/-- The selected scalar of an assignment. -/
def selScalar (s : Source ι a b) (J : Finset ι) (y : J → Id) (τ : Character) (t : ℝ) : ℂ :=
  (if Function.Injective y then 1 else 0) * selAmp s J y *
    (if IsCoprime (∏ j, y j) s.R then 1 else 0) * heightCoeff τ t (∏ j, y j)

theorem tuple_slot_prime (s : Source ι a b) (v : Tuple ι)
    (hv : v ∈ Fintype.piFinset (tuplePools s)) (i : ι) : Prime (v (Sum.inl i)) :=
  s.hp i _ ((Fintype.mem_piFinset.mp hv) (Sum.inl i))

theorem finiteTupleProduct_ne_zero_of_mem (s : Source ι a b) (v : Tuple ι)
    (hv : v ∈ Fintype.piFinset (tuplePools s)) : finiteTupleProduct v ≠ 0 := by
  unfold finiteTupleProduct
  rw [Finset.prod_ne_zero_iff]
  intro k _
  exact source_pools_nonzero s.pool s.hp s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂ k (v k)
    ((Fintype.mem_piFinset.mp hv) k)

theorem selected_expansion (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (ha : 0 < a)
    (u : Id) (hu : Squarefree u) (τ : Character) (t : ℝ) (k : O) :
    gaussPolynomial Finset.univ (sourceGenerator (sourceColumns s))
      (sourceGenerator_supported (sourceColumns s))
      (fun I : supportedColumns (sourceColumns s) => sourceCoefficient s ha u I * heightCoeff τ t I) k =
    ∑ y ∈ Fintype.piFinset (fun j : J => s.pool j.val), selScalar s J y τ t *
      ∑ I ∈ sourceColumns (restSource s hB1 J),
        sourceCoefficient (restSource s hB1 J) ha (seedRest u (∏ j, y j)) I *
          ((if IsCoprime (∏ j, y j) I then 1 else 0) * heightCoeff τ t I *
            primaryGaussRow ((∏ j, y j) * I) k) := by
  rw [source_gauss_tuples s ha u τ t k, sum_tuples_split s hB1 J]
  apply Finset.sum_congr rfl
  intro y hy
  have hyp : ∀ j, Prime (y j) := fun j => s.hp j.val _ ((Fintype.mem_piFinset.mp hy) j)
  have hD : (∏ j, y j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (hyp j).ne_zero)
  -- the residual columns
  have hcol := finite_column_sum (Fintype.piFinset (tuplePools (restSource s hB1 J)))
    (originalTuple (restSource s hB1 J) ha (seedRest u (∏ j, y j)))
    (fun I => (if IsCoprime (∏ j, y j) I then 1 else 0) * heightCoeff τ t I *
      primaryGaussRow ((∏ j, y j) * I) k)
  change _ = selScalar s J y τ t * ∑ I ∈ finiteColumns (Fintype.piFinset (tuplePools
    (restSource s hB1 J))), finiteColumnCoefficient (Fintype.piFinset (tuplePools
      (restSource s hB1 J))) (originalTuple (restSource s hB1 J) ha (seedRest u (∏ j, y j))) I * _
  rw [hcol, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrp : ∀ k', Prime (r (Sum.inl k')) := fun k' =>
    s.hp k'.val _ ((Fintype.mem_piFinset.mp hr) (Sum.inl k'))
  have hn : finiteTupleProduct r ≠ 0 :=
    finiteTupleProduct_ne_zero_of_mem (restSource s hB1 J) r hr
  rw [originalTuple_join s hB1 J ha u y r hyp hrp, finiteTupleProduct_join, heightCoeff_mul,
    dvd_mul_iff_seedRest hu hD hn]
  have hseed := profile_seed_mask (punctureProduct s.S s.H) s.R (seedRest u (∏ j, y j))
    (fun j : Rest J => s.ν j.val) (fun j => s.Wslot j.val) (fun j => s.P j.val)
    (CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d r
  change _ = _ * ((tupleWeight (punctureProduct s.S s.H) r * profileCoefficient s.R
    (fun j : Rest J => s.ν j.val) (fun j => s.Wslot j.val) (fun j => s.P j.val)
    (CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 (seedRest u (∏ j, y j)) r) * _)
  rw [← hseed]
  change ((if Function.Injective y then 1 else 0) * selAmp s J y *
      (if IsCoprime (∏ j, y j) s.R then 1 else 0) *
    ((if IsCoprime (∏ j, y j) (finiteTupleProduct r) then 1 else 0) *
      (if seedRest u (∏ j, y j) ∣ finiteTupleProduct r then 1 else 0)) *
    (tupleWeight (punctureProduct s.S s.H) r * profileCoefficient s.R
    (fun j : Rest J => s.ν j.val) (fun j => s.Wslot j.val) (fun j => s.P j.val)
    (CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 1 r)) *
      (heightCoeff τ t (∏ j, y j) * heightCoeff τ t (finiteTupleProduct r) *
        primaryGaussRow ((∏ j, y j) * finiteTupleProduct r) k) = _
  unfold selScalar
  by_cases hs : seedRest u (∏ j, y j) ∣ finiteTupleProduct r
  · simp only [hs, ite_true]; ring
  · simp only [hs, ite_false]; ring

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
