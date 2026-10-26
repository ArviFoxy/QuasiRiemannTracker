/- Mixed step (L4/L5, F5): new in this submission. A first-layer column keeps its label, its common
ideal and its rays when its residual divisor is replaced by a divisor of it. The residual seeds of
the transfer without (S) are such divisors; the cardinality of a family whose labels are injective in
`(first label, seed)` is read on these columns. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.ActiveColumns
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.MixedStep.SeedColumn
noncomputable section
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61InitialMass
open scoped Classical
local notation "O" => HeckeFamily.O

/-- The residual divisors of a first block are closed under divisors. -/
theorem divisors_dvd {s : FirstBlockSource} {L L' : Ideal O} (hL : L ∈ s.divisors) (h : L' ∣ L) :
    L' ∈ s.divisors := by
  unfold FirstBlockSource.divisors CenteredMomentMobiusRegroup.divisorPool at hL ⊢
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hL
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
  have hne : Ideal.span {CenteredMomentFirstPhysicalSource.element s.C s.D s.hD.1 s.pool i} ≠ ⊥ := by
    rw [CenteredMomentFirstPhysicalSource.element_span]
    exact (CenteredMomentFirstPhysicalSource.column_supported s.C s.D s.hD.1 s.pool i).1
  rw [IdealMobiusDivisorSum.mem_idealDivisors hne] at hi ⊢
  exact h.trans hi

/-- The column with the label and the rays of `j` and the divisor `L'` of its residual divisor. -/
def seedColumn {Label : Type*} {s : Label → FirstBlockSource} (j : FirstColumnIndex s) (L' : Ideal O)
    (h : L' ∣ j.2.1.val) : FirstColumnIndex s :=
  ⟨j.1, ⟨L', divisors_dvd j.2.1.property h⟩, j.2.2.1, j.2.2.2⟩

theorem seedColumn_label {Label : Type*} {s : Label → FirstBlockSource} (j : FirstColumnIndex s)
    (L' : Ideal O) (h : L' ∣ j.2.1.val) : (seedColumn j L' h).1 = j.1 := rfl

theorem seedColumn_seed {Label : Type*} {s : Label → FirstBlockSource} (j : FirstColumnIndex s)
    (L' : Ideal O) (h : L' ∣ j.2.1.val) : (seedColumn j L' h).2.1.val = L' := rfl

/-- A live column stays live when its residual divisor is replaced by a squarefree divisor. -/
theorem seedColumn_live {Label : Type*} [Fintype Label] {s : Label → FirstBlockSource}
    {V : Fin 4 → ℝ → ℂ} {j : FirstColumnIndex s} (hj : j ∈ firstLiveColumns s V) {L' : Ideal O}
    (h : L' ∣ j.2.1.val) (hsf : Squarefree L') : seedColumn j L' h ∈ firstLiveColumns s V := by
  obtain ⟨z, hz⟩ := (Finset.mem_filter.mp hj).2
  obtain ⟨hzr, hz0, hz1, _⟩ := (Finset.mem_filter.mp hz)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, Finset.mem_filter.mpr ⟨hzr, hz0, hz1, hsf⟩⟩

end
end QRH.MixedStep.SeedColumn
#print axioms QRH.MixedStep.SeedColumn.divisors_dvd
#print axioms QRH.MixedStep.SeedColumn.seedColumn_live
