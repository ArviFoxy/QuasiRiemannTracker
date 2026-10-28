/- Copyright (c) 2026 Sil. Apache-2.0.
Bridge from cube-free columns to the fifth-power hypotheses of FP's Gauss transfer.

Cube-free columns are in particular fifth-power free, so FP `GaussTransfer` (the
fourth-power identity `χ_n(D)² g(n,k) = g(n,k D⁴)` with all nonunit cases) and every
FP lemma assuming `SexticSieve.PowerFree 5`/`6` is imported unchanged.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.GaussTransfer
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SexticSieve

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.FifthFreeBridge
open OAI OAI.SevenEighths
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- Literal cube-freeness of an element. -/
def ElementCubeFree (a : O) : Prop := ∀ p : O, Prime p → ¬p^3 ∣ a

theorem cubeFree_fifthFree_element {a : O} (h : ElementCubeFree a) :
    Candidate.FourthPower.GaussTransfer.FifthFree a :=
  fun p hp hd => h p hp ((pow_dvd_pow p (by norm_num : 3 ≤ 5)).trans hd)

/-- Ideal form: `PowerFree 3 ⇒ PowerFree n` for every `n ≥ 3` (in particular 5 and 6). -/
theorem powerFree_three_le {n : ℕ} (hn : 3 ≤ n) {I : Id}
    (h : Candidate.FourthPower.SexticSieve.PowerFree 3 I) :
    Candidate.FourthPower.SexticSieve.PowerFree n I :=
  Candidate.FourthPower.SexticSieve.powerFree_mono hn h

theorem powerFree_three_five {I : Id} (h : Candidate.FourthPower.SexticSieve.PowerFree 3 I) :
    Candidate.FourthPower.SexticSieve.PowerFree 5 I :=
  powerFree_three_le (by norm_num) h

/-- The design's bridge `cubeFree_fifthFree`: a cube-free principal ideal has a fifth-power
free generator, which is the hypothesis of `GaussTransfer.normalized_fourth_power`. -/
theorem cubeFree_fifthFree (a : O)
    (h : Candidate.FourthPower.SexticSieve.PowerFree 3 (Ideal.span {a})) :
    Candidate.FourthPower.GaussTransfer.FifthFree a := by
  intro p hp hd
  have hprime : Prime (Ideal.span {p} : Id) :=
    Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
      ((Ideal.span_singleton_prime hp.ne_zero).mpr hp)
  apply h (Ideal.span {p}) hprime
  obtain ⟨q, hq⟩ := (pow_dvd_pow p (by norm_num : 3 ≤ 5)).trans hd
  refine ⟨Ideal.span {q}, ?_⟩
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton, hq]

theorem cubeFree_of_powerFree (a : O)
    (h : Candidate.FourthPower.SexticSieve.PowerFree 3 (Ideal.span {a})) : ElementCubeFree a := by
  intro p hp hd
  have hprime : Prime (Ideal.span {p} : Id) :=
    Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
      ((Ideal.span_singleton_prime hp.ne_zero).mpr hp)
  apply h (Ideal.span {p}) hprime
  obtain ⟨q, hq⟩ := hd
  refine ⟨Ideal.span {q}, ?_⟩
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton, hq]

end QRH.DensitySplitThird.CubeFree.FifthFreeBridge
