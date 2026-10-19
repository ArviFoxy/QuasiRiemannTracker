/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.FiniteGain

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Sil.Uneven.Bootstrap

def pairSlope (u v : ℝ) : ℝ := u*v/(u+v)
def pairConst (u v c e : ℝ) : ℝ := (v*c+u*e)/(u+v)
def pairWidth (u v w z : ℝ) : ℝ := (v*w+u*z)/(u+v)
def mixedFace (u v c e w z d t S : ℝ) : ℝ :=
  1-d*pairSlope u v*t-d*pairConst u v c e-d*pairWidth u v w z*S

/-- Eliminate the two witness lengths by their positive convex combination. -/
theorem mixed_face {u v c e w z d t S r m E : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hd : 0 ≤ d) (hlen : t ≤ r+m)
    (hI : E ≤ 1-d*u*r-d*c-d*w*S)
    (hP : E ≤ 1-d*v*m-d*e-d*z*S) :
    E ≤ mixedFace u v c e w z d t S := by
  have hsum : 0 < u+v := add_pos hu hv
  have h₁ := mul_le_mul_of_nonneg_left hI hv.le
  have h₂ := mul_le_mul_of_nonneg_left hP hu.le
  have h₃ := mul_le_mul_of_nonneg_left hlen (mul_nonneg (mul_nonneg hd hu.le) hv.le)
  have he : (u+v)*mixedFace u v c e w z d t S=
      (u+v)-d*u*v*t-d*(v*c+u*e)-d*(v*w+u*z)*S := by
    unfold mixedFace pairSlope pairConst pairWidth
    field_simp
    <;> ring
  apply (mul_le_mul_iff_of_pos_left hsum).mp
  rw [he]
  nlinarith only [h₁,h₂,h₃]

def crossing (a d k c w S : ℝ) : ℝ :=
  (a+d*k/6-a*d*c-a*d*w*S)/(a+d*k)

/-- A bound on the crossing controls the whole decreasing affine face. -/
theorem face_at_cutoff {a d k c w S R : ℝ}
    (ha : 0 < a) (hd : 0 ≤ d) (hk : 0 ≤ k)
    (hcross : crossing a d k c w S ≤ R) :
    1-d*k*((R-1/6)/a)-d*c-d*w*S ≤ R := by
  have hden : 0 < a+d*k := add_pos_of_pos_of_nonneg ha (mul_nonneg hd hk)
  have hn := (div_le_iff₀ hden).mp hcross
  have ht : a*((R-1/6)/a)=R-1/6 := mul_div_cancel₀ _ ha.ne'
  have htd := congrArg (fun x : ℝ => d*k*x) ht
  have hscaled : 0 ≤ a*(R-(1-d*k*((R-1/6)/a)-d*c-d*w*S)) := by
    nlinarith only [hn,htd]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp hscaled)

/-- The auxiliary plain moment has three possible active width constraints. -/
theorem auxiliary_plain_faces {d m S B lam upper E : ℝ}
    (hd : 0 ≤ d)
    (hE : E ≤ 1-2*d*m-d*min S (min upper ((B-2*m)/lam))) :
    E ≤ max (1-2*d*m-d*S)
      (max (1-2*d*m-d*upper) (1-2*d*m-d*((B-2*m)/lam))) := by
  rcases le_total S (min upper ((B-2*m)/lam)) with h|h
  · rw [min_eq_left h] at hE
    exact hE.trans (le_max_left _ _)
  · rw [min_eq_right h] at hE
    rcases le_total upper ((B-2*m)/lam) with h'|h'
    · rw [min_eq_left h'] at hE
      exact hE.trans ((le_max_left _ _).trans (le_max_right _ _))
    · rw [min_eq_right h'] at hE
      exact hE.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The old capped moment controls the omitted long-length region. -/
theorem old_plain_tail {d m mcut S E : ℝ} (hd : 0 ≤ d)
    (hm : mcut ≤ m) (hS : 2*(1-2*mcut)/9 ≤ S)
    (hE : E ≤ 1-2*d*m-d*min S (2*(1-2*m)/9)) :
    E ≤ 1-2*d/9-14*d*mcut/9 := by
  rw [min_eq_right (by linarith)] at hE
  have hdm := mul_le_mul_of_nonneg_left hm hd
  nlinarith only [hE,hdm]

/-- Six inverse/plain pairs and the old-moment tail exhaust all alternatives. -/
theorem seven_face_count {u c w : Fin 2 → ℝ} {v e z : Fin 3 → ℝ}
    {d t S r m E tail R : ℝ}
    (hu : ∀i,0 < u i) (hv : ∀j,0 < v j) (hd : 0 ≤ d) (hlen : t ≤ r+m)
    (hI : E ≤ max (1-d*u 0*r-d*c 0-d*w 0*S) (1-d*u 1*r-d*c 1-d*w 1*S))
    (hP : E ≤ max
      (max (1-d*v 0*m-d*e 0-d*z 0*S) (1-d*v 1*m-d*e 1-d*z 1*S))
      (max (1-d*v 2*m-d*e 2-d*z 2*S) tail))
    (hpairs : ∀i j,mixedFace (u i) (v j) (c i) (e j) (w i) (z j) d t S ≤ R)
    (htail : tail ≤ R) : E ≤ R := by
  have hpair (i : Fin 2) (j : Fin 3)
      (hi : E ≤ 1-d*u i*r-d*c i-d*w i*S)
      (hp : E ≤ 1-d*v j*m-d*e j-d*z j*S) : E ≤ R :=
    (mixed_face (hu i) (hv j) hd hlen hi hp).trans (hpairs i j)
  rcases le_max_iff.mp hP with hp|hp
  · rcases le_max_iff.mp hp with hp|hp
    · rcases le_max_iff.mp hI with hi|hi
      · exact hpair 0 0 hi hp
      · exact hpair 1 0 hi hp
    · rcases le_max_iff.mp hI with hi|hi
      · exact hpair 0 1 hi hp
      · exact hpair 1 1 hi hp
  · rcases le_max_iff.mp hp with hp|hp
    · rcases le_max_iff.mp hI with hi|hi
      · exact hpair 0 2 hi hp
      · exact hpair 1 2 hi hp
    · exact hp.trans htail

end Sil.Uneven.Bootstrap
#print axioms Sil.Uneven.Bootstrap.mixed_face
#print axioms Sil.Uneven.Bootstrap.face_at_cutoff
#print axioms Sil.Uneven.Bootstrap.old_plain_tail
#print axioms Sil.Uneven.Bootstrap.seven_face_count
