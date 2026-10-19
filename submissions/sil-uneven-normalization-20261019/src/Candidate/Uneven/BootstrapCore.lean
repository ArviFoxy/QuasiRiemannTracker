/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
    The seven-case scalar argument; the auxiliary analytic moment remains a separate input. -/
import Candidate.Uneven.BootstrapPairs
import Candidate.Uneven.BootstrapCoefficients

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.Bootstrap

def auxB : ℝ := 1988153/2000000
def auxLambda : ℝ := 4191153/1000000
def auxLower : ℝ := 3/125
def auxUpper : ℝ := 7/250
def auxCutoff : ℝ := (auxB-auxLambda*auxLower)/2
def tailExponent (d : ℝ) : ℝ := 1-2*d/9-14*d*auxCutoff/9
def inverseSlope : Fin 2 → ℝ := ![1,1/2]
def inverseConst : Fin 2 → ℝ := ![0,1/2]
def inverseWidth : Fin 2 → ℝ := ![1,0]
def plainSlope : Fin 3 → ℝ := ![2,2-2/auxLambda,2]
def plainConst : Fin 3 → ℝ := ![0,auxB/auxLambda,auxUpper]
def plainWidth : Fin 3 → ℝ := ![1,0,0]
def pairIndex (i : Fin 2) (j : Fin 3) : Fin 7 := ⟨3*i.val+j.val,by omega⟩
def count (d S : ℝ) : ℝ := Saturated.rho d-physicalGain d S 1
def cutoff (d S : ℝ) : ℝ := (count d S-1/6)/(5/6-d)

theorem pair_identity {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (S : ℝ) (i : Fin 2) (j : Fin 3) :
    Saturated.rho d-crossing (5/6-d) d
      (pairSlope (inverseSlope i) (plainSlope j))
      (pairConst (inverseSlope i) (plainSlope j) (inverseConst i) (plainConst j))
      (pairWidth (inverseSlope i) (plainSlope j) (inverseWidth i) (plainWidth j)) S=
        slope d (pairIndex i j)*S+offset d (pairIndex i j) := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hden0 : (0:ℝ) < (5+(-2*d)) := by
    have he : (5+(-2*d))=(92/25:ℝ)+2*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hnz0 := ne_of_gt hden0
  have hden1 : (0:ℝ) < (52867295+(-25146918*d)) := by
    have he : (52867295+(-25146918*d))=(906758228/25:ℝ)+25146918*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hnz1 := ne_of_gt hden1
  have hden2 : (0:ℝ) < (15+(-6*d)) := by
    have he : (15+(-6*d))=(276/25:ℝ)+6*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hnz2 := ne_of_gt hden2
  have hden3 : (0:ℝ) < (25+(-18*d)) := by
    have he : (25+(-18*d))=(328/25:ℝ)+18*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hnz3 := ne_of_gt hden3
  have hden4 : (0:ℝ) < 1 := by
    norm_num
  have hnz4 := ne_of_gt hden4
  have hden5 : (0:ℝ) < (1586018850+(-1388815080*d)+(301763016*(d^2))) := by
    have he : (1586018850+(-1388815080*d)+(301763016*(d^2)))=(500530541856/625:ℝ)+25063960488*(d-31/50)^0*(33/50-d)^2+24762197472*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hnz5 := ne_of_gt hden5
  have hden6 : (0:ℝ) < (3750+(-1500*d)) := by
    have he : (3750+(-1500*d))=2760+1500*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hnz6 := ne_of_gt hden6
  have hden7 : (0:ℝ) < (375+(-420*d)+(108*(d^2))) := by
    have he : (375+(-420*d)+(108*(d^2)))=(90528/625:ℝ)+7044*(d-31/50)^0*(33/50-d)^2+6936*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hnz7 := ne_of_gt hden7
  have hden8 : (0:ℝ) < (2543364750+(-2920568520*d)+(761289048*(d^2))) := by
    have he : (2543364750+(-2920568520*d)+(761289048*(d^2)))=(592129397568/625:ℝ)+48652963464*(d-31/50)^0*(33/50-d)^2+47891674416*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hnz8 := ne_of_gt hden8
  have hden9 : (0:ℝ) < (93750+(-105000*d)+(27000*(d^2))) := by
    have he : (93750+(-105000*d)+(27000*(d^2)))=(181056/5:ℝ)+1761000*(d-31/50)^0*(33/50-d)^2+1734000*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hnz9 := ne_of_gt hden9
  have hden10 : (0:ℝ) < (3750000000+(-1500000000*d)) := by
    have he : (3750000000+(-1500000000*d))=2760000000+1500000000*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hnz10 := ne_of_gt hden10

  fin_cases i <;> fin_cases j <;>
    norm_num [pairIndex,inverseSlope,inverseConst,inverseWidth,plainSlope,plainConst,plainWidth,
      auxB,auxLambda,auxUpper,pairSlope,pairConst,pairWidth,crossing,Saturated.rho,slope,offset] <;>
    field_simp (disch := first | assumption | positivity | linarith) <;> ring

theorem tail_identity {d : ℝ} (hd1 : d ≤ 33/50) : Saturated.rho d-tailExponent d=offset d 6 := by
  norm_num [Saturated.rho,tailExponent,auxCutoff,auxB,auxLambda,auxLower,offset]
  have hden : 5-2*d ≠ 0 := by linarith
  field_simp (disch := first | assumption | linarith) <;> ring

theorem count_covers_faces {d S : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    (∀i j,mixedFace (inverseSlope i) (plainSlope j) (inverseConst i) (plainConst j)
      (inverseWidth i) (plainWidth j) d (cutoff d S) S ≤ count d S) ∧
    tailExponent d ≤ count d S := by
  have hd : 0 ≤ d := by linarith
  have ha : 0 < 5/6-d := by linarith
  constructor
  · intro i j
    have hgain := FiniteGain.gain_le (slope d) (offset d) S 1 (pairIndex i j)
    have hid := pair_identity hd0 hd1 S i j
    have hcross : crossing (5/6-d) d
        (pairSlope (inverseSlope i) (plainSlope j))
        (pairConst (inverseSlope i) (plainSlope j) (inverseConst i) (plainConst j))
        (pairWidth (inverseSlope i) (plainSlope j) (inverseWidth i) (plainWidth j)) S ≤ count d S := by
      dsimp [count,physicalGain]
      linarith only [hid,hgain]
    apply face_at_cutoff ha hd _ hcross
    fin_cases i <;> fin_cases j <;> norm_num [pairSlope,inverseSlope,plainSlope,auxLambda]
  · have hgain := FiniteGain.gain_le (slope d) (offset d) S 1 6
    have hid := tail_identity hd1
    have hz : slope d 6=0 := by norm_num [slope]
    rw [hz,zero_mul,zero_add,mul_one] at hgain
    dsimp [count,physicalGain]
    linarith only [hid,hgain]

theorem aux_length_gates : (81/200:ℝ) < auxCutoff ∧ auxCutoff < 9/20 ∧
    2*(1-2*auxCutoff)/9 < auxLower := by
  norm_num [auxCutoff,auxB,auxLambda,auxLower]

theorem cutoff_bounds {d S : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) (hS : 0 ≤ S) :
    1 ≤ cutoff d S ∧ cutoff d S ≤ 3/2 := by
  have ha : 0 < 5/6-d := by linarith
  have hden : 0 < 5-2*d := by linarith
  have hcap := physicalGain_cap (S:=S) hd0 hd1 (show (0:ℝ) ≤ 1 by norm_num)
  have hgain : 0 ≤ physicalGain d S 1 :=
    FiniteGain.gain_nonneg (coefficient_nonneg hd0 hd1).1 (coefficient_nonneg hd0 hd1).2 hS (by norm_num)
  have hnum : 0 ≤ -1200*d^2+1018*d-45 := by
    have hp := mul_nonneg (sub_nonneg.mpr hd0) (sub_nonneg.mpr hd1)
    nlinarith only [hd0,hd1,hp]
  have hlo : 0 ≤ Saturated.rho d-3/200-1/6-(5/6-d) := by
    have he : Saturated.rho d-3/200-1/6-(5/6-d)=
        (-1200*d^2+1018*d-45)/(600*(5-2*d)) := by
      unfold Saturated.rho
      field_simp (disch := first | linarith | positivity) <;> ring
    rw [he]
    exact div_nonneg hnum (by positivity)
  have hhi : 0 ≤ 1/6+(3/2)*(5/6-d)-Saturated.rho d := by
    have he : 1/6+(3/2)*(5/6-d)-Saturated.rho d=(6*d-5)^2/(12*(5-2*d)) := by
      unfold Saturated.rho
      field_simp (disch := first | linarith | positivity) <;> ring
    rw [he]
    positivity
  unfold cutoff count
  constructor
  · apply (le_div_iff₀ ha).mpr
    linarith only [hcap,hlo]
  · apply (div_le_iff₀ ha).mpr
    linarith only [hgain,hhi]

theorem short_fiber {d S r m E : ℝ}
    (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) (hlen : cutoff d S ≤ r+m)
    (hI : E ≤ max (1-d*r-d*S) (1-d/2-d*r/2))
    (hP : E ≤ max (max (1-2*d*m-d*S)
      (1-d*auxB/auxLambda-d*(2-2/auxLambda)*m))
      (max (1-2*d*m-d*auxUpper) (tailExponent d))) : E ≤ count d S := by
  have hfaces := count_covers_faces (S:=S) hd0 hd1
  apply seven_face_count (u:=inverseSlope) (c:=inverseConst) (w:=inverseWidth)
    (v:=plainSlope) (e:=plainConst) (z:=plainWidth)
    (d:=d) (t:=cutoff d S) (S:=S) (r:=r) (m:=m) (tail:=tailExponent d)
    ?_ ?_ (by linarith) hlen ?_ ?_ hfaces.1 hfaces.2
  · intro i
    fin_cases i <;> norm_num [inverseSlope]
  · intro j
    fin_cases j <;> norm_num [plainSlope,auxLambda]
  · convert hI using 1 <;> norm_num [inverseSlope,inverseConst,inverseWidth] <;> ring
  · convert hP using 1 <;> norm_num [plainSlope,plainConst,plainWidth] <;> ring

theorem global_plain_faces {d S m E : ℝ} (hd : 0 ≤ d) (hS : auxLower ≤ S)
    (hold : E ≤ 1-2*d*m-d*min S (2*(1-2*m)/9))
    (haux : 81/200 ≤ m → m ≤ auxCutoff →
      E ≤ 1-2*d*m-d*min S (min auxUpper ((auxB-2*m)/auxLambda))) :
    E ≤ max (max (1-2*d*m-d*S) (1-d*auxB/auxLambda-d*(2-2/auxLambda)*m))
      (max (1-2*d*m-d*auxUpper) (tailExponent d)) := by
  by_cases hlo : 81/200 ≤ m
  · by_cases hhi : m ≤ auxCutoff
    · have h := auxiliary_plain_faces hd (haux hlo hhi)
      have he : 1-2*d*m-d*((auxB-2*m)/auxLambda)=
          1-d*auxB/auxLambda-d*(2-2/auxLambda)*m := by ring
      rw [he] at h
      apply h.trans
      apply max_le
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · apply max_le
        · exact (le_max_left _ _).trans (le_max_right _ _)
        · exact (le_max_right _ _).trans (le_max_left _ _)
    · have htail := old_plain_tail hd (le_of_not_ge hhi) (aux_length_gates.2.2.le.trans hS) hold
      exact htail.trans ((le_max_right _ _).trans (le_max_right _ _))
  · have hc : auxUpper ≤ 2*(1-2*m)/9 := by norm_num [auxUpper] at *; linarith
    have hm := mul_le_mul_of_nonneg_left (min_le_min_left S hc) hd
    have hsmall : E ≤ 1-2*d*m-d*min S auxUpper := by linarith only [hold,hm]
    rcases le_total S auxUpper with h|h
    · rw [min_eq_left h] at hsmall
      exact hsmall.trans ((le_max_left _ _).trans (le_max_left _ _))
    · rw [min_eq_right h] at hsmall
      exact hsmall.trans ((le_max_left _ _).trans (le_max_right _ _))

theorem weighted_short_fiber_aux {d p S r m E : ℝ}
    (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) (hp : p ≤ 1/2) (hS : auxLower ≤ S)
    (hlen : cutoff d S ≤ r+m)
    (hI : E ≤ 1-d*r-2*d*p*min S ((1-r)/2))
    (hold : E ≤ 1-2*d*m-2*d*p*min S (2*(1-2*m)/9))
    (haux : 81/200 ≤ m → m ≤ auxCutoff →
      E ≤ 1-2*d*m-2*d*p*min S (min auxUpper ((auxB-2*m)/auxLambda))) :
    E+2*d*p*S ≤ count d S+d*S := by
  have hd : 0 ≤ d := by linarith
  have hi := PR63Adaptation.inverse_half_faces hd
    (PR63Adaptation.amplitude_to_half hd hp (min_le_left _ _) hI)
  have ho := PR63Adaptation.amplitude_to_half hd hp (min_le_left _ _) hold
  have ha := fun hm0 hm1 => PR63Adaptation.amplitude_to_half hd hp (min_le_left _ _) (haux hm0 hm1)
  have hh := short_fiber hd0 hd1 hlen hi (global_plain_faces hd hS ho ha)
  linarith only [hh]

end Sil.Uneven.Bootstrap
#print axioms Sil.Uneven.Bootstrap.pair_identity
#print axioms Sil.Uneven.Bootstrap.count_covers_faces
#print axioms Sil.Uneven.Bootstrap.cutoff_bounds
#print axioms Sil.Uneven.Bootstrap.short_fiber
#print axioms Sil.Uneven.Bootstrap.weighted_short_fiber_aux
