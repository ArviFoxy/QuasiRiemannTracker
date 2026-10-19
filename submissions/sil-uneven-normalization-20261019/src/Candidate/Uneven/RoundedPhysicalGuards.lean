/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Exact physical shortening and continuation margins at the rational endpoint. -/
import Candidate.Uneven.RoundedRowsBase

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Sil.Uneven.RoundedRows

def physicalGuard (g : ℕ) : ℝ :=
  let x := 1+ell-h
  let dm := h-3/2000
  let dp := h+upper_padding
  let c := (399999/10000000:ℝ)
  let B := planeB 6
  let L := planeLambda 6
  let lo := 1-y/dm
  let hi := 1-y/dp+3/2000
  let clo := (B-2*hi)/L
  let chi := (B-2*lo)/L
  match g with
  | 0 => theta-874/1000
  | 1 => 7/8-theta
  | 2 => ell-1672/10000
  | 3 => 1674/10000-ell
  | 4 => h-793/1000
  | 5 => 798/1000-h
  | 6 => y-458/1000
  | 7 => 463/1000-y
  | 8 => x-ell
  | 9 => y-x
  | 10 => 2*x-y
  | 11 => 1/2-y
  | 12 => h-1/2
  | 13 => 2*y-h
  | 14 => ell-1/6
  | 15 => 1/5-ell
  | 16 => h-4*ell
  | 17 => y/dm-1/2
  | 18 => 99-y/(1/200)
  | 19 => (42/10)*ell-y
  | 20 => y/2-h*(17/50-1/6)-1/50-7/100
  | 21 => y/20-(1+h)/1000-1/4000
  | 22 => h/600-1/1000-1/4000
  | 23 => ell/dp-1/5
  | 24 => dm-1/2
  | 25 => 1-dp
  | 26 => 2*y/dp-1
  | 27 => 1/6-(2*y/dm-1)
  | 28 => (8/10)*(1-6*(1/100))-3/4
  | 29 => lo-405/1000
  | 30 => 4224/10000-hi
  | 31 => clo-365/10000
  | 32 => 38/1000-chi
  | 33 => L-2
  | 34 => 1-405/1000-B/2-(9-L)*(4/100)/2
  | 35 => (7/18-1/500)*(3/2000)+(1-B)/18+(L/18-1/4)*c
  | _ => 0

theorem all_physical_guards {g : ℕ} (hg : g ≤ 35) : 0 < physicalGuard g := by
  interval_cases g <;>
    norm_num [physicalGuard,theta,h,ell,y,upper_padding,planeB,planeLambda]

theorem parameter_identities : ell=11/3-4*theta ∧ y=h-2*ell ∧
    (1+ell-h)+y=1-ell := by norm_num [theta,h,ell,y]

end Sil.Uneven.RoundedRows
#print axioms Sil.Uneven.RoundedRows.all_physical_guards
