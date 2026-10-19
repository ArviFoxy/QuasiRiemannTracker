/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.RoundedRowsBase

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem coarse_gap_0_0 {d p : ℝ}
    (hd : (0/1:ℝ) ≤ d ∧ d ≤ (3/4:ℝ))
    (hp : (0/1:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 ≤ gap 0 0 d p := by
  let bx : ℝ := (d-(0/1:ℝ))/(3/4:ℝ)
  let byv : ℝ := (p-(0/1:ℝ))/(1/2:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : gap 0 0 d p =
    (10279286742492942048154593122771/7500000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (931111084252768734095911308949504922903/253009305000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (51370005666249760886767160154936355759/15813081562500000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (47515273137814907618709187733897230759/50601861000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (104786937122380014818628083087107/75000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (8250792707932433379968307985019999920243/2530093050000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (1464633592063664184578595236152463017991863147/592719522375768750000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (2878891426209023706136736115548360769346111201/4741756179006150000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (23087819697450594337082151859397/75000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (1542409457456153820890444895524950691213/2530093050000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (235760432644742546551276394076780286167072407/592719522375768750000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 +
    (405623944292199661597556232314892882027884351/4741756179006150000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [gap,base,denominator,numerator,theta,reserve,h,y,ell,
      rowHeight,rowCapacity,planeB,planeLambda,bx,byv]
    norm_num
    ring
  rw [hid]
  positivity

theorem coarse_row_0 {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    ∃ i : ℕ, i ≤ 7 ∧ available i d p ∧ row 0 i d p ≤ theta-reserve := by
  refine ⟨0,by norm_num,Or.inl rfl,row_bound_of_gap (denominator_pos (by norm_num) hd hp) ?_⟩
  apply coarse_gap_0_0
  all_goals constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2]

end Sil.Uneven.RoundedRows
