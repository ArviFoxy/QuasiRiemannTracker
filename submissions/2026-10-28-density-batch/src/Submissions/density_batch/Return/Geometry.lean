/- Repeated marks: fork of Collet's final-stage module Geometry (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the PR69 `Parameters` at theta = 174799/200000, h = 8053/10000 -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Submissions.density_batch.Return.Constants
set_option autoImplicit false
namespace QRH.DensityBatch.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalParameters : Parameters where
  theta := QRH.DensityBatch.Return.theta
  ell := QRH.DensityBatch.Return.ell
  x := QRH.DensityBatch.Return.x
  y := QRH.DensityBatch.Return.y
  ell_pos := by norm_num [QRH.DensityBatch.Return.ell,QRH.DensityBatch.Return.c]
  sixth_lt_ell := by norm_num [QRH.DensityBatch.Return.ell,QRH.DensityBatch.Return.c]
  ell_lt_fifth := by norm_num [QRH.DensityBatch.Return.ell,QRH.DensityBatch.Return.c]
  ell_lt_x := by norm_num [QRH.DensityBatch.Return.x,QRH.DensityBatch.Return.ell,QRH.DensityBatch.Return.c,QRH.DensityBatch.Return.h]
  x_lt_y := by norm_num [QRH.DensityBatch.Return.x,QRH.DensityBatch.Return.y,QRH.DensityBatch.Return.ell,QRH.DensityBatch.Return.c,QRH.DensityBatch.Return.h]
  y_lt_half := by norm_num [QRH.DensityBatch.Return.y,QRH.DensityBatch.Return.ell,QRH.DensityBatch.Return.c,QRH.DensityBatch.Return.h]
  x_add_y := by dsimp [QRH.DensityBatch.Return.x,QRH.DensityBatch.Return.y];ring
  dilation_gap := by norm_num [QRH.DensityBatch.Return.x,QRH.DensityBatch.Return.y,QRH.DensityBatch.Return.ell,QRH.DensityBatch.Return.c,QRH.DensityBatch.Return.h]
  tuple_margin_neg := by norm_num [QRH.DensityBatch.Return.x,QRH.DensityBatch.Return.y,QRH.DensityBatch.Return.ell,QRH.DensityBatch.Return.c,QRH.DensityBatch.Return.h]
  signal_boundary := QRH.DensityBatch.Return.geometry_mellin
end QRH.DensityBatch.Return.Geometry
