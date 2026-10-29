/- Repeated marks: fork of Collet's final-stage module TransportInstances (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the widened box `BoundsN` (not PR76 `BoundsR`, which fails here) at the new parameters -/
import Submissions.density_ten.Bridge.TransportGeometry
import Submissions.density_ten.Return.Geometry
set_option autoImplicit false
namespace QRH.DensityTen.Return.Geometry
open QRH.DensityTen.Bridge.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalBounds : @BoundsN finalParameters := by
  refine @BoundsN.mk finalParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,QRH.Record1252270103Return.Geometry.dPlus,QRH.Record1252270103Return.Geometry.signal,QRH.Record1252270103Return.Geometry.signalShift,finalParameters,
    QRH.DensityTen.Return.theta,QRH.DensityTen.Return.h,QRH.DensityTen.Return.ell,QRH.DensityTen.Return.x,QRH.DensityTen.Return.y,QRH.DensityTen.Return.c] <;> norm_num
end QRH.DensityTen.Return.Geometry
