/- Repeated marks: fork of Collet's generic physical return module PhysicalDirect.Data (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return so that the
physical schedule applies the physical face globally (Lemma D). -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.repeated_marks_20261024.ReturnD.Schedule
import Submissions.hailey_collet_1252270103.Record1252270103Return.GenericData
open QRH.Record1252270103Return

namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
abbrev BaselineData := QRH.Record1252270103Return.GenericPhysical.BaselineData
abbrev BaselineSourceData (D : BaselineData) := QRH.Record1252270103Return.GenericPhysical.BaselineSourceData D
end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
