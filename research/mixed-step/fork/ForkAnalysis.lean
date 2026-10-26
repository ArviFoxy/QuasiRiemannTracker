import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularCallbacks
open Lean Meta Elab Command

/-! Fork set of the NF source step.

`tainted`: Collet declarations whose statement (definitions and structures: also value)
depends on the HIGH gain, the uniform detector cutoff, or the source validity predicate.
`closure`: everything the proof of `nf_truncated` / `nf_step_of_truncated` uses.
The fork restates exactly `tainted ∩ closure`. -/

def seedNames : List Name := [
  `QRH.Record1252270103Source.High.gain,
  `QRH.Record1252270103Source.High.cutoff,
  `Record1252270103Finite.SourceValid ]

def roots : List Name := [
  `QRH.Record1252270103Source.InitialRegularToTruncated.nf_truncated,
  `QRH.Record1252270103Source.InitialTruncated.nf_step_of_truncated ]

/-- The NF step of the repeated-mark graph always has a HIGH parent: the natural branch is not
traversed. -/
def stopNames : List Name := [
  `QRH.Record1252270103Source.High.GlobalPhysical.regular_supplier_natural ]

def inCollet (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if (`Submissions.hailey_collet_1252270103).isPrefixOf m then some m else none
  | none => none

def stmtRefs (ci : ConstantInfo) : NameSet :=
  let tyRefs := ci.type.getUsedConstantsAsSet
  match ci with
  | .defnInfo d => tyRefs.append d.value.getUsedConstantsAsSet
  | .opaqueInfo d => tyRefs.append d.value.getUsedConstantsAsSet
  | _ => tyRefs

def allRefs (ci : ConstantInfo) : NameSet :=
  match ci.value? (allowOpaque := true) with
  | some v => ci.type.getUsedConstantsAsSet.append v.getUsedConstantsAsSet
  | none => ci.type.getUsedConstantsAsSet

run_cmd do
  let env ← getEnv
  -- taint (statement level)
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if (inCollet env n).isSome then
      for r in (stmtRefs ci).toList do
        rev := rev.insert r ((rev.getD r #[]).push n)
      if let .ctorInfo c := ci then
        rev := rev.insert n ((rev.getD n #[]).push c.induct)
      if let .recInfo r := ci then
        for t in r.all do rev := rev.insert t ((rev.getD t #[]).push n)
  let mut tainted : NameSet := {}
  let mut queue : Array Name := #[]
  for s in seedNames do
    tainted := tainted.insert s
    queue := queue.push s
  let mut i := 0
  while i < queue.size do
    let x := queue[i]!
    i := i + 1
    for y in rev.getD x #[] do
      if !tainted.contains y then
        tainted := tainted.insert y
        queue := queue.push y
  -- proof closure of the roots (Collet declarations only)
  let mut closure : NameSet := {}
  let mut stack : Array Name := roots.toArray
  while h : stack.size > 0 do
    let x := stack.back
    stack := stack.pop
    if closure.contains x || stopNames.contains x then continue
    closure := closure.insert x
    if let some ci := env.find? x then
      for r in (allRefs ci).toList do
        if (inCollet env r).isSome && !closure.contains r then
          stack := stack.push r
  -- report tainted ∩ closure by module
  let mut byMod : Std.HashMap Name (Array Name) := {}
  let mut cnt : Nat := 0
  for n in closure.toList do
    if tainted.contains n then
      if let some m := inCollet env n then
        cnt := cnt + 1
        byMod := byMod.insert m ((byMod.getD m #[]).push n)
  let modsSorted := byMod.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let mut lines : Array String := #[]
  for (m, ns) in modsSorted do
    let shown := ns.toList.filter (fun n => !n.isInternal)
    lines := lines.push (m.toString ++ "\t" ++ String.intercalate " " (shown.map toString))
    logInfo m!"{m} {ns.size}"
  -- also: all tainted names (any module), for reference rewriting
  let mut all : Array String := #[]
  for n in tainted.toList do
    if (inCollet env n).isSome && !n.isInternal then all := all.push n.toString
  -- declarations of the fork whose type, value or proof mentions a seed directly
  let mut direct : Array String := #[]
  for n in closure.toList do
    if tainted.contains n && !(seedNames.contains n) then
      if let some ci := env.find? n then
        let refs := allRefs ci
        let hits := seedNames.filter (fun s => refs.contains s)
        if !hits.isEmpty then
          direct := direct.push (n.toString ++ "\t" ++ String.intercalate " " (hits.map toString))
  IO.FS.writeFile "/home/user/lean-env/fork_direct.tsv" (String.intercalate "\n" direct.toList)
  IO.FS.writeFile "/home/user/lean-env/fork_closure.tsv" (String.intercalate "\n" lines.toList)
  IO.FS.writeFile "/home/user/lean-env/fork_tainted_all.txt" (String.intercalate "\n" all.toList)
  logInfo m!"closure: {closure.size}, fork modules: {modsSorted.size}, fork declarations: {cnt}, tainted total: {all.size}"
