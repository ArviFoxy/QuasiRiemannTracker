import Candidate.Main
open Lean

/-- Print `module<TAB>constant` for every constant in the transitive closure of the two
candidate theorems, so the export can be attributed to developments. -/
partial def closure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut refs := ci.type.getUsedConstants.toList
        if let some v := ci.value? (allowOpaque := true) then
          refs := refs ++ v.getUsedConstants.toList
        match ci with
        | .inductInfo i => refs := refs ++ i.ctors ++ i.all
        | .ctorInfo c => refs := refs ++ [c.induct]
        | .recInfo r => refs := refs ++ r.all
        | _ => pure ()
        for r in refs do
          if !seen.contains r then stack := r :: stack
  return seen

#eval show CoreM Unit from do
  let env ← getEnv
  let s := closure env [`Candidate.bound, `Candidate.bound_sharp]
  let h ← IO.FS.Handle.mk "module_of.tsv" .write
  let mut count := 0
  for n in s.toList do
    let m := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => "<local>"
    h.putStrLn s!"{m}\t{n}"
    count := count + 1
  IO.println s!"closure constants: {count}"
