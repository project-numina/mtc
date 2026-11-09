-- The runner prepends Lean and the target audit private imports.
open Lean Elab Command Meta
set_option maxHeartbeats 0 in
run_cmd Command.liftTermElabM do
  let env ← getEnv
  let out ← IO.FS.Handle.mk "scripts/style/.proposition-definitions.tsv" .write
  out.putStrLn "module\tname"
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!.toString
    unless mod.startsWith "MTC." do continue
    let candidate := match ci with
      | .defnInfo _ | .opaqueInfo _ => true
      | _ => false
    unless candidate do continue
    let proof ← try isProp ci.type catch _ => pure false
    if proof then out.putStrLn s!"{mod}\t{name}"
