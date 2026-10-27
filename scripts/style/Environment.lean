-- The runner prepends `import Mathlib` and the audit's private imports.
open Lean Elab Command Meta

def styleDeps (ci : ConstantInfo) : Array Name :=
  let structural := match ci with
    | .inductInfo v => v.ctors.toArray
    | .recInfo v => v.all.toArray
    | _ => #[]
  ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]) ++ structural

def styleModule (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => ""

def styleKind (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

partial def styleCone (env : Environment) : Std.HashSet Name := Id.run do
  let mut queue := #[`PropertyF.Ground.target]
  let mut seen : Std.HashSet Name := {}
  while !queue.isEmpty do
    let n := queue.back!
    queue := queue.pop
    if seen.contains n then continue
    seen := seen.insert n
    -- Pinned upstream modules cannot depend on this project.
    unless (styleModule env n).startsWith "PropertyF." do continue
    if let some ci := env.find? n then
      queue := queue ++ styleDeps ci
  return seen

/-- Number of structurally distinct expression nodes; avoids exponential unfolding of sharing. -/
partial def styleNodes (type : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut todo := #[type]
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if seen.contains e then continue
    seen := seen.insert e
    match e with
    | .forallE _ d b _ | .lam _ d b _ => todo := todo.push d |>.push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .app f a => todo := todo.push f |>.push a
    | _ => pure ()
  return seen.size

def styleBinderFallback (type : Expr) : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut t := type
  let mut e := 0; let mut i := 0; let mut s := 0; let mut c := 0
  while let .forallE _ _ b bi := t do
    match bi with
    | .default => e := e+1
    | .implicit => i := i+1
    | .strictImplicit => s := s+1
    | .instImplicit => c := c+1
    t := b
  return (e, i, s, c, 999999)

def styleBinders (type : Expr) : MetaM (Nat × Nat × Nat × Nat × Nat) := do
  forallTelescope type fun xs _ => do
    let mut e := 0; let mut i := 0; let mut s := 0; let mut c := 0; let mut h := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      match d.binderInfo with
      | .default => e := e + 1
      | .implicit => i := i + 1
      | .strictImplicit => s := s + 1
      | .instImplicit => c := c + 1
      try
        if ← isProp d.type then
          if h != 999999 then h := h + 1
      catch _ =>
        h := 999999
    return (e, i, s, c, h)

set_option maxHeartbeats 0 in
run_cmd Command.liftTermElabM do
  let env ← getEnv
  unless (env.find? `PropertyF.Ground.target).isSome do
    throwError "target is missing; build the project before running the survey"
  let sampleText ← IO.FS.readFile "scripts/style/.sample-modules"
  let sample := Std.HashSet.ofList (sampleText.splitOn "\n")
  let cone := styleCone env
  let out ← IO.FS.Handle.mk "scripts/style/.environment.tsv" .write
  out.putStrLn "module\tname\tkind\tcone\ttype_nodes\texplicit\timplicit\tstrict\tinstance\thypotheses\ttype_hash"
  let moduleNames := env.header.moduleNames.map (·.toString)
  let kinds := moduleNames.map fun mod =>
    if mod.startsWith "PropertyF." then 1
    else if sample.contains mod then 2
    else if mod.startsWith "Mathlib." then 3
    else 0
  IO.eprintln s!"imported modules: {moduleNames.size}, sampled present: {(kinds.filter (· == 2)).size}"
  let candidates := env.constants.fold (init := #[]) fun acc n ci => Id.run do
    let some idx := env.getModuleIdxFor? n | return acc
    let i := idx.toNat
    let k := kinds[i]!
    if k == 1 then return acc.push (n, ci, moduleNames[i]!)
    if k == 2 then
      match ci with
      | .thmInfo _ | .axiomInfo _ => return acc.push (n, ci, moduleNames[i]!)
      | _ => return acc
    return acc
  for ((n, ci, mod), index) in candidates.toList.zipIdx do
    if index % 1000 == 0 then IO.eprintln s!"environment declarations: {index}/{candidates.size}, {n}"
    let (e, i, s, c, h) ← try styleBinders ci.type catch _ => pure (styleBinderFallback ci.type)
    let row := s!"{mod}\t{n}\t{styleKind ci}\t{if cone.contains n then 1 else 0}\t{styleNodes ci.type}\t{e}\t{i}\t{s}\t{c}\t{h}\t{hash ci.type}"
    out.putStrLn row
  -- Verify hash candidates with Lean's syntactic expression equality. This is
  -- deliberately narrower than definitional equality and does not change imports.
  let mut buckets : Std.HashMap UInt64 (Array (Name × Expr)) := {}
  for (n, ci, mod) in candidates do
    if mod.startsWith "PropertyF." && !(n.toString.splitOn ".").getLast!.startsWith "_" then
      match ci with
      | .thmInfo _ =>
        let h := hash ci.type
        buckets := buckets.insert h ((buckets[h]?.getD #[]).push (n, ci.type))
      | _ => pure ()
  let (hashRows, exactRows) := env.constants.fold (init := (#[], #[])) fun (hs, es) n ci => Id.run do
    let some idx := env.getModuleIdxFor? n | return (hs, es)
    let i := idx.toNat
    if kinds[i]! != 2 && kinds[i]! != 3 then return (hs, es)
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      let h := hash ci.type
      let some entries := buckets[h]? | return (hs, es)
      let mut es := es
      for (p, ty) in entries do
        if ty == ci.type then es := es.push s!"{p}\t{n}\t{moduleNames[i]!}"
      return (hs.push s!"{h}\t{n}\t{moduleNames[i]!}", es)
    | _ => return (hs, es)
  let hashOut ← IO.FS.Handle.mk "scripts/style/.mathlib-hashes.tsv" .write
  for row in hashRows do hashOut.putStrLn row
  let exactOut ← IO.FS.Handle.mk "scripts/style/.mathlib-exact.tsv" .write
  for row in exactRows do exactOut.putStrLn row
  let projectOut ← IO.FS.Handle.mk "scripts/style/.project-exact.tsv" .write
  for (_, entries) in buckets.toList do
    for ((a, ta), i) in entries.toList.zipIdx do
      for (b, tb) in entries.toList.drop (i+1) do
        if ta == tb then projectOut.putStrLn s!"{a}\t{b}"
