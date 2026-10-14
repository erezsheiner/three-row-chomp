import Lean

/-!
Audit tooling, not a proof: independently enumerate every constant serialized
in each intended module's highest-visibility object-file part. This checks that
the elaborated environment census did not silently omit private/generated names.
-/

open Lean

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let manifest ← IO.ofExcept (Json.parse (← IO.FS.readFile "../final-source-manifest.json"))
  let modules ← IO.ofExcept (manifest.getObjValAs? (Array String) "modules")
  let output ← IO.FS.Handle.mk "../final-serialized-module-census.jsonl" .write
  for module in modules do
    let path ← findOLean module.toName
    let mut files := #[path]
    for level in #[OLeanLevel.server, OLeanLevel.private] do
      let part := level.adjustFileName path
      if ← part.pathExists then files := files.push part
    let parts ← readModuleDataParts files
    let some highestPart := parts[parts.size - 1]? | throw (IO.userError s!"No module data for {module}")
    let highest := highestPart.1
    for name in highest.constNames, info in highest.constants do
      let kind := match info with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
      output.putStrLn (Json.mkObj [("module", toJson module), ("name", toJson name.toString), ("kind", toJson kind)]).compress
  output.flush
  IO.println s!"Serialized module census complete for {modules.size} intended modules."
