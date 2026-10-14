import Lean

-- Presentation metadata from revised compiled objects; not proof certification.
open Lean

unsafe def main (args : List String) : IO Unit := do
  let [manifestPath, newRoot, outputPath] := args
    | throw (IO.userError "Expected manifest, revised object root, output")
  initSearchPath (← findSysroot) [System.FilePath.mk newRoot]
  let manifest ← IO.ofExcept (Json.parse (← IO.FS.readFile manifestPath))
  let modules ← IO.ofExcept (manifest.getObjValAs? (Array String) "modules")
  let output ← IO.FS.Handle.mk outputPath .write
  for module in modules do
    let path := System.FilePath.mk newRoot / (module.replace "." "/" ++ ".olean")
    let mut files := #[path]
    for level in #[OLeanLevel.server, OLeanLevel.private] do
      let part := level.adjustFileName path
      if ← part.pathExists then files := files.push part
    let parts ← readModuleDataParts files
    let some highest := parts[parts.size - 1]? | throw (IO.userError s!"No object data: {module}")
    let env ← importModules #[{module := module.toName}] {} (loadExts := true)
    let extract : CoreM Unit := do
      for name in highest.1.constNames do
        let range ← findDeclarationRanges? name
        let line := match range with
          | some r => toJson r.range.pos.line
          | none => Json.null
        output.putStrLn (Json.mkObj [("module", toJson module), ("name", toJson name.toString),
          ("sourceLine", line)]).compress
    discard <| extract.toIO {fileName := "<revised ranges>", fileMap := default} {env}
  output.flush
  IO.println s!"Exported revised compiler source ranges for {modules.size} modules."
