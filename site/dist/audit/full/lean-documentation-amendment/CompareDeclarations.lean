import Lean

/-!
Audit tooling only. Compare all serialized constants in the highest-visibility
parts of two independently compiled versions of a module. Expression equality
is `Expr.equal`, not the alpha-equivalence used by `BEq Expr`; binder names and
annotations are therefore included. This does not add mathematical axioms.
-/

open Lean

def sameBase (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && Expr.equal a.type b.type

def sameQuotKind : QuotKind → QuotKind → Bool
  | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
  | _, _ => false

def sameRule (a b : RecursorRule) : Bool :=
  a.ctor == b.ctor && a.nfields == b.nfields && Expr.equal a.rhs b.rhs

def sameConstant (a b : ConstantInfo) : Bool :=
  sameBase a b && match a, b with
  | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe
  | .defnInfo x, .defnInfo y =>
      Expr.equal x.value y.value && x.hints == y.hints && x.safety == y.safety && x.all == y.all
  | .thmInfo x, .thmInfo y => Expr.equal x.value y.value && x.all == y.all
  | .opaqueInfo x, .opaqueInfo y =>
      Expr.equal x.value y.value && x.isUnsafe == y.isUnsafe && x.all == y.all
  | .quotInfo x, .quotInfo y => sameQuotKind x.kind y.kind
  | .inductInfo x, .inductInfo y =>
      x.numParams == y.numParams && x.numIndices == y.numIndices &&
      x.all == y.all && x.ctors == y.ctors && x.numNested == y.numNested &&
      x.isRec == y.isRec && x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive
  | .ctorInfo x, .ctorInfo y =>
      x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams &&
      x.numFields == y.numFields && x.isUnsafe == y.isUnsafe
  | .recInfo x, .recInfo y =>
      x.all == y.all && x.numParams == y.numParams && x.numIndices == y.numIndices &&
      x.numMotives == y.numMotives && x.numMinors == y.numMinors &&
      x.rules.length == y.rules.length && (x.rules.zip y.rules).all (fun (r, s) => sameRule r s) &&
      x.k == y.k && x.isUnsafe == y.isUnsafe
  | _, _ => false

def comparatorControls : IO Unit := do
  let nat := mkConst ``Nat
  let explicitType := Expr.forallE `x nat nat .default
  let implicitType := Expr.forallE `x nat nat .implicit
  let mk (type value : Expr) : ConstantInfo := .defnInfo {
    name := `probe, levelParams := [], type, value,
    hints := .abbrev, safety := .safe, all := [`probe] }
  let a := mk explicitType (mkNatLit 0)
  let b := mk implicitType (mkNatLit 0)
  let c := mk explicitType (mkNatLit 1)
  unless sameConstant a a do throw (IO.userError "Reflexivity control failed")
  unless explicitType == implicitType do throw (IO.userError "Alpha-equivalence control changed")
  if sameConstant a b then throw (IO.userError "Binder-annotation negative control failed")
  if sameConstant a c then throw (IO.userError "Value negative control failed")
  IO.println "Controls passed: identity accepted; changed binder annotation and value rejected."

unsafe def loadParts (path : System.FilePath) : IO (Array (ModuleData × CompactedRegion)) := do
  let mut files := #[path]
  for level in #[OLeanLevel.server, OLeanLevel.private] do
    let part := level.adjustFileName path
    if ← part.pathExists then files := files.push part
  readModuleDataParts files

unsafe def main (args : List String) : IO Unit := do
  comparatorControls
  let [manifestPath, oldRoot, newRoot, outputPath] := args
    | throw (IO.userError "Expected manifest, old object root, new object root, output")
  initSearchPath (← findSysroot)
  let manifest ← IO.ofExcept (Json.parse (← IO.FS.readFile manifestPath))
  let modules ← IO.ofExcept (manifest.getObjValAs? (Array String) "modules")
  let output ← IO.FS.Handle.mk outputPath .write
  let mut total := 0
  for module in modules do
    let rel := module.replace "." "/" ++ ".olean"
    let oldParts ← loadParts (System.FilePath.mk oldRoot / rel)
    let newParts ← loadParts (System.FilePath.mk newRoot / rel)
    let some oldPart := oldParts[oldParts.size - 1]? | throw (IO.userError s!"No old data: {module}")
    let some newPart := newParts[newParts.size - 1]? | throw (IO.userError s!"No new data: {module}")
    let oldData := oldPart.1
    let newData := newPart.1
    unless oldData.constNames.size == oldData.constants.size &&
        newData.constNames.size == newData.constants.size do
      throw (IO.userError s!"Malformed declaration arrays: {module}")
    let mut oldMap : Std.HashMap Name ConstantInfo := {}
    let mut newMap : Std.HashMap Name ConstantInfo := {}
    for name in oldData.constNames, info in oldData.constants do
      unless name == info.name do throw (IO.userError s!"Old name mismatch: {module}/{name}")
      if oldMap.contains name then throw (IO.userError s!"Duplicate old name: {module}/{name}")
      oldMap := oldMap.insert name info
    for name in newData.constNames, info in newData.constants do
      unless name == info.name do throw (IO.userError s!"New name mismatch: {module}/{name}")
      if newMap.contains name then throw (IO.userError s!"Duplicate new name: {module}/{name}")
      newMap := newMap.insert name info
    unless oldMap.size == newMap.size do throw (IO.userError s!"Changed declaration count: {module}")
    for (name, oldInfo) in oldMap do
      let some newInfo := newMap[name]? | throw (IO.userError s!"Missing declaration: {module}/{name}")
      unless sameConstant oldInfo newInfo do
        throw (IO.userError s!"Changed declaration data: {module}/{name}")
      output.putStrLn (Json.mkObj [("module", toJson module), ("name", toJson name.toString),
        ("exactTypeValueAndFieldsIdentical", toJson true)]).compress
    total := total + oldMap.size
    IO.println s!"{module}: {oldMap.size} declarations structurally identical."
  output.flush
  IO.println s!"PASS: {modules.size} modules, {total} serialized declarations identical."
