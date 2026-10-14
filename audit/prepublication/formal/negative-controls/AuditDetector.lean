import AuditBadAxiom
import Lean

/-!
Audit tooling only: inspect the elaborated environment of every intended core
module. This file contributes no project theorem and is excluded from the
264-module publication proof census. It writes exact elaborated type trees.
-/

open Lean Meta Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option pp.all true
set_option pp.maxSteps 10000000

namespace PublicationAudit

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def strings (xs : Array String) : Json := Json.arr (xs.map Json.str)

partial def expression (e : Expr) : Json :=
  match e with
  | .bvar n => Json.mkObj [("node", "boundVariable"), ("index", toJson n)]
  | .fvar id => Json.mkObj [("node", "freeVariable"), ("name", toJson id.name.toString)]
  | .mvar id => Json.mkObj [("node", "metavariable"), ("name", toJson id.name.toString)]
  | .sort u => Json.mkObj [("node", "sort"), ("level", toJson (reprStr u))]
  | .const n us => Json.mkObj [("node", "constant"), ("name", toJson n.toString), ("levels", toJson (us.map reprStr))]
  | .app f a => Json.mkObj [("node", "application"), ("function", expression f), ("argument", expression a)]
  | .lam n t b bi => Json.mkObj [("node", "lambda"), ("name", toJson n.toString), ("binderInfo", toJson (reprStr bi)), ("type", expression t), ("body", expression b)]
  | .forallE n t b bi => Json.mkObj [("node", "forall"), ("name", toJson n.toString), ("binderInfo", toJson (reprStr bi)), ("type", expression t), ("body", expression b)]
  | .letE n t v b nonDep => Json.mkObj [("node", "let"), ("name", toJson n.toString), ("type", expression t), ("value", expression v), ("body", expression b), ("nonDependent", toJson nonDep)]
  | .lit l => Json.mkObj [("node", "literal"), ("value", toJson (reprStr l))]
  | .mdata _ b => Json.mkObj [("node", "metadata"), ("body", expression b)]
  | .proj n i b => Json.mkObj [("node", "projection"), ("structure", toJson n.toString), ("index", toJson i), ("body", expression b)]

def readExpected : IO (Array String) := do
  let raw ← IO.FS.readFile "source-manifest.json"
  let json ← IO.ofExcept (Json.parse raw)
  IO.ofExcept (json.getObjValAs? (Array String) "modules")

elab "#audit_publication_environment" : command => liftTermElabM do
  let expected ← readExpected
  let env ← getEnv
  let imported := env.header.moduleNames.map Name.toString
  let missing := expected.filter (!imported.contains ·)
  unless missing.isEmpty do
    throwError "Missing intended imported modules: {missing}"
  let output ← IO.FS.Handle.mk "control-kernel-census.raw.jsonl" .write
  let mut count := 0
  let mut theoremCount := 0
  let mut proofCount := 0
  let mut violations : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!.toString
    unless expected.contains moduleName do continue
    let isProof ← isProp info.type
    let axioms ← collectAxioms name
    let custom := axioms.filter fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound
    let typeText := (← ppExpr info.type).pretty 120
    let typeDeps := info.type.getUsedConstants
    let valueDeps := match info.value? true with
      | some value => value.getUsedConstants
      | none => #[]
    let ranges ← findDeclarationRanges? name
    let line : Json := match ranges with
      | some rs => toJson rs.range.pos.line
      | none => Json.null
    let record := Json.mkObj [
      ("name", toJson name.toString), ("module", toJson moduleName),
      ("kind", toJson (kind info)), ("isProof", toJson isProof),
      ("isUnsafe", toJson info.isUnsafe), ("isPartial", toJson info.isPartial),
      ("universeParameters", toJson (info.levelParams.map Name.toString)),
      ("sourceLine", line), ("typePretty", toJson typeText),
      ("typeExpression", expression info.type),
      ("typeHasMetavariables", toJson info.type.hasMVar),
      ("typeHasFreeVariables", toJson info.type.hasFVar),
      ("axioms", strings (axioms.map Name.toString)),
      ("nonstandardAxioms", strings (custom.map Name.toString)),
      ("directTypeDependencies", strings (typeDeps.map Name.toString)),
      ("directValueDependencies", strings (valueDeps.map Name.toString))]
    output.putStrLn record.compress
    count := count + 1
    if kind info == "theorem" then theoremCount := theoremCount + 1
    if isProof then proofCount := proofCount + 1
    if !custom.isEmpty || info.isUnsafe || info.type.hasMVar || info.type.hasFVar || kind info == "axiom" then
      violations := violations.push (Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName), ("kind", toJson (kind info)), ("nonstandardAxioms", strings (custom.map Name.toString)), ("unsafe", toJson info.isUnsafe)])
  output.flush
  let summary := Json.mkObj [
    ("expectedModules", strings expected), ("importedIntendedModules", strings (imported.filter expected.contains)),
    ("declarationCount", toJson count), ("theoremDeclarationCount", toJson theoremCount),
    ("proofValuedDeclarationCount", toJson proofCount), ("violations", Json.arr violations)]
  IO.FS.writeFile "control-kernel-census.summary.json" summary.pretty
  unless violations.isEmpty do throwError "Full kernel declaration audit found {violations.size} violations"
  logInfo m!"Full project environment census: {count} declarations; {theoremCount} theorem declarations; {proofCount} proof-valued declarations; no disallowed axiom or unsafe project declaration."

end PublicationAudit

#audit_publication_environment
