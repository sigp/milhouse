import Tree
import Lean

open Lean Elab Command

/-!
Conservative definition-body dependencies of the available in-scope API roots.
This follows constants in definition values, including types inside those
values and complete supplied dictionaries. It does not specialize arguments,
resolve abstract generic callbacks, follow theorem proofs, or prove execution
reachability. Opaque declarations are recorded without opening their bodies.
The driver checks the root inventory, completion, and forbidden model references.
-/

private structure ModelAuditRoot where
  label : String
  declaration : String
  deriving FromJson

set_option maxRecDepth 100000
set_option maxHeartbeats 0

run_cmd do
  let env := (← getEnv).setExporting false
  let source ← liftIO <| IO.FS.readFile "PROGRESSIVE_LIST_MODEL_ROOTS.json"
  let parsed ← ofExcept <| Json.parse source
  let roots ← ofExcept <| fromJson? (α := List ModelAuditRoot) parsed
  for root in roots do
    let rootName := root.declaration.toName
    let some rootInfo := env.find? rootName | throwError "Missing root: {rootName}"
    unless rootInfo.hasValue do
      throwError "Root has no definition body: {rootName}"
    let mut pending : List Name := [rootName]
    let mut seen : NameSet := {}
    let mut nodes : Array Json := #[]
    while !pending.isEmpty do
      let declName := pending.head!
      pending := pending.tail!
      if seen.contains declName then continue
      seen := seen.insert declName
      let some info := env.find? declName | throwError "Missing dependency: {declName}"
      if let some value := info.value? then
        pending := value.getUsedConstants.toList ++ pending
      if let some idx := env.getModuleIdxFor? declName then
        let moduleName := env.header.moduleNames[idx]!
        if Name.isPrefixOf `Tree moduleName then
          let kind := match info with
            | .defnInfo _ => "definition"
            | .opaqueInfo _ => "opaque"
            | .axiomInfo _ => "axiom"
            | .thmInfo _ => "theorem"
            | _ => "type"
          nodes := nodes.push (Json.mkObj [
            ("name", toJson declName.toString),
            ("module", toJson moduleName.toString),
            ("kind", toJson kind)])
    liftIO <| IO.println (Json.mkObj [
      ("kind", toJson "root"), ("label", toJson root.label),
      ("declaration", toJson root.declaration),
      ("nodes", Json.arr nodes)]).compress
  liftIO <| IO.println (Json.mkObj [
    ("kind", toJson "summary"), ("roots", toJson roots.length)]).compress
