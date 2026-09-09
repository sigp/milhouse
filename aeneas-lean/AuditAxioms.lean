import Tree
import Lean.Util.CollectAxioms

open Lean Elab Command

/-!
Machine-readable axiom inventory for `scripts/aeneas-audit-axioms.py`.
Read the elaborated environment so private and generated theorem declarations
are included. The driver builds first, verifies module coverage, and rejects
unexpected axioms in both declarations and transitive theorem dependencies.
-/

run_cmd do
  let env ← getEnv
  let mut theoremCount := 0
  let mut axiomCount := 0
  for entry in env.constants.toList do
    let declName := entry.1
    if let some idx := env.getModuleIdxFor? declName then
      let moduleName := env.header.moduleNames[idx]!
      if Name.isPrefixOf `Tree moduleName then
        match entry.2 with
        | .thmInfo _ =>
          let axioms ← collectAxioms declName
          liftIO <| IO.println (Json.mkObj [
            ("kind", toJson "theorem"),
            ("module", toJson moduleName.toString),
            ("name", toJson declName.toString),
            ("axioms", toJson (axioms.toList.map Name.toString))]).compress
          theoremCount := theoremCount + 1
        | .axiomInfo _ =>
          liftIO <| IO.println (Json.mkObj [
            ("kind", toJson "axiom"),
            ("module", toJson moduleName.toString),
            ("name", toJson declName.toString)]).compress
          axiomCount := axiomCount + 1
        | _ => pure ()
  let modules := env.header.moduleNames.filter (Name.isPrefixOf `Tree)
  liftIO <| IO.println (Json.mkObj [
    ("kind", toJson "summary"),
    ("modules", toJson (modules.toList.map Name.toString)),
    ("theorems", toJson theoremCount),
    ("axiomDeclarations", toJson axiomCount)]).compress
