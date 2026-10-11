import Lean
import Lean.Util.CollectAxioms

/-! Environment-derived declaration audit for the pinned Lean 4.34.1 toolchain.
Import this helper AFTER the modules being audited. It does not import Math115
or choose a hand-written theorem roster. Prefix and defining-module filters are
unioned, so private declarations from selected modules are included too.

Example driver:
  import Math115
  import ResearchAudit.EnvironmentAudit
  #environment_audit prefixes [Math115] modules [] headlines
    [Math115.IdealRepairRefinement.feasibleChain_poincare_d17_refined]

The command writes exactly one JSON object to stdout. The caller must bind the
JSON to a successful compiler exit and the imported object/source hashes.
-/
namespace ResearchAudit.EnvironmentAudit
open Lean Elab Command Meta

private def namesJson (ns : Array Name) : Json :=
  toJson (ns.map toString)

private def kind (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def definingModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some i => (env.header.modules[i]!).module
  | none => env.mainModule

private def dependencies (ci : ConstantInfo) : Array Name := Id.run do
  let mut names := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    names := names ++ value.getUsedConstants
  if let .inductInfo v := ci then
    names := names ++ v.ctors.toArray
  return (names.foldl (fun s n => s.insert n) ({} : NameSet)).toArray.qsort Name.lt

private partial def closure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : Except String NameSet := do
  match pending with
  | [] => return seen
  | name :: rest =>
    if seen.contains name then
      closure env rest seen
    else
      let some ci := env.find? name | throw s!"missing dependency declaration: {name}"
      closure env ((dependencies ci).toList ++ rest) (seen.insert name)

private def declarationJson (env : Environment) (name : Name) : CommandElabM Json := do
  let some ci := env.find? name | throwError "missing declaration {name}"
  let axs ← collectAxioms name
  let statement ← liftTermElabM <| do
    return (← ppExpr ci.type).pretty
  return Json.mkObj [
    ("name", toJson name.toString), ("module", toJson (definingModule env name).toString),
    ("kind", toJson (kind ci)), ("statement", toJson statement),
    ("dependencies", namesJson (dependencies ci)), ("axioms", namesJson axs),
    ("standard_axioms", namesJson (axs.filter fun n =>
      n == `propext || n == `Classical.choice || n == `Quot.sound)),
    ("nonstandard_axioms", namesJson (axs.filter fun n =>
      !(n == `propext || n == `Classical.choice || n == `Quot.sound)))]

syntax (name := environmentAudit) "#environment_audit" "prefixes" "[" ident,* "]"
  "modules" "[" ident,* "]" "headlines" "[" ident,* "]" : command

@[command_elab environmentAudit]
def elabEnvironmentAudit : CommandElab := fun stx => do
    let env := (← getEnv).setExporting false
    let ps := stx[3].getSepArgs.map (·.getId)
    let ms := stx[7].getSepArgs.map (·.getId)
    let hs ← stx[11].getSepArgs.mapM fun id =>
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    if ps.isEmpty && ms.isEmpty then throwError "audit scope must not be empty"
    for m in ms do
      if (env.getModuleIdx? m).isNone then throwError "audit module is not imported: {m}"
    for h in hs do
      if (env.find? h).isNone then throwError "headline is not imported: {h}"
    let selected := env.constants.fold (init := #[]) fun acc n ci =>
      if definingModule env n != `ResearchAudit.EnvironmentAudit &&
          !(`ResearchAudit.EnvironmentAudit).isPrefixOf n &&
          (ps.any (fun p => p.isPrefixOf n || p.isPrefixOf (definingModule env n)) ||
            ms.contains (definingModule env n)) then
        acc.push (n, ci)
      else acc
    let selected := selected.qsort fun a b => Name.lt a.1 b.1
    let theoremNames := selected.filterMap fun (n, ci) =>
      if ci matches .thmInfo _ then some n else none
    let declarations ← selected.mapM fun (n, _) => declarationJson env n
    let mut headlineRecords := #[]
    for h in hs do
      let reachable ← match closure env [h] with
        | .ok seen => pure (seen.toArray.qsort Name.lt)
        | .error msg => throwError "{msg}"
      headlineRecords := headlineRecords.push <| Json.mkObj [
        ("name", toJson h.toString), ("closure", namesJson reachable),
        ("declarations", toJson (← reachable.mapM (declarationJson env)))]
    -- Fail the compiler command if ANY selected declaration or headline has an
    -- unexpected axiom. A caller must still verify exit status and JSON framing.
    for n in (selected.map (·.1)) ++ hs do
      let axs ← collectAxioms n
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "unexpected axiom {ax} in {n}"
    let report := Json.mkObj [
      ("schema_version", toJson (1 : Nat)), ("method", toJson "compiled Lean environment"),
      ("prefixes", namesJson ps), ("modules", namesJson ms),
      ("imported_modules", namesJson (env.header.modules.map (·.module))),
      ("declaration_count", toJson selected.size),
      ("theorem_count", toJson theoremNames.size), ("theorem_names", namesJson theoremNames),
      ("declarations", toJson declarations), ("headlines", toJson headlineRecords)]
    liftIO <| IO.println report.compress
end ResearchAudit.EnvironmentAudit
