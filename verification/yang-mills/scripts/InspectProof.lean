import Lean

/-! Trusted checked-environment inspector. Never evaluate submitted audit syntax.
Modes: qft Module Theorem; yangmills Module Theorem; specification Module.
Legacy two-argument invocation is QFT-only. Kernel verification is distinct
from external acceptance and never supplies a Clay certificate. -/
open Lean

private def dottedName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => Name.str n c) Name.anonymous

private def isAllowedAxiom (n : Name) : Bool :=
  n == dottedName "propext" || n == dottedName "Classical.choice" ||
  n == dottedName "Quot.sound"

private def ymTarget := dottedName "YangMills.YangMillsExistenceAndMassGap"
private def qftTarget := dottedName "YangMills.QFTExistenceAndMassGap"

/-- Check the compiled definition, not editable coverage labels. -/
private def checkYMDefinition (env : Environment) : Except String Unit := do
  let some (.defnInfo info) := env.checked.get.find? ymTarget
    | throw "reviewed Yang--Mills target is absent or not a definition"
  let [u] := info.levelParams | throw "Yang--Mills target must have ONE universe parameter"
  unless info.type == mkSort .zero do throw "Yang--Mills target is not a closed Prop"
  let .forallE _ group body _ := info.value.consumeMData
    | throw "Yang--Mills target does not universally quantify the actual group"
  unless group == mkConst (dottedName "YangMills.CompactSimpleGaugeGroup") [.param u] do
    throw "Yang--Mills target uses the wrong group universe/type"
  let .app (.const nonempty [_]) candidate := body.consumeMData
    | throw "Yang--Mills target is not Nonempty of the fixed candidate"
  unless nonempty == dottedName "Nonempty" do throw "wrong existence wrapper"
  unless candidate == mkApp
      (mkConst (dottedName "YangMills.FilteredGeneratedCandidate") [.param u]) (.bvar 0) do
    throw "Yang--Mills target uses a different/conditional candidate or fixed universe"

private def inspect (mode moduleText theoremText : String) : IO UInt32 := do
  let env ← importModules #[{ module := dottedName moduleText }] {} 0
  if mode == "specification" then
    match checkYMDefinition env with
    | .error error => IO.eprintln s!"REJECTED: {error}"; return 1
    | .ok () =>
      IO.println "YM_SPECIFICATION_SHAPE_PASSED: exact one-universe all-group candidate definition"
      return 0
  unless mode == "qft" || mode == "yangmills" do
    IO.eprintln "REJECTED: unknown kernel inspection mode"
    return 1
  if mode == "yangmills" then
    match checkYMDefinition env with
    | .error error => IO.eprintln s!"REJECTED: {error}"; return 1
    | .ok () => pure ()
  let theoremName := dottedName theoremText
  match env.checked.get.find? theoremName with
  | none => IO.eprintln s!"REJECTED: theorem {theoremText} does not exist"; return 1
  | some (.thmInfo info) =>
    if mode == "qft" then
      unless info.type == mkConst qftTarget do
        IO.eprintln "REJECTED: proof has wrong or conditional target type"
        return 1
    else
      let [u] := info.levelParams
        | IO.eprintln "REJECTED: Yang--Mills proof must have ONE universe parameter"; return 1
      unless info.type == mkConst ymTarget [.param u] do
        IO.eprintln "REJECTED: proof has wrong, fixed-universe or conditional target type"
        return 1
    let (_, state) := ((CollectAxioms.collect theoremName).run env).run {}
    let extra := state.axioms.filter (fun ax => !isAllowedAxiom ax)
    unless extra.isEmpty do
      IO.eprintln s!"REJECTED: unapproved transitive axioms {extra.toList}"
      return 1
    if mode == "qft" then
      IO.println s!"QFT_KERNEL_CHECK_PASSED: {theoremText} has exact QFT-only type and no unapproved axioms"
    else
      IO.println s!"YM_KERNEL_CHECK_PASSED: {theoremText} has exact universe-polymorphic Yang--Mills type and no unapproved axioms; external acceptance not assessed"
    return 0
  | some _ => IO.eprintln "REJECTED: submitted declaration is not a theorem"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["specification", moduleText] => inspect "specification" moduleText ""
  | [mode, moduleText, theoremText] => inspect mode moduleText theoremText
  | [moduleText, theoremText] => inspect "qft" moduleText theoremText
  | _ =>
    IO.eprintln "Usage: InspectProof.lean (qft|yangmills) Module Theorem | specification Module"
    return 1
