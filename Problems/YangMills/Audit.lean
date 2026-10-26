import Lean
import Problems.YangMills.Statement
import Problems.YangMills.YangMillsSpecification

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Audit submitted proofs

Ordinary Lean allows `sorry`, or a theorem proved using a newly declared axiom.
These commands reject both, transitively. The only permitted foundational axioms
are Lean's usual `propext`, `Classical.choice`, and `Quot.sound`.

`#audit_axioms declaration` audits dependencies; it does not check a target.
`#check_qft_proof declaration` additionally requires exactly the closed
`QFTExistenceAndMassGap` proposition. A conditional theorem cannot pass it.
These QFT-only commands do not verify the full Yang--Mills target; the
separate exact-target command below does. Neither asserts external acceptance.
-/

open Lean Elab Command Meta

private def auditDeclaration (name : Name) : CommandElabM Unit := do
  let axioms ← Lean.collectAxioms name
  let unexpected := axioms.filter fun n =>
    n != ``propext && n != ``Classical.choice && n != ``Quot.sound
  unless unexpected.isEmpty do
    throwError "Proof audit rejected {name}: unapproved axioms {unexpected.toList}"
  logInfo m!"Axiom audit passed for {name}."

elab "#audit_axioms " id:ident : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  for name in names do
    auditDeclaration name

elab "#check_qft_proof " id:ident : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  unless names.length == 1 do
    throwError "Expected one unambiguous declaration."
  let name := names[0]!
  liftTermElabM do
    let info ← getConstInfo name
    unless ← isDefEq info.type (mkConst ``YangMills.QFTExistenceAndMassGap) do
      throwError "Wrong target: expected exactly YangMills.QFTExistenceAndMassGap, without extra hypotheses."
  auditDeclaration name
  logInfo "QFT-and-gap target checked. This is not a certification of Yang–Mills."

/-! Exact Yang--Mills kernel admission is separate from external/CMI acceptance.
The explicit trusted switch records the completed definition review; it does not supply an existence proof or external acceptance. -/
private def yangMillsAdmissionReviewed : Bool := true

private def checkYangMillsDeclaration (candidate : Syntax) : CommandElabM Unit := do
  unless yangMillsAdmissionReviewed do
    throwError "CLAY_CERTIFICATION_BLOCKED: reviewed-target admission is not activated."
  let names ← liftCoreM <| realizeGlobalConstWithInfos candidate
  unless names.length == 1 do throwError "Expected one unambiguous declaration."
  let name := names[0]!
  let info ← liftCoreM <| getConstInfo name
  let .thmInfo proofInfo := info
    | throwError "Proof audit rejected: submitted declaration is not a theorem."
  let [u] := proofInfo.levelParams
    | throwError "Wrong target: Yang--Mills theorem must have ONE universe parameter."
  unless proofInfo.type == mkConst `YangMills.YangMillsExistenceAndMassGap [.param u] do
    throwError "Wrong target: expected exact universe-polymorphic YangMillsExistenceAndMassGap, without fixed universes or hypotheses."
  auditDeclaration name
  logInfo "YM_KERNEL_CHECK_PASSED: exact declared Yang--Mills target; external acceptance not assessed; not a Clay certificate."

elab "#check_yang_mills_proof " candidate:ident : command =>
  checkYangMillsDeclaration candidate

/-- Compatibility command name; output is a mathematical kernel result only. -/
elab "#check_clay_proof " candidate:ident : command =>
  checkYangMillsDeclaration candidate

elab "#clay_certification_status" : command => do
  if yangMillsAdmissionReviewed then
    logInfo "YM_SPECIFICATION_READY: reviewed fixed target defined; existence proof not submitted by this command; kernel proof verification not run; external acceptance not assessed; no Clay certificate."
  else
    logInfo "CLAY_CERTIFICATION_BLOCKED: reviewed-target admission is not activated."
