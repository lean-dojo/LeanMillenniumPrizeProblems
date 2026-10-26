#!/usr/bin/env python3
"""Fail-closed submission checker anchored to the exact Jaffe–Witten PDF.

Exit 0: reviewed specification ready, or exact declared-target kernel proof accepted.
Never an assertion of external acceptance or a Clay certificate.
Exit 1: invalid source, proof, or verification infrastructure.
Exit 2: specification incomplete or a reviewed-target proof was not submitted.

This is a mathematical proof checker, not a security sandbox for hostile Lean code.
Run on a trusted checkout/toolchain and have referees review the specification.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import secrets
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PDF_RELATIVE = "source/yangmills.pdf"
PDF_SHA256 = "3558403ca14c11e382f73a09e548222708540bfdf478cf96aa11c52d43e23e09"
PDF_BLOB_SHA1 = "2647452ed43c68632d786a9667e61e6f5e8a8e74"
MANIFEST = "source/requirements.json"
CLAUSE_IDS = frozenset({
    "group", "spacetime", "qft-axioms", "ym-identification",
    "gauge-observables", "renormalized-filtration", "ultraviolet",
    "stress-tensor", "ope", "nontrivial", "physical-gap",
    "universal-existence",
})
# Only these source-derived clauses affect the prospective Clay proof target.
# Section 4 footnote 1 is explicitly framed as an expectation; the particular
# dimension-filtration implementation is interpretive guidance, not an
# additional mandatory existence theorem. Roles are fixed here: changing the
# user-editable inventory cannot silently promote a strategy into a requirement.
NORMATIVE_SOURCE_BASIS = {
    "group": "section_4_theorem",
    "spacetime": "section_4_theorem",
    "qft-axioms": "section_4_theorem",
    "ym-identification": "section_4_explanation",
    "gauge-observables": "section_4_explanation",
    "ultraviolet": "section_4_explanation",
    "stress-tensor": "section_4_predictions",
    "ope": "section_4_predictions",
    "nontrivial": "section_4_theorem",
    "physical-gap": "section_4_mass_definition",
    "universal-existence": "section_4_theorem",
}
INTERPRETIVE_SOURCE_BASIS = {
    "renormalized-filtration": "section_4_footnote_1",
}
# Provenance is separate from *acceptance role*: an explicitly required
# phrase can still need mathematical interpretation before it becomes Lean.
# These are provenance classifications, never assumed physics propositions.
FORMALIZATION_LAYER = {
    "group": "literal_form",
    "spacetime": "literal_form",
    "qft-axioms": "cited_framework",
    "ym-identification": "interpretation_needed",
    "gauge-observables": "interpretation_needed",
    "renormalized-filtration": "nonbinding_guidance",
    "ultraviolet": "interpretation_needed",
    "stress-tensor": "interpretation_needed",
    "ope": "interpretation_needed",
    "nontrivial": "interpretation_needed",
    "physical-gap": "literal_form",
    "universal-existence": "literal_form",
}
# Trusted activation switch: root may change ONLY after final fixed-target review.
# Coverage metadata, proof text, and CLI arguments cannot enable this switch.
YM_ADMISSION_REVIEWED = True
YM_TARGET = "YangMills.YangMillsExistenceAndMassGap"

VALID_STATES = {"formalized", "partial", "missing"}
THEOREM_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")


class SpecificationError(ValueError):
    pass


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_inventory(root: Path) -> dict:
    """Check source identity and enforce a complete, non-duplicated clause inventory.

    A coverage annotation is NOT a proof of semantic fidelity. This does not
    unlock Clay verification, even if every annotation says "formalized".
    """
    manifest = json.loads((root / MANIFEST).read_text(encoding="utf-8"))
    if manifest.get("schema_version") != 3:
        raise SpecificationError("Unsupported requirements inventory version")
    source = manifest.get("source")
    if not isinstance(source, dict):
        raise SpecificationError("Missing canonical source declaration")
    for key, fixed in (
        ("path", PDF_RELATIVE),
        ("sha256", PDF_SHA256),
        ("git_blob_sha1", PDF_BLOB_SHA1),
        ("section", "4. The Problem"),
        ("printed_page", 6),
    ):
        if source.get(key) != fixed:
            raise SpecificationError(f"Source contract changed: {key}")
    pdf = root / PDF_RELATIVE
    if not pdf.is_file() or sha256(pdf) != PDF_SHA256:
        raise SpecificationError("source/yangmills.pdf does not match pinned Jaffe–Witten PDF")
    entries = manifest.get("requirements")
    if not isinstance(entries, list):
        raise SpecificationError("Missing paper-clause inventory")
    ids = [x.get("id") for x in entries if isinstance(x, dict)]
    if len(ids) != len(entries) or len(ids) != len(set(ids)) or set(ids) != CLAUSE_IDS:
        raise SpecificationError("Paper-clause inventory is incomplete, altered, or duplicated")
    if set(NORMATIVE_SOURCE_BASIS) | set(INTERPRETIVE_SOURCE_BASIS) != CLAUSE_IDS:
        raise SpecificationError("Verifier source-role contract no longer matches clause IDs")
    for entry in entries:
        key = entry["id"]
        expected_role, expected_basis = (
            ("required", NORMATIVE_SOURCE_BASIS[key])
            if key in NORMATIVE_SOURCE_BASIS else
            ("interpretive_guidance", INTERPRETIVE_SOURCE_BASIS[key])
        )
        if (entry.get("acceptance_role") != expected_role
                or entry.get("source_basis") != expected_basis):
            raise SpecificationError(
                f"Non-source assumption or changed acceptance scope for {key}")
        if entry.get("formalization_layer") != FORMALIZATION_LAYER[key]:
            raise SpecificationError(
                f"Changed PDF/Lean provenance classification for {key}")
        if not isinstance(entry.get("formalization_note"), str):
            raise SpecificationError(
                f"Missing explanation of formalization boundary for {key}")
        if entry.get("status") not in VALID_STATES:
            raise SpecificationError(f"Unknown coverage status for {entry['id']}")
        if not all(isinstance(entry.get(k), str) and entry[k].strip()
                   for k in ("description", "location", "gap")):
            raise SpecificationError(f"Missing provenance or gap for {entry['id']}")
        if not isinstance(entry.get("lean"), list):
            raise SpecificationError(f"Invalid declaration references for {entry['id']}")
    return manifest


def _run(args: list[str], root: Path, timeout: int = 1200) -> subprocess.CompletedProcess:
    return subprocess.run(args, cwd=root, capture_output=True, text=True,
                          timeout=timeout, check=False)



FINGERPRINTED_FILES = (
    "YangMills/Statement.lean",
    "YangMills/GaugeGroup.lean",
    "YangMills/PDFLiteral.lean",
    "YangMills/SourceClassification.lean",
    "YangMills/GaugeHolonomy.lean",
    "YangMills/LatticeGaugeAction.lean",
    "YangMills/PeriodicLattice4.lean",
    "YangMills/GroupwiseNecessary.lean",
    "YangMills/LocalObservables.lean",
    "YangMills/QuantumCorrelations.lean",
    "YangMills/InvariantJetPolynomials.lean",
    "YangMills/Ultraviolet.lean",
    "YangMills/CompositeFields.lean",
    "YangMills/StressTensor.lean",
    "YangMills/PerturbativeYangMills.lean",
    "YangMills/Renormalization.lean",
    "YangMills/OperatorProductExpansion.lean",
    "YangMills/WickRotation.lean",
    "YangMills/RenormalizationGroup.lean",
    "YangMills/Nontriviality.lean",
    "YangMills/Classical.lean",
    "YangMills/QFT/Spacetime.lean",
    "YangMills/QFT/Wightman.lean",
    "YangMills/QFT/Operator.lean",
    "YangMills/Spectrum.lean",
    "YangMills/Audit.lean",
    "YangMills/Verification.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "scripts/InspectProof.lean",
    "scripts/verify_submission.py",
    "source/SPECIFICATION_REVIEW.md",
    "source/SOURCE_ANALYSIS.md",
    "source/QFT_REVIEW.md",
    "source/YANG_MILLS_REVIEW.md",
    "source/ADVERSARIAL_REVIEW.md",
    "source/PERTURBATIVE_PRESCRIPTION.md",
    "source/COMPOSITE_STRESS_REVIEW.md",
    "source/PERTURBATIVE_IMPLEMENTATION.md",
    "source/CENTRAL_ADVERSARIAL_REVIEW.md",
    MANIFEST,
)


def provenance(root: Path) -> dict:
    """Reproducibility metadata; fingerprints do not certify semantics."""
    result = {
        "local_fingerprints_sha256": {
            path: sha256(root / path)
            for path in sorted(set(FINGERPRINTED_FILES) |
                {str(p.relative_to(root)) for p in (root / "YangMills").rglob("*.lean")} |
                {str(p.relative_to(root)) for p in (root / "source").glob("*.md")} |
                {str(p.relative_to(root)) for p in (root / "scripts").glob("*.py")})
            if (root / path).is_file()
        }
    }
    version = root / "lean-toolchain"
    if version.is_file():
        result["pinned_lean_toolchain"] = version.read_text(encoding="utf-8").strip()
    if (root / ".git").exists():
        try:
            commit = _run(["git", "rev-parse", "HEAD"], root, timeout=10)
            if commit.returncode == 0:
                result["git_commit"] = commit.stdout.strip()
            dirty = _run(["git", "status", "--porcelain"], root, timeout=10)
            result["git_worktree_dirty"] = dirty.returncode != 0 or bool(dirty.stdout.strip())
        except (OSError, subprocess.TimeoutExpired):
            result["git_commit"] = None
            result["git_worktree_dirty"] = None
    return result

def verify(root: Path, claim: str, proof_file: Path | None = None,
           theorem: str | None = None) -> tuple[dict, int]:
    report = {
        "source": PDF_RELATIVE,
        "expected_pdf_sha256": PDF_SHA256,
        "claim": claim,
        "status": "INVALID_SPECIFICATION",
        "clay_certificate": False,
        "qft_only_certificate": False,
        "yang_mills_kernel_certificate": False,
        "specification_shape_status": "not_run",
        # These are fixed verifier judgments, never inferred from coverage labels.
        "specification_readiness": "incomplete",
        "full_target_defined": False,
        "existence_proof_required_for_specification": False,
        "proof_submission_status": "submitted" if proof_file is not None else "not_submitted",
        "kernel_verification_status": "not_run",
        "semantic_review_status": "unresolved_findings",
        "external_acceptance_status": "not_assessed",
        "admitted_target": None,
    }
    try:
        inventory = load_inventory(root)
        report["pdf_hash_verified"] = True
        report["provenance"] = provenance(root)
        report["coverage"] = {e["id"]: e["status"] for e in inventory["requirements"]}
        report["formalization_layers"] = {
            e["id"]: e["formalization_layer"]
            for e in inventory["requirements"]
        }
        report["source_basis"] = {
            e["id"]: {"role": e["acceptance_role"], "basis": e["source_basis"]}
            for e in inventory["requirements"]
        }
        report["incomplete_clauses"] = sorted(
            e["id"] for e in inventory["requirements"]
            if e["acceptance_role"] == "required" and e["status"] != "formalized")
        report["interpretive_guidance"] = sorted(
            e["id"] for e in inventory["requirements"]
            if e["acceptance_role"] == "interpretive_guidance")
    except (OSError, ValueError, KeyError, TypeError) as exc:
        report["pdf_hash_verified"] = False
        report["error"] = f"{type(exc).__name__}: {exc}"
        return report, 1

    if claim == "qft":
        # QFT proof checking does not inspect the full YM definition or its
        # semantic admission. Do not turn a mode-local omission into a false
        # assertion that the globally reviewed specification is incomplete.
        report.update(specification_readiness="not_assessed_in_qft_mode",
                      full_target_defined=None,
                      semantic_review_status="not_assessed_in_qft_mode")
    ym_claim = claim in {"clay", "yangmills"}
    if claim not in {"clay", "yangmills", "specification", "qft"}:
        report["error"] = f"Unknown claim: {claim}"
        return report, 1
    built_already = False
    if ym_claim or claim == "specification":
        if not YM_ADMISSION_REVIEWED or report["incomplete_clauses"]:
            report["status"] = ("SPECIFICATION_INCOMPLETE" if claim == "specification"
                                else "CLAY_CERTIFICATION_BLOCKED")
            if proof_file is not None:
                report["proof_submission_status"] = "not_evaluated_specification_incomplete"
            report["reason"] = (
                "The trusted reviewed-target activation is disabled or required coverage "
                "is incomplete. Coverage labels alone cannot activate admission. "
                "Existence proofs are not specification-readiness requirements.")
            return report, 2
        try:
            built = _run(["lake", "build"], root)
            report["build_exit_code"] = built.returncode
            if built.returncode:
                report["status"] = "BUILD_FAILED"
                report["error"] = (built.stdout + built.stderr)[-4000:]
                return report, 1
            built_already = True
            shape = _run(["lake", "env", "lean", "--run",
                          str(root / "scripts" / "InspectProof.lean"),
                          "specification", "YangMills"], root)
            report["specification_shape_output_tail"] = (shape.stdout + shape.stderr)[-3000:]
            if shape.returncode or "YM_SPECIFICATION_SHAPE_PASSED:" not in shape.stdout:
                report["status"] = "INVALID_SPECIFICATION"
                report["specification_shape_status"] = "rejected"
                report["error"] = "Compiled exact all-group universe-polymorphic target check failed"
                return report, 1
        except (OSError, subprocess.TimeoutExpired) as exc:
            report["status"] = "VERIFIER_ERROR"
            report["error"] = f"{type(exc).__name__}: {exc}"
            return report, 1
        report.update(specification_readiness="ready", full_target_defined=True,
                      semantic_review_status="reviewed_fixed_specification",
                      specification_shape_status="passed", admitted_target=YM_TARGET)
        if claim == "specification":
            if proof_file is not None:
                report["proof_submission_status"] = "not_evaluated_specification_only"
            report["status"] = "SPECIFICATION_READY"
            report["reason"] = "Reviewed fixed target is defined; no existence proof was requested or verified"
            return report, 0
        if proof_file is None and theorem is None:
            report["status"] = "PROOF_NOT_SUBMITTED"
            report["reason"] = "Specification ready; no existence proof submitted; kernel verification not run"
            return report, 2
    if proof_file is None or theorem is None or not THEOREM_NAME.fullmatch(theorem):
        report.update(status="INVALID_PROOF_SUBMISSION",
                      proof_submission_status="invalid_arguments")
        report["error"] = "Kernel admission requires --proof-file and a simple qualified --theorem name"
        return report, 1
    if proof_file.suffix != ".lean" or not proof_file.is_file():
        report.update(status="INVALID_PROOF_SUBMISSION",
                      proof_submission_status="invalid_arguments")
        report["error"] = "A readable .lean proof-file is required"
        return report, 1
    try:
        program = proof_file.read_text(encoding="utf-8")
        report["proof_sha256"] = sha256(proof_file)
    except (OSError, UnicodeError) as exc:
        report.update(status="INVALID_PROOF_SUBMISSION",
                      proof_submission_status="invalid_arguments")
        report["error"] = f"Unreadable UTF-8 proof source: {type(exc).__name__}: {exc}"
        return report, 1
    try:
        (root / ".lake").mkdir(exist_ok=True)
        built = (subprocess.CompletedProcess(["lake", "build"], 0, "", "")
                 if built_already else _run(["lake", "build"], root))
        report["build_exit_code"] = built.returncode
        if built.returncode:
            report["status"] = "BUILD_FAILED"
            report["error"] = (built.stdout + built.stderr)[-4000:]
            return report, 1
        # Audit is appended by the trusted verifier, not chosen by the submitter.
        # A proof source must compile as a self-contained Lean file when imported
        # from the project root (local imports must be available there).
        with tempfile.TemporaryDirectory(prefix="verify-kernel-", dir=root / ".lake") as temp:
            # Compile untrusted proof separately. Do NOT append a textual audit
            # command: the submission could redefine its syntax and spoof output.
            name = "KernelCandidate_" + secrets.token_hex(12)
            source_path = Path(temp) / (name + ".lean")
            source_path.write_text("import YangMills\n" + program + "\n", encoding="utf-8")
            olean = root / ".lake" / "build" / "lib" / "lean" / (name + ".olean")
            olean.parent.mkdir(parents=True, exist_ok=True)
            try:
                compiled = _run(["lake", "env", "lean", "-o", str(olean),
                                 str(source_path)], root)
                report["proof_compile_exit_code"] = compiled.returncode
                if compiled.returncode != 0:
                    report["status"] = "PROOF_REJECTED"
                    report["kernel_verification_status"] = "compilation_failed"
                    report["proof_submission_status"] = "rejected"
                    report["error"] = "Proof source failed to compile"
                    report["proof_compile_output_tail"] = (
                        compiled.stdout + compiled.stderr)[-3000:]
                    return report, 1
                # Auditing uses a trusted Lean program compiled independently
                # of the candidate. It imports the candidate .olean dynamically
                # and reads the checked kernel environment, with no submitted
                # macros or user-defined audit syntax in the verifier source.
                inspected = _run([
                    "lake", "env", "lean", "--run",
                    str(root / "scripts" / "InspectProof.lean"),
                    "yangmills" if ym_claim else "qft", name, theorem,
                ], root)
                report["kernel_audit_exit_code"] = inspected.returncode
                report["kernel_verification_status"] = "rejected"
                report["kernel_audit_output_tail"] = (
                    inspected.stdout + inspected.stderr)[-3000:]
                if (inspected.returncode == 0 and
                        ("YM_KERNEL_CHECK_PASSED:" if ym_claim else "QFT_KERNEL_CHECK_PASSED:")
                        in inspected.stdout):
                    if ym_claim:
                        report.update(status="YANG_MILLS_KERNEL_PROOF_ACCEPTED",
                                      admitted_target=YM_TARGET, yang_mills_kernel_certificate=True,
                                      kernel_verification_status="passed_declared_yang_mills_target",
                                      proof_submission_status="accepted_declared_yang_mills_target",
                                      verified_theorem=theorem)
                        report["reason"] = ("Exact reviewed universe-polymorphic target and approved "
                                            "transitive axioms; external acceptance not assessed; "
                                            "this report is not a Clay certificate")
                        return report, 0
                    report["status"] = "QFT_ONLY_PROOF_ACCEPTED"
                    report["admitted_target"] = "YangMills.QFTExistenceAndMassGap"
                    report["qft_only_certificate"] = True
                    report["kernel_verification_status"] = "passed_declared_qft_target"
                    report["proof_submission_status"] = "accepted_declared_qft_target"
                    report["verified_theorem"] = theorem
                    report["reason"] = "Exactly QFTExistenceAndMassGap, not the Yang–Mills Clay statement"
                    return report, 0
                report["status"] = "PROOF_REJECTED"
                report["proof_submission_status"] = "rejected"
                report["error"] = (
                    "Independent kernel-environment inspection rejected "
                    "the theorem type and/or transitive axioms")
                return report, 1
            finally:
                olean.unlink(missing_ok=True)
    except (OSError, UnicodeError, subprocess.TimeoutExpired) as exc:
        report["status"] = "VERIFIER_ERROR"
        report["error"] = f"{type(exc).__name__}: {exc}"
        return report, 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--claim", choices=["clay", "yangmills", "qft", "specification"], default="clay")
    parser.add_argument("--proof-file", type=Path,
                        help="Lean source file (necessary for kernel proof verification)")
    parser.add_argument("--theorem", type=str,
                        help="Fully qualified theorem name (necessary for kernel proof verification)")
    parser.add_argument("--report", type=Path,
                        help="Optional JSON report path (default: stdout only)")
    args = parser.parse_args()
    report, status = verify(ROOT, args.claim, args.proof_file, args.theorem)
    payload = json.dumps(report, sort_keys=True, indent=2, ensure_ascii=True) + "\n"
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(payload, encoding="utf-8")
    sys.stdout.write(payload)
    return status


if __name__ == "__main__":
    raise SystemExit(main())
