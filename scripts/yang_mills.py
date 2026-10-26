#!/usr/bin/env python3
"""Run the pinned Yang–Mills specification and proof-admission checks.

The embedded project has its own Lean toolchain. Its checks do not validate
the legacy Problems.YangMills sketch or establish a Millennium Prize solution.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "verification" / "yang-mills"
MANIFEST = ROOT / "verification" / "yang-mills-source.json"


def check_snapshot() -> dict:
    """Require the reviewed source snapshot, including its verifier, unchanged."""
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    for name, expected in manifest["files"].items():
        path = PROJECT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f"Imported Yang–Mills source differs from snapshot: {name}")
    # Build artifacts and Python bytecode are deliberately outside the snapshot.
    actual = set()
    for directory, subdirs, files in os.walk(PROJECT):
        subdirs[:] = [name for name in subdirs if name not in {".lake", "__pycache__"}]
        actual.update(str((Path(directory) / name).relative_to(PROJECT)) for name in files)
    extra = actual - set(manifest["files"])
    if extra:
        raise ValueError(f"Unrecorded files in Yang–Mills snapshot: {', '.join(sorted(extra))}")
    return manifest


def run(script: str, *args: str) -> int:
    # cwd selects the nested lean-toolchain, not the root project's version.
    return subprocess.run(
        [sys.executable, str(PROJECT / "scripts" / script), *args], cwd=PROJECT
    ).returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("integrity", help="Check the imported source hashes")
    check = commands.add_parser("check", help="Build, run regressions, and check specification readiness")
    check.add_argument("--report", type=Path, help="Write the specification JSON report")
    verify = commands.add_parser("verify", help="Inspect the specification or a future submitted proof")
    verify.add_argument("--claim", choices=["specification", "yangmills", "qft", "clay"],
                        default="specification")
    verify.add_argument("--proof-file", type=Path)
    verify.add_argument("--theorem")
    verify.add_argument("--report", type=Path)
    args = parser.parse_args()
    try:
        snapshot = check_snapshot()
        if args.command == "integrity":
            print(f"Yang–Mills snapshot verified: {snapshot['commit']}")
            return 0
        if args.command == "check":
            result = run("check_proofs.py")
            if result:
                return result
        forwarded = ["--claim", getattr(args, "claim", "specification")]
        for flag in ("proof_file", "theorem", "report"):
            value = getattr(args, flag, None)
            if value is not None:
                # User paths are relative to the caller, not the nested project.
                forwarded.extend(["--" + flag.replace("_", "-"),
                                  str(value.resolve()) if isinstance(value, Path) else value])
        return run("verify_submission.py", *forwarded)
    except (OSError, ValueError, KeyError) as exc:
        print(f"Yang–Mills verification setup failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
