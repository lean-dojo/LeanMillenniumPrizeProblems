"""Integration regressions; mathematical admission tests live in the snapshot."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import yang_mills as runner


class IntegrationTests(unittest.TestCase):
    def test_snapshot_rejects_drift_and_extra_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            project = root / "project"
            project.mkdir()
            source = project / "Target.lean"
            source.write_text("def target : Prop := True\n")
            manifest = root / "source.json"
            manifest.write_text(json.dumps({"files": {
                "Target.lean": hashlib.sha256(source.read_bytes()).hexdigest()
            }}))
            with patch.object(runner, "PROJECT", project), patch.object(runner, "MANIFEST", manifest):
                runner.check_snapshot()
                (project / ".lake").mkdir()
                (project / ".lake" / "build-artifact").write_text("ignored")
                runner.check_snapshot()
                source.write_text("def target : Prop := False\n")
                with self.assertRaisesRegex(ValueError, "differs from snapshot"):
                    runner.check_snapshot()
                source.write_text("def target : Prop := True\n")
                (project / "Extra.lean").write_text("axiom extra : False\n")
                with self.assertRaisesRegex(ValueError, "Unrecorded files"):
                    runner.check_snapshot()
                (project / "Extra.lean").unlink()
                source.unlink()
                with self.assertRaisesRegex(ValueError, "differs from snapshot"):
                    runner.check_snapshot()

    def test_proof_paths_and_missing_proof_exit_code(self):
        with patch.object(runner, "check_snapshot", return_value={}), \
             patch.object(runner, "run", return_value=2) as run, \
             patch("sys.argv", ["yang_mills.py", "verify", "--claim", "yangmills",
                                "--proof-file", "Proof.lean", "--theorem", "Example.proof",
                                "--report", "report.json"]):
            self.assertEqual(runner.main(), 2)
            run.assert_called_once_with(
                "verify_submission.py", "--claim", "yangmills",
                "--proof-file", str(Path("Proof.lean").resolve()),
                "--theorem", "Example.proof", "--report", str(Path("report.json").resolve()))

    def test_failed_regressions_prevent_readiness_check(self):
        with patch.object(runner, "check_snapshot", return_value={}), \
             patch.object(runner, "run", return_value=1) as run, \
             patch("sys.argv", ["yang_mills.py", "check"]):
            self.assertEqual(runner.main(), 1)
            run.assert_called_once_with("check_proofs.py")

    def test_bad_snapshot_prevents_lean_execution(self):
        with patch.object(runner, "check_snapshot", side_effect=ValueError("changed")), \
             patch.object(runner, "run") as run, \
             patch("sys.argv", ["yang_mills.py", "check"]), \
             contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(runner.main(), 1)
            run.assert_not_called()

    def test_nested_project_selects_its_own_toolchain(self):
        with patch.object(runner.subprocess, "run") as execute:
            execute.return_value.returncode = 1
            self.assertEqual(runner.run("check_proofs.py"), 1)
            self.assertEqual(execute.call_args.kwargs["cwd"], runner.PROJECT)


if __name__ == "__main__":
    unittest.main()
