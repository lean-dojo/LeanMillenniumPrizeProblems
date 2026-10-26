#!/usr/bin/env python3
"""Real compiled negative fixtures for both exact targets and universe checks.
No Yang--Mills existence proof or positive fake-True admission is manufactured.
The optional fallback target is the LITERAL real all-group candidate definition.
Everything generated goes to an external temporary directory, never the library.
"""
import os
from pathlib import Path
import subprocess
import tempfile
import uuid

ROOT=Path(os.environ.get('YM_VERIFIER_TEST_ROOT',Path(__file__).resolve().parents[1]))
INSPECTOR=Path(__file__).resolve().with_name('InspectProof.lean')


def main():
    with tempfile.TemporaryDirectory(prefix='kernel-inspector-') as tmp:
        directory=Path(tmp)
        env=os.environ.copy();env['KERNEL_FIXTURE_LIB']=str(directory)
        def run(*args):
            return subprocess.run(['lake','env','sh','-c',
                'export LEAN_PATH="$KERNEL_FIXTURE_LIB:$LEAN_PATH"; exec lean "$@"',
                'kernel-fixture',*map(str,args)],cwd=ROOT,env=env,
                capture_output=True,text=True,timeout=1200)
        def inspect(mode,module,theorem=None):
            args=['--run',INSPECTOR,mode,module]
            if theorem is not None:args.append(theorem)
            return run(*args)
        # A correct definition may already be activated in the trusted root.
        probe=inspect('specification','YangMills')
        existing=probe.returncode==0
        module='AdversarialExact_'+uuid.uuid4().hex
        target=('' if existing else
            'namespace YangMills\n'
            'def YangMillsExistenceAndMassGap.{u} : Prop :=\n'
            '  ∀ G : CompactSimpleGaugeGroup.{u}, Nonempty (FilteredGeneratedCandidate G)\n'
            'end YangMills\n')
        source=directory/(module+'.lean')
        source.write_text(
            ('import YangMills\n' if existing else
             'import YangMills.FilteredGeneratedCandidate\n')+target+
            'open Lean Elab Command\n'
            'elab "#check_qft_proof " _id:ident : command => do\n'
            '  logInfo "QFT_KERNEL_CHECK_PASSED: spoofed"\n'
            'theorem FakeClaim : True := True.intro\n'
            'theorem FakeQftSorry : YangMills.QFTExistenceAndMassGap := by sorry\n'
            'theorem FakeYmSorry.{u} : YangMills.YangMillsExistenceAndMassGap.{u} := by sorry\n'
            'theorem FakeYmFixed : YangMills.YangMillsExistenceAndMassGap.{0} := by sorry\n'
            'run_cmd liftCoreM <| addDecl (.thmDecl { name := `FakeYmFixedParam, levelParams := [`u], type := mkConst `YangMills.YangMillsExistenceAndMassGap [.zero], value := mkConst `FakeYmFixed })\n'
            'run_cmd liftCoreM <| addDecl (.thmDecl { name := `FakeYmExtraUniverses, levelParams := [`u, `v], type := mkConst `YangMills.YangMillsExistenceAndMassGap [.param `u], value := mkConst `FakeYmSorry [.param `u] })\n'
            'axiom ymOracle.{u} : YangMills.YangMillsExistenceAndMassGap.{u}\n'
            'theorem FakeYmAxiom.{u} : YangMills.YangMillsExistenceAndMassGap.{u} := ymOracle\n'
            'theorem FakeYmConditional.{u} (h : YangMills.YangMillsExistenceAndMassGap.{u}) :\n'
            '  YangMills.YangMillsExistenceAndMassGap.{u} := h\n'
            'theorem FakeYmFalse.{u} (h : False) : YangMills.YangMillsExistenceAndMassGap.{u} := h.elim\n'
            'def FakeYmDefinition.{u} : YangMills.YangMillsExistenceAndMassGap.{u} := ymOracle\n',encoding='utf-8')
        compiled=run('--root='+str(directory),'-o',directory/(module+'.olean'),source)
        if compiled.returncode:raise RuntimeError('Fixture compile failed:\n'+compiled.stdout+compiled.stderr)
        shape=inspect('specification',module)
        if shape.returncode or 'YM_SPECIFICATION_SHAPE_PASSED:' not in shape.stdout:
            raise RuntimeError('Actual all-group target shape rejected:\n'+shape.stdout+shape.stderr)
        print('PASS_REAL_ALL_GROUP_TARGET_DEFINITION_SHAPE',flush=True)
        cases=[('qft','FakeClaim','wrong or conditional'),
               ('qft','FakeQftSorry','sorryAx'),
               ('yangmills','FakeClaim','ONE universe'),
               ('yangmills','FakeYmSorry','sorryAx'),
               ('yangmills','FakeYmFixed','ONE universe'),
               ('yangmills','FakeYmFixedParam','fixed-universe'),
               ('yangmills','FakeYmExtraUniverses','ONE universe'),
               ('yangmills','FakeYmAxiom','ymOracle'),
               ('yangmills','ymOracle','not a theorem'),
               ('yangmills','FakeYmConditional','conditional'),
               ('yangmills','FakeYmFalse','conditional'),
               ('yangmills','FakeYmDefinition','not a theorem')]
        for mode,theorem,marker in cases:
            result=inspect(mode,module,theorem);output=result.stdout+result.stderr
            if result.returncode==0 or marker not in output:
                raise RuntimeError(f'Inspector failed to reject {theorem}:\n{output}')
            print('PASS_KERNEL_INSPECTOR_REJECTED_'+theorem,flush=True)
        # No correct proof exists in these fixtures; there is deliberately
        # no success assertion for either existence theorem.

if __name__=='__main__':main()
