#!/usr/bin/env python3
"""Regression tests: source roles, trusted activation, and exact-target reports.
Mocked inspector results test runner plumbing only; they are NOT Lean proofs.
Real negative kernel fixtures are in test_kernel_inspector.py.
"""
from __future__ import annotations
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_submission as v
ROOT = Path(os.environ.get("YM_VERIFIER_TEST_ROOT", Path(__file__).resolve().parents[1]))

class SourceContractTests(unittest.TestCase):
    def inventory(self):
        return v.load_inventory(ROOT)

    def ready_inventory(self):
        record = copy.deepcopy(self.inventory())
        for row in record['requirements']:
            if row['acceptance_role'] == 'required': row['status'] = 'formalized'
        return record

    @staticmethod
    def cp(code=0, text=''):
        return subprocess.CompletedProcess(['fixture'], code, text, '')

    def run_ready(self, claim, proof_file=None, theorem=None, outputs=None, root=ROOT):
        responses = outputs or [self.cp(), self.cp(text='YM_SPECIFICATION_SHAPE_PASSED: fixture')]
        with patch.object(v, 'YM_ADMISSION_REVIEWED', True), \
             patch.object(v, 'load_inventory', return_value=self.ready_inventory()), \
             patch.object(v, 'provenance', return_value={}), \
             patch.object(v, '_run', side_effect=responses) as calls:
            report, rc = v.verify(root, claim, proof_file, theorem)
        return report, rc, calls

    @staticmethod
    def copy_source(root):
        (root/'source').mkdir()
        shutil.copy2(ROOT/v.PDF_RELATIVE, root/v.PDF_RELATIVE)
        shutil.copy2(ROOT/v.MANIFEST, root/v.MANIFEST)
        return root

    def tamper(self, change):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.copy_source(Path(tmp))
            manifest = json.loads((root/v.MANIFEST).read_text())
            change(manifest)
            (root/v.MANIFEST).write_text(json.dumps(manifest))
            return v.verify(root, 'clay')

    def test_pdf_pinned(self):
        self.assertEqual(self.inventory()['source']['sha256'],v.PDF_SHA256)
        self.assertEqual(len(self.inventory()['requirements']),len(v.CLAUSE_IDS))

    def test_provenance_git_state(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/'.git').mkdir()
            with patch.object(v,'_run',side_effect=[self.cp(text='abc\n'),self.cp(text=' M foo\n')]):
                p=v.provenance(root)
            self.assertEqual(p['git_commit'],'abc'); self.assertTrue(p['git_worktree_dirty'])

    def test_all_model_sources_fingerprinted(self):
        p=v.provenance(ROOT)['local_fingerprints_sha256']
        self.assertIn('YangMills/FilteredGeneratedCandidate.lean',p)
        self.assertIn('YangMills/FullBVActualNilpotency.lean',p)

    def test_footnote_guidance_not_requirement(self):
        rows={r['id']:r for r in self.inventory()['requirements']}
        self.assertEqual(rows['renormalized-filtration']['acceptance_role'],'interpretive_guidance')
        self.assertNotIn('renormalized-filtration',v.NORMATIVE_SOURCE_BASIS)

    def test_footnote_cannot_be_promoted(self):
        report,rc=self.tamper(lambda m:next(r for r in m['requirements'] if r['id']=='renormalized-filtration').update(acceptance_role='required'))
        self.assertEqual(rc,1); self.assertIn('acceptance scope',report['error'])

    def test_source_basis_cannot_change(self):
        report,rc=self.tamper(lambda m:next(r for r in m['requirements'] if r['id']=='physical-gap').update(source_basis='section_4_footnote_1'))
        self.assertEqual(rc,1); self.assertIn('acceptance scope',report['error'])

    def test_layer_cannot_be_relabelled(self):
        report,rc=self.tamper(lambda m:next(r for r in m['requirements'] if r['id']=='ym-identification').update(formalization_layer='literal_form'))
        self.assertEqual(rc,1); self.assertIn('provenance classification',report['error'])

    def test_group_literal_layer_preserved(self):
        report,rc=self.tamper(lambda m:next(r for r in m['requirements'] if r['id']=='group').update(formalization_layer='interpretation_needed'))
        self.assertEqual(rc,1); self.assertIn('provenance classification',report['error'])

    def test_missing_clause_rejected(self):
        report,rc=self.tamper(lambda m:m['requirements'].pop())
        self.assertEqual(rc,1); self.assertIn('incomplete',report['error'])

    def test_duplicate_clause_rejected(self):
        report,rc=self.tamper(lambda m:m['requirements'].append(m['requirements'][0]))
        self.assertEqual(rc,1); self.assertIn('duplicated',report['error'])

    def test_tampered_pdf_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=self.copy_source(Path(tmp))
            with (root/v.PDF_RELATIVE).open('ab') as f:f.write(b'changed')
            report,rc=v.verify(root,'specification')
        self.assertEqual(rc,1); self.assertFalse(report['pdf_hash_verified'])

    def test_status_labels_alone_cannot_activate(self):
        with patch.object(v,'load_inventory',return_value=self.ready_inventory()),patch.object(v,'YM_ADMISSION_REVIEWED',False):
            report,rc=v.verify(ROOT,'clay')
        self.assertEqual(rc,2); self.assertEqual(report['incomplete_clauses'],[])
        self.assertEqual(report['specification_readiness'],'incomplete'); self.assertFalse(report['clay_certificate'])

    def test_disabled_specification_needs_no_existence_proof(self):
        with patch.object(v,'YM_ADMISSION_REVIEWED',False): report,rc=v.verify(ROOT,'specification')
        self.assertEqual(rc,2); self.assertFalse(report['existence_proof_required_for_specification'])
        self.assertEqual(report['kernel_verification_status'],'not_run')

    def test_proof_does_not_bypass_disabled_gate(self):
        with patch.object(v,'YM_ADMISSION_REVIEWED',False):report,rc=v.verify(ROOT,'clay',Path('absent.lean'),'Fake')
        self.assertEqual(rc,2); self.assertEqual(report['proof_submission_status'],'not_evaluated_specification_incomplete')

    def test_ready_without_proof(self):
        report,rc,_=self.run_ready('specification')
        self.assertEqual(rc,0); self.assertEqual(report['status'],'SPECIFICATION_READY')
        self.assertEqual(report['proof_submission_status'],'not_submitted')
        self.assertEqual(report['kernel_verification_status'],'not_run')
        self.assertEqual(report['semantic_review_status'],'reviewed_fixed_specification')
        self.assertEqual(report['external_acceptance_status'],'not_assessed'); self.assertFalse(report['clay_certificate'])

    def test_ready_ym_no_proof_distinct(self):
        report,rc,_=self.run_ready('yangmills')
        self.assertEqual(rc,2); self.assertEqual(report['status'],'PROOF_NOT_SUBMITTED')
        self.assertEqual(report['specification_readiness'],'ready'); self.assertFalse(report['yang_mills_kernel_certificate'])

    def test_ready_wrong_compiled_definition_rejected(self):
        report,rc,_=self.run_ready('specification',outputs=[self.cp(),self.cp(1,'REJECTED: wrong target')])
        self.assertEqual(rc,1); self.assertEqual(report['specification_shape_status'],'rejected')

    def assert_ready_invalid_submission(self, report, rc):
        self.assertEqual(rc,1)
        self.assertEqual(report['status'],'INVALID_PROOF_SUBMISSION')
        self.assertEqual(report['proof_submission_status'],'invalid_arguments')
        self.assertEqual(report['specification_readiness'],'ready')
        self.assertTrue(report['full_target_defined'])
        self.assertEqual(report['specification_shape_status'],'passed')
        self.assertEqual(report['kernel_verification_status'],'not_run')
        self.assertFalse(report['yang_mills_kernel_certificate'])
        self.assertFalse(report['clay_certificate'])

    def test_ready_theorem_without_file_invalid(self):
        report,rc,_=self.run_ready('yangmills',theorem='Foo')
        self.assert_ready_invalid_submission(report,rc)

    def test_ready_file_without_theorem_invalid(self):
        report,rc,_=self.run_ready('yangmills',proof_file=Path('Candidate.lean'))
        self.assert_ready_invalid_submission(report,rc)

    def test_ready_bad_theorem_name_invalid(self):
        report,rc,_=self.run_ready('yangmills',Path('Candidate.lean'),'Foo\n#eval 1')
        self.assert_ready_invalid_submission(report,rc)

    def test_ready_nonlean_file_invalid(self):
        with tempfile.TemporaryDirectory() as tmp:
            proof=Path(tmp)/'Candidate.txt'; proof.write_text('not a Lean source')
            report,rc,_=self.run_ready('yangmills',proof,'Foo')
        self.assert_ready_invalid_submission(report,rc)

    def test_ready_absent_file_invalid(self):
        with tempfile.TemporaryDirectory() as tmp:
            report,rc,_=self.run_ready('yangmills',Path(tmp)/'absent.lean','Foo')
        self.assert_ready_invalid_submission(report,rc)

    def test_ready_unreadable_file_invalid(self):
        with tempfile.TemporaryDirectory() as tmp:
            proof=Path(tmp)/'Candidate.lean'; proof.write_text('theorem Foo : True := True.intro')
            original=Path.read_text
            def read(path,*args,**kwargs):
                if path==proof: raise PermissionError('fixture cannot read proof')
                return original(path,*args,**kwargs)
            with patch.object(Path,'read_text',read):
                report,rc,_=self.run_ready('yangmills',proof,'Foo')
        self.assert_ready_invalid_submission(report,rc)

    def test_ready_shape_marker_without_success_rejected(self):
        report,rc,_=self.run_ready('specification',outputs=[self.cp(),self.cp(1,'YM_SPECIFICATION_SHAPE_PASSED: spoof')])
        self.assertEqual(rc,1); self.assertFalse(report['full_target_defined'])

    def test_build_failure_no_readiness(self):
        report,rc,_=self.run_ready('specification',outputs=[self.cp(1,'build fail')])
        self.assertEqual(rc,1); self.assertEqual(report['status'],'BUILD_FAILED')

    def proof_case(self,mode,inspection):
        with tempfile.TemporaryDirectory() as tmp:
            fixture=Path(tmp)/'repo'; fixture.mkdir(); self.copy_source(fixture)
            proof=Path(tmp)/'Candidate.lean'; proof.write_text('theorem Foo : True := True.intro\n')
            if mode=='qft':
                with patch.object(v,'provenance',return_value={}),patch.object(v,'_run',side_effect=[self.cp(),self.cp(),inspection],root=fixture) as calls:
                    report,rc=v.verify(fixture,mode,proof,'Foo')
            else:
                report,rc,calls=self.run_ready(mode,proof,'Foo',[self.cp(),self.cp(text='YM_SPECIFICATION_SHAPE_PASSED:'),self.cp(),inspection],root=fixture)
        return report,rc,calls

    def test_qft_certificate_never_clay(self):
        report,rc,calls=self.proof_case('qft',self.cp(text='QFT_KERNEL_CHECK_PASSED: Foo'))
        self.assertEqual(rc,0); self.assertTrue(report['qft_only_certificate']); self.assertFalse(report['clay_certificate'])
        self.assertFalse(report['yang_mills_kernel_certificate']); self.assertEqual(calls.call_count,3)

    def test_qft_mode_does_not_misreport_global_ym_readiness(self):
        # The QFT branch deliberately never runs the YM definition-shape check.
        # This remains true even after the separately trusted YM gate activates.
        with patch.object(v,'YM_ADMISSION_REVIEWED',True):
            report,rc,calls=self.proof_case('qft',self.cp(text='QFT_KERNEL_CHECK_PASSED: Foo'))
        self.assertEqual(rc,0)
        self.assertEqual(report['specification_readiness'],'not_assessed_in_qft_mode')
        self.assertIsNone(report['full_target_defined'])
        self.assertEqual(report['semantic_review_status'],'not_assessed_in_qft_mode')
        self.assertEqual(report['specification_shape_status'],'not_run')
        self.assertEqual(calls.call_count,3)
        self.assertEqual(report['external_acceptance_status'],'not_assessed')
        self.assertFalse(report['clay_certificate'])

    def test_ym_kernel_not_external_certificate(self):
        report,rc,calls=self.proof_case('yangmills',self.cp(text='YM_KERNEL_CHECK_PASSED: Foo'))
        self.assertEqual(rc,0); self.assertTrue(report['yang_mills_kernel_certificate'])
        self.assertFalse(report['clay_certificate']); self.assertFalse(report['qft_only_certificate'])
        self.assertEqual(report['external_acceptance_status'],'not_assessed')
        self.assertEqual(report['admitted_target'],v.YM_TARGET)
        self.assertIn('yangmills',calls.call_args_list[-1].args[0])

    def test_clay_alias_is_kernel_only(self):
        report,rc,_=self.proof_case('clay',self.cp(text='YM_KERNEL_CHECK_PASSED: Foo'))
        self.assertEqual(rc,0); self.assertFalse(report['clay_certificate']); self.assertTrue(report['yang_mills_kernel_certificate'])

    def test_wrong_mode_marker_rejected(self):
        report,rc,_=self.proof_case('yangmills',self.cp(text='QFT_KERNEL_CHECK_PASSED: Foo'))
        self.assertEqual(rc,1); self.assertEqual(report['status'],'PROOF_REJECTED')

    def test_qft_failed_audit_rejected(self):
        report,rc,_=self.proof_case('qft',self.cp(1,'REJECTED: wrong type'))
        self.assertEqual(rc,1); self.assertFalse(report['qft_only_certificate'])

    def test_spoofed_compilation_message_not_evidence(self):
        report,rc,_=self.proof_case('yangmills',self.cp(1,'YM_KERNEL_CHECK_PASSED: spoof'))
        self.assertEqual(rc,1); self.assertFalse(report['yang_mills_kernel_certificate'])

    def test_unsafe_theorem_name_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            proof=Path(tmp)/'Proof.lean';proof.write_text('theorem Foo : True := True.intro')
            report,rc=v.verify(ROOT,'qft',proof,'Foo\n#print axioms Mathlib')
        self.assertEqual(rc,1); self.assertFalse(report['qft_only_certificate'])
        self.assertEqual(report['status'],'INVALID_PROOF_SUBMISSION')
        self.assertEqual(report['proof_submission_status'],'invalid_arguments')
        self.assertEqual(report['specification_readiness'],'not_assessed_in_qft_mode')

    def test_unknown_claim_rejected(self):
        report,rc=v.verify(ROOT,'unreviewed-mode')
        self.assertEqual(rc,1);self.assertIn('Unknown claim',report['error'])

if __name__=='__main__':unittest.main()
