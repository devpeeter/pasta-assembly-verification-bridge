"""Fast checks of exact document formatting and generated-candidate freshness."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


SOURCE = Path(__file__).resolve().parents[1] / 'scripts/generate_mul_json_certificate.py'


class CertificateGeneratorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='pasta-json-certificate-')
        self.root = Path(self.temp.name)
        for directory in ('scripts', 'bridge', 'generated'):
            (self.root / directory).mkdir()
        self.script = self.root / 'scripts' / SOURCE.name
        shutil.copyfile(SOURCE, self.script)

    def tearDown(self):
        self.temp.cleanup()

    def run_generator(self, data, *args):
        (self.root / 'generated/mul-check.json').write_bytes(data)
        return subprocess.run([sys.executable, str(self.script), *args],
                              text=True, capture_output=True)

    def test_fresh_candidate_and_stale_candidate(self):
        raw = b'{"a":"one"}\n'
        self.assertEqual(self.run_generator(raw).returncode, 0)
        self.assertEqual(self.run_generator(raw, '--check').returncode, 0)
        for name in ('MulJsonTextDagBase.lean', 'MulJsonTextDagFinal.lean'):
            target = self.root / 'bridge' / name
            target.write_bytes(target.read_bytes() + b'\n')
            result = self.run_generator(raw, '--check')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('stale', result.stderr)
            self.assertEqual(self.run_generator(raw).returncode, 0)

    def test_missing_final_lf_rejected(self):
        result = self.run_generator(b'{"a":"one"}')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('one final LF', result.stderr)

    def test_duplicate_key_rejected(self):
        result = self.run_generator(b'{"a":1,"a":2}\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('compact ordered ASCII JSON', result.stderr)

    def test_unicode_escape_rejected_explicitly(self):
        result = self.run_generator(b'{"a":"\\u1234"}\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('unsupported non-ASCII', result.stderr)


if __name__ == '__main__':
    unittest.main()
