import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import ci_unit
import source_manifest


class SourceManifestTests(unittest.TestCase):
    def test_refresh_covers_hidden_workflows_and_nested_manifests(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / '.github/workflows').mkdir(parents=True)
            (root / '.github/workflows/unit.yml').write_bytes(b'name: check\n')
            (root / 'nested').mkdir()
            (root / 'nested/SOURCE-MANIFEST.json').write_bytes(b'{}\n')
            result = source_manifest.refresh(root)
            self.assertEqual(result['checked_files'], 2)
            manifest = json.loads((root / 'SOURCE-MANIFEST.json').read_bytes())
            self.assertEqual(set(manifest['files']),
                             {'.github/workflows/unit.yml', 'nested/SOURCE-MANIFEST.json'})
            self.assertNotIn(b'\r', (root / 'SOURCE-MANIFEST.json').read_bytes())

    def test_default_check_rejects_changes_without_rewriting_manifest(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / 'proof.lean'
            source.write_bytes(b'theorem example : True := trivial\n')
            source_manifest.refresh(root)
            original = (root / 'SOURCE-MANIFEST.json').read_bytes()
            source.write_bytes(b'changed source\n')
            with patch.object(source_manifest, 'ROOT', root), patch.object(sys, 'argv', ['source_manifest.py']):
                with self.assertRaises(ci_unit.CiError):
                    source_manifest.main()
            self.assertEqual((root / 'SOURCE-MANIFEST.json').read_bytes(), original)

    def test_empty_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(ValueError, 'empty'):
                source_manifest.refresh(Path(temporary))
