"""Check the source manifest, or explicitly refresh it after reviewed changes.

Refreshing hashes is packaging maintenance, not proof or acceptance evidence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from ci_unit import ARCHIVE_PREFIX, ROOT, check_source_manifest, source_files


def refresh(root: Path) -> dict:
    files = source_files(root)
    if not files:
        raise ValueError('refusing an empty source manifest')
    manifest = {'format': 1, 'archive_prefix': ARCHIVE_PREFIX,
                'files': {name: hashlib.sha256(path.read_bytes()).hexdigest()
                          for name, path in sorted(files.items())}}
    (root / 'SOURCE-MANIFEST.json').write_bytes(
        (json.dumps(manifest, indent=2) + '\n').encode('utf-8'))
    return check_source_manifest(root)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true',
                        help='explicitly update packaging hashes; does not run or approve proofs')
    args = parser.parse_args()
    result = refresh(ROOT) if args.write else check_source_manifest(ROOT)
    print(json.dumps({'status': 'PASS', 'mode': 'refreshed' if args.write else 'checked',
                      **result}, indent=2))
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit('Source manifest failed: ' + str(error)) from error
