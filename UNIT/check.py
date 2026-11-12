#!/usr/bin/env python3
"""Check frozen dependencies, all Unit declarations, and relation independence.

Usage: python3 UNIT/check.py [path/to/seg]
UNIT_CHECKER is also accepted; otherwise use the recorded local checker.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def main():
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "vendor-manifest.json").read_text())
    for item in manifest["files"]:
        path = root / item["file"]
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        if digest != item["sha256"]:
            sys.exit(f"Dependency differs from snapshot: {path}")
        if (root / path.name).resolve() != path.resolve():
            sys.exit(f"Import does not point to snapshot: {root / path.name}")
    if len(sys.argv) > 2:
        sys.exit(__doc__)
    checker = Path(sys.argv[1] if len(sys.argv) == 2 else
                   os.environ.get("UNIT_CHECKER", manifest["checker"]["path"]))
    checker = checker.expanduser().resolve()
    if not checker.is_file():
        sys.exit("Unit checker missing. Pass its path or set UNIT_CHECKER.")
    recorded = hashlib.sha256(checker.read_bytes()).hexdigest() == manifest["checker"]["sha256"]
    print(f"Dependencies: {len(manifest['files'])} hashes verified", flush=True)
    print(f"Checker: {checker} ({'recorded build' if recorded else 'different build'})", flush=True)
    for source in ("All.seg", "IndependentLogicalRelationCheck.seg"):
        try:
            result = subprocess.run([str(checker), source], cwd=root,
                                    text=True, capture_output=True, timeout=60)
        except subprocess.TimeoutExpired:
            sys.exit(f"Unit check of {source} timed out after 60 seconds.")
        print(result.stdout, end="")
        print(result.stderr, end="", file=sys.stderr)
        if result.returncode:
            sys.exit(result.returncode)
        if not re.search(re.escape(source) + r": \d+ declarations, 0 failed,", result.stdout):
            sys.exit(f"Checker did not report a complete successful check of {source}.")


if __name__ == "__main__":
    main()
