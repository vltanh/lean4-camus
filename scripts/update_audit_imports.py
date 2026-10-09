#!/usr/bin/env python3
"""Refresh Audit.lean's import-all block from all Camus library modules."""
import argparse
from pathlib import Path

root = Path(__file__).resolve().parent.parent
path = root / "scripts" / "Audit.lean"
text = path.read_text()
start = text.index("import all Camus")
end = text.index("import all Solution", start)
imports = "\n".join(
    "import all " + ".".join(p.relative_to(root).with_suffix("").parts)
    for p in [root / "Camus.lean", *sorted((root / "Camus").rglob("*.lean"))]
)
expected = text[:start] + imports + "\n" + text[end:]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--check", action="store_true")
args = parser.parse_args()
if args.check:
    if text != expected:
        raise SystemExit("Audit import list is out of date")
    print("Audit imports every library module")
else:
    path.write_text(expected)
