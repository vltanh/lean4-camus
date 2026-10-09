#!/usr/bin/env python3
"""Refresh Audit.lean's import-all block from all Camus library modules."""
from pathlib import Path

root = Path(__file__).resolve().parent.parent
path = root / "scripts" / "Audit.lean"
text = path.read_text()
start = text.index("import all Camus.")
end = text.index("import all Solution", start)
imports = "\n".join(
    "import all " + ".".join(p.relative_to(root).with_suffix("").parts)
    for p in sorted((root / "Camus").rglob("*.lean"))
)
path.write_text(text[:start] + imports + "\n" + text[end:])
