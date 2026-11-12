#!/usr/bin/env python3
"""Fail when project modules are missing from either private-body audit."""
from pathlib import Path
import sys

root = Path(__file__).resolve().parent.parent
excluded = {
    "MTC.PropertyF.Audit.ProjectAudit",
    "MTC.PropertyF.Audit.TargetAudit",
}
modules = {
    ".".join(path.relative_to(root).with_suffix("").parts)
    for path in (root / "MTC").rglob("*.lean")
} - excluded
failed = False
for name in ("ProjectAudit", "TargetAudit"):
    path = root / "MTC" / "PropertyF" / "Audit" / f"{name}.lean"
    imports = {
        line.removeprefix("import all ").strip()
        for line in path.read_text(encoding='utf-8').splitlines()
        if line.startswith("import all ")
    }
    missing = sorted(modules - imports)
    if missing:
        failed = True
        print(f"{name} is missing private imports:", file=sys.stderr)
        for module in missing:
            print(f"  {module}", file=sys.stderr)
if failed:
    sys.exit(1)
print(f"Audit imports cover {len(modules)} project modules.")
