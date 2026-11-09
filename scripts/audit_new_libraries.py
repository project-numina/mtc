#!/usr/bin/env python3
"""Audit every declaration in the MTC library using Lean's kernel environment."""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent

LIBRARIES = ("MTC",)
SORRY = re.compile(r"(?<![\w'])(?:sorry|admit)(?![\w'])")


def code_without_comments_and_strings(text):
    """Mask nested Lean comments and strings, preserving token boundaries and newlines."""
    out = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        pair = text[i:i + 2]
        c = text[i]
        if depth:
            if pair == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif string:
            if c == "\\" and i + 1 < len(text):
                out.append("  ")
                i += 2
            else:
                if c == '"':
                    string = False
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            if end == -1:
                end = len(text)
            out.append(" " * (end - i))
            i = end
        elif c == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def main():
    try:
        # The token check covers project Lean sources; dependency audits below also catch `admit`.
        for path in sorted(ROOT.rglob("*.lean")):
            rel = path.relative_to(ROOT)
            if any(part.startswith(".") for part in rel.parts) or rel.parts[0] in ("scratch", "data"):
                continue
            code = code_without_comments_and_strings(path.read_text(encoding="utf-8"))
            if SORRY.search(code):
                raise ValueError(f"{rel}: unfinished proofs are forbidden in library sources")
        modules = []
        for lib in LIBRARIES:
            modules.append(lib)
            modules.extend(".".join(p.relative_to(ROOT).with_suffix("").parts) for p in sorted((ROOT / lib).rglob("*.lean")))
        imports = "\n".join(f"import all {m}" for m in modules)
        source = f'''module
public meta import Lean
{imports}

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let ownModule := (env.getModuleIdxFor? name).bind fun i => env.header.modules[i.toNat]?
    if ownModule.any (fun m => #["MTC"].any fun lib =>
        m.module.toString == lib || m.module.toString.startsWith (lib ++ ".")) then
      if Lean.isExtern env name || (Lean.Compiler.getImplementedBy? env name).isSome then
        throwError "Foreign implementation in project declaration {{name}}"
      for ax in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {{ax}} in project declaration {{name}}"
      checked := checked + 1
  logInfo m!"Audited {{checked}} declarations in MTC."
'''
        scratch = ROOT / "scratch"
        scratch.mkdir(exist_ok=True)
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", suffix=".lean", dir=scratch, delete=False) as f:
            f.write(source)
            filename = f.name
        try:
            env = os.environ.copy()
            env.setdefault("LEAN_NUM_THREADS", "4")
            return subprocess.call(["taskset", "-c", env.get("PROPERTYF_AUDIT_CORES", "0-3"), "lake", "env", "lean", filename], cwd=ROOT, env=env)
        finally:
            os.unlink(filename)
    except (ValueError, OSError) as exc:
        print(exc, file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
