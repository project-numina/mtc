#!/usr/bin/env python3
"""Run Batteries/Mathlib environment linters over all imported project declarations."""
from pathlib import Path
import os
import re
import subprocess
root=Path(__file__).resolve().parents[2]
os.chdir(root)
audit=(root/'PropertyF/Ground/Integrate/TargetAudit.lean').read_text()
imports='\n'.join(re.findall(r'^import all .+$',audit,re.M))
source=root/'scripts/style/.EnvLintRun.lean'
source.write_text('module\npublic meta import Mathlib\n'+imports+'\nset_option maxHeartbeats 0 in\n#lint in PropertyF\n')
with (root/'STYLE_LINT_ENV.txt').open('w') as out:
    r=subprocess.run(['taskset','-c','28-31','lake','env','lean',str(source.relative_to(root))], stdout=out, stderr=subprocess.STDOUT,env={**os.environ,'LEAN_NUM_THREADS':'4'})
text=(root/'STYLE_LINT_ENV.txt').read_text()
# #lint returns an error when findings exist; reject infrastructure/syntax errors.
if r.returncode and 'declarations (plus' not in text:
    raise SystemExit('Environment lint failed before reporting findings; see STYLE_LINT_ENV.txt')
print(f'Environment lint finished (Lean exit {r.returncode}); see STYLE_LINT_ENV.txt')
