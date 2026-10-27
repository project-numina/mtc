# Style survey tooling

Run from this worktree:

```sh
scripts/style/run.sh
```

This builds and audits `PropertyF`, runs the full-project environment `#lint`, imports Mathlib and the private project modules used by the audit into a separate Lean analysis module, and regenerates `STYLE_REPORT.md`, `STYLE_FILES.tsv`, `STYLE_DECLARATIONS.tsv`, `STYLE_NAME_MATCHES.tsv`, `STYLE_LINT_ENV.txt`, and `STYLE_LINT_BUILD.txt`. It also checks one confirmed Mathlib replacement using `ExistingMathlib.lean`. The manually authored `STYLE_PLAN.md` is not regenerated. The command pins heavy Lean jobs to CPUs 28–31 and sets `LEAN_NUM_THREADS=4`. It does not modify the library or Mathlib. It requires the pinned Lake dependencies and built Mathlib artifacts; the first project build can take several minutes. Intermediate data files beginning with a dot in this directory are ignored by Git.

For source-only iteration on an existing environment dump, use `python3 scripts/style/survey.py --skip-lean`; a stale dump gives a stale cone, so do not publish that as a fresh survey. Use `envlint.py` to regenerate the environment lint independently. Default linter warning blocks from the full build, including Lake replay, and the complete environment lint output are recorded.

The report defines the source heuristics, sampling scheme, and distribution convention. Inspect source candidates before acting: expression-hash equality is neither proof of equality nor a semantic search. The cone contains declarations reached by constants in types and available bodies; project private bodies are imported exactly as in the target audit. It does not model elaboration-time side effects, tactic dependencies, public API obligations, or future uses. File-local declaration name matching may omit ambiguous names. Source parser boundaries and tactical counts are heuristic, particularly for notation, nested syntax, and equation-style declarations. For semantic changes run the independent audit described in the plan.
