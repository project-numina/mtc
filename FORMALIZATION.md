# Formalization status

Work in progress. The entire paper has been read and mapped in `PLAN.md`.

Lean and Mathlib are pinned to `v4.35.0`. Mathlib's 9031 cached artifacts were
downloaded with `LEAN_NUM_THREADS=8 taskset -c 0-7 lake exe cache get`.

The first skeleton used the monolithic `Mathlib` import, which exceeded a 1400 MB
per-process limit. It now uses selective imports. No Mathlib source build is
needed. The repository's original prompt and runner are preserved.

## Assumption ledger

No custom axiom declarations or `sorry` proofs have been introduced at this stage.
No main theorem has yet been claimed. See the exhaustive map in `PLAN.md` for
the categorical and numerical obligations still to implement.

## Paper audit

No mathematical error has yet been established. In particular, the existing
Mathlib centre construction does not supply the fusion/modular results used on
page 5. Those results must not be mistaken for already formalized infrastructure.

## Build

```sh
LEAN_NUM_THREADS=8 taskset -c 0-7 lake exe cache get
bash scripts/check.sh
```

The script pins CPU affinity to cores 0–7. The Lake configuration limits each
Lean elaborator to two threads and 1400 MB. Resource limits will be adjusted
within the requested aggregate budget if necessary.
