# Contributing

Preserve the mathematical hypotheses, conclusions, and categorical definitions.
Keep proofs readable with meaningful named lemmas. Every library declaration
must be complete and use only `propext`, `Classical.choice`, and `Quot.sound`.

After changing Lean modules, regenerate root imports with
`python3 scripts/update_roots.py` and maintain both private-body audit import lists.
Run `scripts/check.sh` and `scripts/audit-target.sh` before submitting changes.
Describe mathematical changes and verification; disclose substantial AI assistance.
