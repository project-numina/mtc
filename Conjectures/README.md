# Conjecture files

Put one statement in `Conjectures/<Topic>/<Name>.lean`, using the namespace
`MTC.Conjectures.<Topic>`. The module docstring must contain the following single-line fields exactly
once. The dashboard and axiom audit read them. The declaration must be the fully qualified name of
the theorem defined in this file.

```lean
module
public import MTC.Seed

/-!
An informal, precise description of the statement and why it matters.
Explain known partial results and, for data-driven claims, the evidence and its coverage.

Status: open
Source: Author, arXiv:0000.00000, Conjecture 1
Declaration: MTC.Conjectures.Topic.exampleConjecture
-/

namespace MTC.Conjectures.Topic

/-- A human-readable description of the precise statement. -/
theorem exampleConjecture : True := by
  sorry

-- Add proved special cases and checks with substantive examples here.
end MTC.Conjectures.Topic
```

This is a format example, not a research problem. Replace the statement, imports, topic, source and
name. Use `PropertyF.Ground.Target` and its definitions directly for property F statements. Cite the
exact theorem or question when available and distinguish a conjecture from an established result.
Explain how hypotheses are satisfied and check the statement against examples. Do not assume that a
numerical modular datum is realized by a category unless there is evidence for that claim.

The status values are:

- `open`: no accepted proof or disproof is known.
- `solved`: an accepted proof exists in the literature, but this statement has not been formally proved here.
- `formalized`: the statement has a proof in this repository with only the allowed axioms.
- `disproved`: a counterexample has been established; cite it and identify the precise statement refuted.

Cite the basis for status changes. For `open`, `solved` and `disproved`, only the named conjecture
itself may depend on `sorryAx`; auxiliary results must have complete proofs. A `formalized` statement
must be free of `sorryAx` and all other nonstandard axioms. Regenerate the dashboard with
`python3 scripts/conjecture_status.py` and commit the result.
