# Property F implies weak integrality for pseudo-unitary braided fusion categories

[manuscript.pdf](manuscript.pdf) · [manuscript.txt](manuscript.txt)

The manuscript proves that every braided fusion category with property F and a pseudo-unitary
Galois conjugate is weakly integral. This is one direction of the Naidu–Rowell property F
conjecture, for a class that includes all unitary modular tensor categories.

**Status:** formalized, with no additional hypotheses. The axiom audit reports exactly
`[propext, Classical.choice, Quot.sound]`; an independent review is in
[docs/verification.md](../../docs/verification.md).

| Manuscript | Lean declaration | File |
|---|---|---|
| Theorem 1.1 | `MTC.PropertyF.weaklyIntegral_of_propertyF` | [MTC/PropertyF/Theorem.lean](../../MTC/PropertyF/Theorem.lean) |
| Definitions used in the statement | `MTC.PropertyF.TargetStatement` | [MTC/PropertyF/Statement.lean](../../MTC/PropertyF/Statement.lean) |
| Consequences for pseudo-unitary categories | | [MTC/PropertyF/PseudoUnitary.lean](../../MTC/PropertyF/PseudoUnitary.lean) |
