# Property F implies weak integrality for pseudo-unitary braided fusion categories

- [property-f-unitary.tex](property-f-unitary.tex) ([PDF](property-f-unitary.pdf)): the full
  manuscript, October 15, 2026.
- [property-f-simplified.pdf](property-f-simplified.pdf): a shorter proof by contradiction,
  written by Julio Parra-Martinez (October 22, 2026). The formalization follows this argument.
  Its LaTeX source will be added when available.

Both prove that every braided fusion category with property F and a pseudo-unitary
Galois conjugate is weakly integral. This is one direction of the Naidu–Rowell property F
conjecture, for a class that includes all unitary modular tensor categories.

**Status:** formalized, with no additional hypotheses. The axiom audit reports exactly
`[propext, Classical.choice, Quot.sound]`; an independent review is in
[docs/verification.md](../../docs/verification.md).

| Manuscript | Lean declaration | File |
|---|---|---|
| Theorem 1.1 (`thm:main` in the full manuscript) | `PropertyF.Ground.target` | [PropertyF/Ground/Final.lean](../../PropertyF/Ground/Final.lean) |
| Definitions used in the statement | `PropertyF.Ground.TargetStatement` | [PropertyF/Ground/Target.lean](../../PropertyF/Ground/Target.lean) |
| Consequences for pseudo-unitary categories | | [MTC/PropertyF/PseudoUnitary.lean](../../MTC/PropertyF/PseudoUnitary.lean) |
