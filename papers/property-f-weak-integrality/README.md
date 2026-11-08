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
| Theorem 1.1 (`thm:main` in the full manuscript) | `MTC.PropertyF.weaklyIntegral_of_propertyF` | [MTC/PropertyF/Theorem.lean](../../MTC/PropertyF/Theorem.lean) |
| Definitions used in the statement | `MTC.PropertyF.TargetStatement` | [MTC/PropertyF/Statement.lean](../../MTC/PropertyF/Statement.lean) |
| Consequences for pseudo-unitary categories | | [MTC/PropertyF/PseudoUnitary.lean](../../MTC/PropertyF/PseudoUnitary.lean) |

## Later pivotal manuscript

[property-f-pivotal-simplified.tex](property-f-pivotal-simplified.tex) ([PDF generated from this source](property-f-pivotal-simplified.pdf)) is the later manuscript
“Property F implies weak integrality” dated October 22, 2026. It is distinct from the
October 22 PDF listed above: its main theorem treats nondegenerate **pivotal** braided fusion
categories, without assuming a pseudo-unitary conjugate. The source was supplied as Slack file
`F0CDCTLCP7S` (posted October 27, 2026); the supplied context identifies it with the title and
date of the latest PDF in the November 8 thread. SHA-256:
`eeaebf94753d7d98a216a3e2e0e9faa37b2d024222adf433c66b2b750093d10f`.
The linked PDF was generated locally from this source with Tectonic 0.15.0; it is not a copy of the Slack PDF. The repository's earlier October 22 PDF has a different abstract and main theorem and is preserved unchanged.

The existing theorem above formalizes the weak-integrality conclusion under the stronger
pseudo-unitary-conjugate hypothesis. It does **not** establish the new pivotal manuscript's
main theorem, its degenerate extension, normalization or closure lemmas, or its objectwise
conclusion. The table below tracks the new manuscript independently.

| Later manuscript result | Current Lean coverage |
|---|---|
| Proposition 2.1 (`prop:FPobject`) | `MTC.PropertyF.Pivotal.existsUnique_fp_column_globalDimension` proves the unique FP column and its intrinsic global-dimension identity for any pivotal structure with invertible categorical S matrix. Equivalence of invertibility with categorical nondegeneracy remains outstanding. |
| Trace bound and saturation (`lem:trace`, `lem:saturation`) | `MTC.Braided.Trace.pivotal_unitary_trace_bound`, `norm_monodromy_trace_div_dimension_le_fp`, and `MTC.PropertyF.Pivotal.pivotal_saturation` prove the general pivotal trace bound and both parts of the saturation lemma, including complex dimensions and zero-weight support. |
| Nondegenerate proposition and main theorem (`prop:nondeg`, `thm:main`) | `NondegenerateMainStatement` records an unproved target. Under invertibility of the actual pivotal S matrix, `fp_column_invertible_of_propertyF` proves pseudo-unitarity and an actual tensor inverse for the FP object using its finite braid images, `weaklyIntegral_of_invertibleS_of_propertyF` proves weak integrality, and `main_of_invertibleS_of_propertyF` proves pseudo-unitarity, pseudo-unitarity of every semilinearly equivalent Galois conjugate, and weak integrality. `categoricalS_det_ne_zero_of_trivial_S_centralizer` reduces invertibility to numerical S-centrality of only the tensor unit. `isNondegenerate_conjugate` proves categorical nondegeneracy transfers to arbitrary semilinearly braided equivalent conjugates. The remaining bridge for the stated manuscript hypothesis is numerical S-centrality to actual transparency, and thus categorical nondegeneracy to invertibility. |
| Centre and normalization lemmas, degenerate theorem (`lem:centre`, `lem:normalise`, `thm:degenerate`) | The general pivotal centre is fusion (`MTC.Center.Induction.center_fusion_of_pivotal`) and its global dimension is squared (`globalDimension_square_of_pivotal`). `NormalizationStatement` and `DegenerateMainStatement` record unproved targets; `adjointGenerated_simple_iff` and `positiveOnTransparentAdjoint_iff_categorical` identify their fusion labels and positivity condition with the actual tensor, dual, finite-sum and retract closure of simple adjoint generators. The finite fusion-degree group, kernel/character extension, and `fusionDegree_zero_iff_adjointLabel` are proved; `normalize_pivotal_on_muger_of_adjoint_positivity` proves normalization from the stated label-level positivity condition and transparent-simple FP-norm saturation; `pivotal_doubleCentralizer_of_invertibleS` handles numerical double centralizers without sphericality. `bundledMuger` constructs the actual symmetric transparent fusion subcategory, proves FP and pivotal dimension preservation, and reduces transparent FP-norm saturation to pseudo-unitarity of that subcategory; actual transparent simple labels form a fusion subring; the first canonical-image centralizer identity and FP-column placement under the explicit numerical-to-actual criterion are proved. `pseudoUnitary_of_adjoint_positivity_and_center_criteria` connects the adjoint-positivity hypothesis to pseudo-unitarity, conditional on transparent FP-norm saturation and the centre S-matrix criteria. Proving pseudo-unitarity of the symmetric transparent fusion subcategory, proving the centrality criterion, and the full results remain open. |
| Pseudo-unitary-conjugate corollary (`cor:pu`) | The existing `weaklyIntegral_of_propertyF` proves weak integrality under this hypothesis; the additional pseudo-unitarity conclusion is not yet established here. |
| Closure lemma and eventual objectwise infinite images (`lem:closure`, `cor:object`) | `MTC.PropertyF.Pivotal.eventually_infinite_braidImages_of_not_objectPropertyF` proves eventual infinitude when the simple object already fails objectwise property F. `ClosureStatement` records the unproved closure target, and `finite_braidImage_of_finite_pure` reduces it to the pure braid image. `sweepBlockCross_word` proves actual arbitrary positive-width rectangular block crossings are explicit braid words. Their common-flattening realization for all generators, the pure-braid treatment of sums, closure, and hypotheses guaranteeing an initial infinite image remain open. |
