# Dependencies for modular workstream

- **fusion**: the genuine category interface, fusion coefficients, dual reciprocity and the positive-character uniqueness theorem have been merged and used to prove both ground and legacy `conjugate_labels`.
- **dimensions**: pivotal/spherical structure, categorical trace and its cyclicity, trace of identity, multiplicativity, duality and semilinear transport. Used to define S and prove symmetry and the unit column. The iterated pivotal trace and partial-trace constructions are now merged and used to prove the Hopf-link product and Verlinde equations. The spherical structure on the centre and semilinear transport of traces remain dependencies.
- **centre**: construction of the non-degenerate spherical braided fusion structure on the Drinfeld centre, expressed using the shared fusion and dimensions interfaces. Needed to instantiate modular data for the centre and obtain a precise nondegeneracy condition from which to prove S².
- **integrate**: the frozen target category and conjugacy interfaces have been merged; the final centre/rigidity witness still needs integration.

The actual categorical S identities, character classification and Galois action are proved under a spherical pivotal structure, real simple dimensions and invertible S. The missing inputs are the centre-specific constructions and their connection to nondegeneracy, not the earlier abstract character classification.

## Round 2
- **fusion**: construct induction objects `I i` in the actual centre with `finrank (Z_j ⟶ I i) = finrank (U Z_j ⟶ X_i)` and `fpDimension Z (I i) = globalFPDimension C * fpSimple C i`. These are precisely the two open premises of `CentreModular.center_globalFPDimension_of_induction`; an underlying decomposition for `U I(X)` suffices for the size equation.
- **centre**: provide actual centre rigidity and `IsFusionCategory`, using `Integrate.bundledCenter C`.
- **dimensions**: provide positive spherical structure of the actual centre; `CentreModular.center_globalDimension_of_induction` then derives the categorical square formula from the above induction facts.
- **fusion/centre**: for nondegeneracy, the centre-specific Hopf-link separation/coend identity for distinct simple centre objects remains to be constructed.

- **modular / fusion induction**: prove the actual centre Kirby sum `∑ z, simpleDimension Z p z * categoricalS Z p k z = if k = unitIndex Z then D else 0` with nonzero D; `CentreModular.categoricalS_det_ne_zero_of_kirby` then proves modularity. The Kirby identity is an unproved centre-specific categorical equality, not an independently obtained nondegeneracy result.
- **dimensions**: centre pseudo-unitarity cannot follow solely from the global FP-square identity; an independent intrinsic global-dimension comparison or positive spherical construction is required.
- **centre/cabling**: the preferred modularity interface is now the triviality of the actual centre's S-centralizer: `∀ k, (∀ i, S i k = dim i * dim k) → k = unitIndex Z` (under FP-valued pivotal dimensions). `categoricalS_det_ne_zero_of_trivial_S_centralizer` proves invertibility from exactly this statement. A proof that the numerical S-test implies transparent double-braidings is still needed, as is triviality of transparent centre objects; neither is assumed proved.
- **modular / centre**: bridging the numerical S test to actual double-braiding transparency requires an additional argument, not merely equality of traces. Finite-order/twist control or a direct induction-loop identity are possible routes, neither currently proved. The centre induction lift and adjunction from fusion and rigid instances from centre are unavailable at the latest merged snapshot.

## Round 3 update
- Fusion has now constructed `induction` and `actualAdjunction`; the actual
  FP square follows from centre rigidity and fusion alone.
- A centre pivotal structure whose components agree with an FP-valued base
  pivotal structure after the canonical dual comparison would now suffice for
  centre sphericality and the categorical dimension square, without assuming
  centre pseudo-unitarity. Constructing that compatible lift remains open.
- The actual centre Kirby identity or another proof of S invertibility remains
  open; numerical S-centrality alone cannot be identified with endomorphism
  transparency without an additional argument.
- The centre Kirby sum can now be rewritten as the weighted sum of actual
  induced-simple Hopf links, in `CentreModular.center_kirby_sum_eq_induced`.
  Evaluating this sum on non-unit centre simples remains open.
- The remaining induced Kirby-loop evaluation is now an explicit finite sum of
  base-category diagonal fusion-block traces (`center_kirby_sum_eq_diagonal_traces`),
  assuming the displayed pivotal compatibility. Vanishing is not yet proved.
- Vafa determinant route: the regular-element cancellation is now proved, but
  actual categorical determinants, their hexagon/tensor identities and the
  torsion-detection vector space remain open.
- `vafaUnitSpace` and `vafaUnitClass_eq_zero_iff` now provide the missing
  torsion-detection space for complex units. The categorical determinant and
  its hexagon/tensor equations remain unproved.
- `fpDeterminant` is constructed and satisfies composition and scalar rules.
  The missing categorical step is its tensor-product rule, then the hexagon
  relation for double braidings; finite monodromy does not yet follow.
- The FP determinant is conjugation invariant and has the tensor rule for
  simple-object automorphisms. The arbitrary-object tensor rule still needs
  block determinant/decomposition arguments.
- Centre rigidity is now constructed and merged (centre f1f0122).
- `finite_order_of_fp_twist_balance` reduces Vafa finite order to one explicit
  FP-weighted fusion equation. The categorical proof of that equation remains
  open; no unconditional finite-order result is claimed.
- The natural-automorphism determinant formula and its finite-order
  consequence are constructed. Actual twist balancing and vanishing FP
  determinants of simple double braidings remain explicit open premises.
- `fpDeterminant_biprod` proves direct-sum additivity for block-diagonal
  automorphisms. Tensor compatibility for arbitrary automorphisms remains open.
