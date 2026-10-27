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
