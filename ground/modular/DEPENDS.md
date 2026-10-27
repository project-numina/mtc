# Dependencies for modular workstream

- **fusion**: the genuine category interface, fusion coefficients, dual reciprocity and the positive-character uniqueness theorem have been merged and used to prove both ground and legacy `conjugate_labels`.
- **dimensions**: pivotal/spherical structure, categorical trace and its cyclicity, trace of identity, multiplicativity, duality and semilinear transport. Used to define S and prove symmetry and the unit column. The iterated pivotal trace and partial-trace constructions are now merged and used to prove the Hopf-link product and Verlinde equations. The spherical structure on the centre and semilinear transport of traces remain dependencies.
- **centre**: construction of the non-degenerate spherical braided fusion structure on the Drinfeld centre, expressed using the shared fusion and dimensions interfaces. Needed to instantiate modular data for the centre and obtain a precise nondegeneracy condition from which to prove S².
- **integrate**: the frozen target category and conjugacy interfaces have been merged; the final centre/rigidity witness still needs integration.

The actual categorical S identities, character classification and Galois action are proved under a spherical pivotal structure, real simple dimensions and invertible S. The missing inputs are the centre-specific constructions and their connection to nondegeneracy, not the earlier abstract character classification.
