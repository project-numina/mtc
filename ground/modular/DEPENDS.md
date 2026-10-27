# Dependencies for modular workstream

- **fusion**: a genuine fusion category interface, integral fusion coefficients, and a proof of existence/uniqueness of its positive fusion character; isomorphism invariance and semilinear equivalence preservation of fusion coefficients. Needed for `conjugate_labels`.
- **dimensions**: pivotal/spherical structure, categorical trace and its cyclicity, trace of identity, multiplicativity, duality and semilinear transport. Needed to define S and establish its identities.
- **centre**: construction of the non-degenerate spherical braided fusion structure on the Drinfeld centre, expressed using the shared fusion and dimensions interfaces. Needed to instantiate modular data for the centre.
- **integrate**: frozen target category and conjugacy interfaces, for connecting these constructions to the final theorem.

The abstract character action in `PropertyF/Ground/Modular/Characters.lean` is already kernel checked without these category-level assumptions. Its constructor explicitly requires classification of normalized S-columns and the numerical S identities; these are remaining proof obligations, not completed dependencies.
