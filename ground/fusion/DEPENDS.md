# Fusion dependencies

- Centre: constructing the centre as a genuine finite semisimple rigid braided
  category, and its induction/forgetful theory, is needed for the centre global
  FP dimension square comparison. Coordinate its exact theorem interface once
  that structure is available.
- Cabling: the generated fusion category, FP-dimension preservation, and
  simple-square integrality are now constructed in fusion. Cabling supplies
  the remaining categorical braid/cabling witness and corollary packaging.
- Integrate/modular: simple-presentation independence and semilinear conjugacy
  invariance are already proved and merged; no additional hypothesis is needed.

These describe proof obligations, not axioms or assumptions in the target.

## Round 2

- Centre: construct rigidity for the actual Mathlib centre. For the alternate
  semisimplicity route, construct a pivotal structure on that centre and show
  its trace on `induction C (𝟙_ C.Obj)` maps to the base trace, or directly
  construct a centre cap on this induced object whose composite with its
  coevaluation is nonzero. These are precise remaining external interfaces;
  see `center_fusion_of_positive_compatible_pivotal` and
  `center_fusion_of_nonzero_induced_cap`.
- Dimensions: construct a positive base pivotal structure for the relevant
  pseudo-unitary category. Fusion proves its trace on the underlying induced
  unit is FPdim(C), hence nonzero.
- Fusion constructs the actual induction functor and forgetful right adjunction,
  finite-dimensional centre Homs, Artinian/Noetherian centre objects, and
  finite simple representatives. Once centre rigidity and either the pivotal
  compatibility or the internal loop-sliding proof is supplied, the existing
  constructions produce centre semisimplicity/fusion and the global FP square.
- Fusion's own alternative `SimpleLoopCentrality` is the explicit finite
  weighted-loop sliding equation for arbitrary underlying maps. It remains
  unproved. Together with sphericality and nonzero global dimension, it
  yields splitting independently of the pivotal-lift route.
