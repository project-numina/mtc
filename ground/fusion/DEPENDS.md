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
  semisimplicity route, prove centrality of the base pivotal map on the
  induced unit, with double-dual objects identified by `forgetDoubleDualIso`;
  it suffices to check simple test objects as stated by
  `center_fusion_of_simple_induced_pivotal_centrality`. Alternatively construct
  a centre cap on that induced object with nonzero coevaluation composite.
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

## Round 3

- A pivotal structure on the centre compatible with a positive base pivotal
  structure would now supply centre fusion, positive sphericality,
  pseudo-unitarity and both global dimension squares, assuming centre rigidity.
  Fusion is investigating the compatible pivotal lift; the compatibility is
  currently an explicit hypothesis, not a constructed result.
