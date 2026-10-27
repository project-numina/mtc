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

- Centre: rigid and `IsFusionCategory` instances on the actual Mathlib centre
  (including semisimplicity and finite simple representatives). Fusion's
  `CentreInduction.globalFPDimension_square_of_induction` also requires, for
  every base simple, an actual centre object whose underlying object is
  `CentreInduction.underlying`, and the Hom-dimension equality given by the
  adjunction to forget; these are fusion's own unproved obligations.
- Dimensions: the nonzero spherical global dimension and relevant trace
  identities for the averaging splitting may be needed to prove semisimplicity.

- Fusion's own outstanding `CentreInduction.SimpleLoopCentrality` is the
  explicit finite loop-sliding equation for arbitrary underlying maps. Under
  that identity, a spherical structure on C and nonzero global dimension,
  the proved averaging construction splits all centre monos and epis.
