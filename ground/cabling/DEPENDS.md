# Dependencies

- Resolved: fusion's split-unit, semisimplicity, FP-character, full-inclusion
  dimension preservation, and weak-integrality simple-square theorems.
- Resolved: modular's braided-functor braid-image coherence.
- Resolved: calculus' left/right strand-insertion coherence.
- Resolved: integrator's legacy-category compatibility and simple-strand
  inclusion bridges. The unconditional ground results do not assume legacy
  hypothesis structures.
- Handoff: the integration workstream must merge `ground/cabling` and use the
  bundle-free property-F and generated-category theorems in the frozen target.

## Round 2

- Centre/fusion: actual `RigidCategory (Center C.Obj)` and
  `IsFusionCategory (Center C.Obj)` instances are needed by the proved
  product-retract dual-closure theorem. No centre dominance is assumed.
- Modular/centre: double-centralizer work needs categorical S nondegeneracy
  and a proof that the S test expresses double-braiding centrality, together
  with the modular centralizer dimension formula (or a direct equivalent).
- Centre/modular: `productLabels_doubleCentralizer` reduces our actual-centre
  double centralizer to proving numerical S-centralizers of product labels lie
  in the integral symmetric core. The missing bridge is S-test to identity
  double braiding (the other direction is proved), plus symmetric-core
  integrality from calculus.
- The categorical bridge now reduces to `IsOfFinOrder` for actual centre double
  braidings between a product-retract simple and an arbitrary simple. A
  finite-order ribbon twist/Vafa result or a direct centre-specific argument
  would suffice. Base property F alone has not been shown to provide this.

## Round 3 finite-twist route

`mixed_monodromy_finite_of_balanced_finite_twist` reduces finite mixed
monodromy to the balancing identity and finite order of simple pivotal twists.
Neither the balancing identity for the actual pivotal/Drinfeld twist nor the
Vafa root-of-unity theorem is assumed proved. Cabling is working on these
steps; the centre's rigid/fusion instances remain separate.
