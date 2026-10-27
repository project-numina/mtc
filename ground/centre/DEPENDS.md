# Centre dependencies

- integrate: frozen target definition of genuine braided fusion category, and its importable interface.
- fusion: finite semisimple category machinery, simple decompositions, tensor functor properties, Frobenius–Perron dimension and uniqueness; needed to construct and calculate the centre's fusion structure and FP dimension.
- dimensions: pivotal/spherical categories, traces and canonical pseudo-unitary structure; needed to equip the centre and prove dimension identities and symmetric-core integrality.
- modular: categorical modular-data interface and construction from nondegeneracy; needed for `CenterInputs.data`.
- calculus: three-strand realization from finite braid images, needed for `CenterInputs.realize`.
- cabling: summand restriction and tensor product braid-image transport, if these are factored out there; needed for `product_witness`.

Exact signatures depend on the frozen category interface and will be refined as it becomes available. These entries do not posit proof-bearing assumptions in the code.

## Round 2 precise centre interface

- fusion: construct, for `C : BraidedFusionCategory` and the canonical centre
  categorical instances (in particular its eventual `RigidCategory` instance),
  `∃ n (S : Fin n → Center C.Obj), (∀ i, Simple (S i)) ∧
  (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧ ∀ X, ∃ m : Fin n → ℕ,
  Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => S p.1))`. This is exactly
  the final argument of `CentreBundle.fusionOfFiniteSemisimple`; it is not
  assumed in the final target. Centre rigidity is independently unfinished.
