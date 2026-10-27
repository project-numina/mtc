# Cabling workstream status

## Done

- `PropertyF.addLeftStrand`, `addLeftStrand_injective`, `strandEmbedding`,
  `strand_inclusion_of_faithful_tensor`: adjoining identity strands gives
  injections of braid images whenever left tensoring is faithful.
- `tensorLeft_faithful_of_unit_retract` and
  `strand_inclusion_of_unit_retract`: a split copy of the unit in `Y ⊗ X`
  implies tensoring by X is faithful and thus gives strand inclusion.

- `strandPermutation`, `pureWords`, `braidWordAction`, `pureBraidImage` and
  `pureBraidImage_finiteIndex`: categorical pure braid images have finite
  index, using permutation of free words.
- `cablingWitnessOfPureAction`: constructs a full `CablingWitness` from
  a pure-word map to the product of cabled braid images and the precise
  kernel containment needed to descend to the pure image.

## In progress

- Obtain the split unit for simple X from rigidity, semisimplicity, and the
  simple unit. Fusion has been asked for the corresponding construction.
- Construct the categorical pure-word map to cabled images and prove its
  kernel containment for a retract of a sum of powers.
- Prove that a faithful braided functor identifies braid images via its
  monoidal coherence isomorphism.

## Remaining

- Construct all other `GeneratedInputs` fields, including the generated
  fusion category, its inclusion and essential image, and cabling witnesses.
- Prove ENO 8.27 and preservation of FP dimension along the inclusion.
- The project lacks constructions of fusion categories, semisimplicity, FP
  dimensions and nonzero-object tensor faithfulness. The final target and
  interfaces are being developed by the other workstreams. Full completion
  requires substantial category-theoretic and braid-calculus infrastructure;
  no reliable time estimate is available yet.
