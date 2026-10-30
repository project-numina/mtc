> Written on 2026-10-28, before the conjecture libraries were added; paths refer to `PropertyF/`.

# Architecture migration plan

This is a proposed follow-up, not a change made in this review. `PropertyF/Ground/Target.lean` is frozen: preserve its path and bytes, all names and imports it uses, and `PropertyF.Ground.target : PropertyF.Ground.TargetStatement`. The table is the target for one-to-one file placement, not a claim that moving files alone fixes layering. Splits and upstream PRs are later tasks; retain the listed destination as the owner of each original declaration until it has been deliberately extracted. Estimated effort is engineering time, not a guarantee or a build-time estimate.

## Target layout

```text
PropertyF.lean                         -- small, documented umbrella
PropertyF/
  Definitions.lean                    -- compatibility boundary for frozen import
  Ground/Target.lean                  -- frozen, intentionally exceptional
  Algebra/                            -- arithmetic, matrices, braid algebra
  CategoryTheory/Rigid/               -- duality, pivotal structures, traces
  CategoryTheory/Trace/               -- partial traces
  Fusion/                             -- simples, rules, FP dimension, scalars
  Fusion/Dimension/                   -- fusion-specific categorical dimensions
  Braid/Cabling/                      -- tensor powers and braid-image transfer
  Braid/Trace/                        -- overlap and three-strand trace arguments
  Center/                             -- Mathlib's Drinfeld center and its properties
  Center/Embeddings/                  -- positive and negative images
  Center/Fusion/                      -- fusion structure and bundled center
  Center/Induction/                   -- adjunction, transparency, pivotal lifting
  Center/Centralizer/                 -- centralizer and image constructions
  Modular/                            -- S matrix, transport, balancing, Vafa
  Symmetric/Permutation/              -- type-A and permutation arguments
  Symmetric/Trace/                    -- trace/projector arguments
  Theorem/                            -- Galois rigidity, center reduction, final theorem
  Audit/                              -- audit modules, independently invoked
```

In the final architecture, generic category theory and algebra should not import fusion, center modularity or the theorem; fusion may use generic algebra and category theory; center construction may use fusion; modularity may use fusion and center results where mathematically required; the paper proof sits above those layers. Braids and generic center facts are parallel branches, not an artificial strictly linear chain. In particular the current `DualTensorNaturality` imports the frozen target and `DoubleDualMonoidal` imports a fusion-dependent file: the mapped generic destinations are aspirational until their generic sections are extracted and verified independently. No module may be labeled low-level solely because it has moved there.

## Namespace and naming policy

* A path move does not by itself rename declarations. First retain all existing namespaces, including `PropertyF.Ground.*`, to keep downstream consumers and audit fixtures stable. The frozen target's `PropertyF.Ground` declarations, `PropertyF` declarations it imports, its statement type, and the final theorem's current name remain permanent compatibility names while the freeze holds.
* After placement, add a coherent API in `PropertyF.Fusion`, `PropertyF.Braid`, `PropertyF.Center`, `PropertyF.Modular`, `PropertyF.Symmetric`, and `PropertyF.Theorem`, with old declarations kept as compatibility aliases where appropriate. General category-theory declarations should ultimately live under `CategoryTheory` only after collision and upstream review; do not introduce a second `Center` construction. Namespace paths do not need to exactly mirror file paths, but document intentional differences. Keep `PivotalStructure` explicit and `IsSpherical` a property of it until multiple structures and instances have been evaluated. Use Mathlib `rightDual`, `ᘁ`, `ExactPairing`, `Center`, and its functor conventions.
* Where the old audit checks exact fully qualified names, retain them or update the gate and its negative/positive fixtures atomically. Namespace migration must not rename or evade forbidden fixtures. Stable names for the frozen statement are not removable aliases. A later explicit approval is required for any modification of the target statement or file.
* Use short scoped `open` commands, `section`/`variable` blocks matching assumptions and `omit` for more general results; do not rewrite every open merely for appearance. Add targeted characteristic `simp`/`reassoc` lemmas after checking orientation, termination, ambiguity and downstream elaboration.

| Current term | Proposed term | Scope and compatibility |
|---|---|---|
| `Ground` | `Fusion`, `Theorem`, or category-specific namespace | Only nonfrozen APIs; retain original target names |
| `Centre`, `CentreInduction`, `CentreCabling`, `CentreModular` | `Center`, `Center.Induction`, `Center.Centralizer`, `Modular` | Match Mathlib spelling; maintain old aliases |
| `CentreCalculus` | `Symmetric.Trace` or `Center.Centralizer` | Assign by declaration, not by old owner |
| `CentreDimensions.PivotalTwist` | `Modular.PivotalTwist` | Generic trace lemmas may later be extracted |
| `CentreIntegrate.TwistBalancing` | `Modular.TwistBalancing` | Existing namespace preserved first |
| `Integrate.ActualCenterReduction` | `Theorem.CenterReduction` | Later split arithmetic and witness sections |
| `Integrate.TwistedRigidity` | `Theorem.GaloisRigidity` | Scalar-twist construction can be extracted separately |
| `Dimensions.GroundNorm` | `Fusion.Dimension.SquaredNorm` | Do not rename the frozen `squaredNorm` definition |
| `Fusion.Agreement` | `Fusion.Agreement` initially; later `FPDimension` | Existing name reflects proof work, later split matrix lemmas |
| `Final` | `Theorem.Final` | Keep `PropertyF.Ground.target` and its exact type |
| `rightDualObject` | `Xᘁ` / Mathlib `rightDual` API | Deprecate only after all uses and compatibility are checked |

## Independent workstreams and integration

Ownership below is disjoint for all current files, including the frozen exceptions. It is ownership of source edits and proposed destinations; **A alone owns** `PropertyF.lean`, `Definitions.lean`, frozen `Target.lean`, audit modules, scripts, lake configuration and shared documentation. All agents work from a common integration base and submit patches to A; they do not edit another owner's files. An agent may create a destination corresponding to its own source. A owns cross-workstream import rewrites and commits them only when integrating that workstream; therefore agents provide a manifest of required edits rather than changing other owners' files. The frozen target has no editor, including A. Parallel analysis and isolated preparation are possible; only one `lake build` or audit may run on the machine at a time, coordinated by A. Never update packages, clean, retrieve caches, or touch other worktrees. All Lean processes use `taskset -c 24-27` and `LEAN_NUM_THREADS=4`.

| Owner | Disjoint scope | Deliverable | Estimate |
|---|---|---|---|
| A | Root, frozen compatibility boundary, all three audit files, `scripts/`, lake and documentation | Gates, inventory generation, integration, roadmap and documentation repair | 3–5 days plus integration |
| B | Algebra, cabling, braid trace files listed in map | Braid/linear algebra modules; identify and extract generic lemmas without moving frozen definitions | 3–5 days |
| C | Fusion, fusion dimension and assigned `Integrate` files | Separately expose simples, FP/characters, unit scalar and squared norm; isolate ENO-specific arguments | 5–8 days |
| D | Assigned generic rigid/trace files | Align Mathlib dual functors and extract foundational pivotal/trace API from fusion dependencies | 4–7 days |
| E | Center, embeddings, induction, fusion and centralizers | Coherent center hierarchy, generic structure versus fusion-specific files, instance overlap review | 6–10 days |
| F | Symmetric, permutation and projector/trace arguments | Collect exterior-power and symmetric-core proofs, delineate general algebra | 3–5 days |
| G | Modular, Vafa, twist and assigned center modular files | Organize S-matrix and modularity, separate generic monodromy from fusion; split large Vafa only after placement | 4–7 days |
| H | Final theorem, Galois rigidity and center reduction | Paper-to-Lean roadmap and staged reduction; explain hypotheses of each bridge | 2–4 days |

Dependencies constrain integration, not analysis ownership: land A's audit/compatibility protocol first; then B and D; then C (requiring relevant foundations); then E/F/G in dependency order determined from the actual DAG; then H and A's final umbrella/docs. E, F and G can prepare simultaneously but their integrations are serialized and rebased by their owners without rewriting shared history. These estimates include normal proof elaboration work but exclude an upstream Mathlib submission and a frozen-statement revision.

### Atomic migration and acceptance gates

1. Record the exact frozen file hash, current theorem type, full `import all` inventory, audit forbidden names and positive/negative fixtures. Make each change a small commit on an integration branch; keep the project building at every committed integration point.
2. For each moved module, create the destination with the original declarations and leave the old module as a compatibility shim importing it. For modules appearing in audits, add **both** the new module and any retained shim to both audit `import all` lists; `import all` of a shim alone does not guarantee inspection of the moved module's private bodies. Update import coverage checker and target-audit module exclusion when audit files themselves move. Do not introduce duplicate declarations by compiling old and new copies. Preserve `public import` behavior and review Lean's module visibility rather than assuming a textual import substitution is sufficient.
3. As a single integration patch, A updates shared root imports, the scripts and audit inventories required by the move; each owner updates only its own files. A generates an inventory from the filesystem, compares missing **and extra** entries, and retains the existing forbidden-cone and fixture checks. Where a destination has not landed, shims remain. Remove a shim only in a later reviewed compatibility change after all clients, root, and audits have moved.
4. After **every integration change**, in strict sequence run `taskset -c 24-27 env LEAN_NUM_THREADS=4 lake build PropertyF`, then `taskset -c 24-27 env LEAN_NUM_THREADS=4 PROPERTYF_AUDIT_CORES=24-27 scripts/audit-target.sh`. Check that the logged axiom list is exactly `[propext, Classical.choice, Quot.sound]`, not merely a subset. Compare the frozen hash, theorem type and audit fixtures; stop and repair any failure before committing or integrating another stream. If the root stops importing `ProjectAudit`, add a sequential `taskset -c 24-27 env LEAN_NUM_THREADS=4 lake build PropertyF.Audit.ProjectAudit` to this gate so the project-wide axiom scan and fixtures still run; retain the target audit as a separate target. Do not run concurrent builds.
5. For each proposed split, extract a generic section with minimum imports into a new module, import it from the existing destination and re-export names as needed. Measure project import cone and representative compile times again; run the same gates. Only then delete redundant imports, after checking public visibility. Moves and splits are not assumed to improve compilation time.
6. Rewrite README, FORMALIZATION, root and top-level theorem docstrings from current declarations and the paper map. Mark old style and agent status material as dated evidence or remove it only after its archival decision. Check all documentation links and distinguish proved results from conditional helper lemmas. Audit output snapshots must identify the exact commit and command.
7. Upstream small independent lemmas first, then foundational rigid/trace and center pieces, then fusion/FP machinery. Generalize and test in separate upstream work; this plan does not require modifying `.lake/packages/mathlib`.

## Complete file mapping

Every currently tracked project Lean module, including the root, appears once. The right column identifies its sole owner. This table specifies physical destination; namespace changes and later splits follow the policy above. Compatibility shims at old paths remain until separately reviewed. New modules created by extraction are additional files, not omissions from this inventory.

| Current file | Destination | Owner |
|---|---|---|
| `PropertyF.lean` | `PropertyF.lean` | A |
| `PropertyF/Arithmetic.lean` | `PropertyF/Algebra/Arithmetic.lean` | B |
| `PropertyF/BlockTrace.lean` | `PropertyF/Algebra/BlockTrace.lean` | B |
| `PropertyF/BraidAlgebra.lean` | `PropertyF/Algebra/BraidAlgebra.lean` | B |
| `PropertyF/CenterBasics.lean` | `PropertyF/Center/Embeddings/Basic.lean` | E |
| `PropertyF/Definitions.lean` | `PropertyF/Definitions.lean` | A |
| `PropertyF/Ground/Cabling/Generated.lean` | `PropertyF/Braid/Cabling/Generated.lean` | B |
| `PropertyF/Ground/Cabling/Naturality.lean` | `PropertyF/Braid/Cabling/Naturality.lean` | B |
| `PropertyF/Ground/Cabling/Strands.lean` | `PropertyF/Braid/Cabling/Strands.lean` | B |
| `PropertyF/Ground/Cabling/UnitPower.lean` | `PropertyF/Braid/Cabling/UnitPower.lean` | B |
| `PropertyF/Ground/Calculus/BraidWeights.lean` | `PropertyF/Braid/Trace/BraidWeights.lean` | B |
| `PropertyF/Ground/Calculus/EndBlocks.lean` | `PropertyF/Braid/Trace/EndBlocks.lean` | B |
| `PropertyF/Ground/Calculus/OverlapBound.lean` | `PropertyF/Braid/Trace/OverlapBound.lean` | B |
| `PropertyF/Ground/Calculus/OverlapCoherence.lean` | `PropertyF/Braid/Trace/OverlapCoherence.lean` | B |
| `PropertyF/Ground/Calculus/PartialTrace.lean` | `PropertyF/CategoryTheory/Trace/Partial.lean` | D |
| `PropertyF/Ground/Calculus/PositiveWeights.lean` | `PropertyF/Braid/Trace/PositiveWeights.lean` | B |
| `PropertyF/Ground/Calculus/RightStrand.lean` | `PropertyF/Braid/Trace/RightStrand.lean` | B |
| `PropertyF/Ground/Calculus/TensorPowerCoherence.lean` | `PropertyF/Braid/Trace/TensorPowerCoherence.lean` | B |
| `PropertyF/Ground/Calculus/ThreeRigidity.lean` | `PropertyF/Braid/Trace/ThreeRigidity.lean` | B |
| `PropertyF/Ground/Calculus/ThreeTrace.lean` | `PropertyF/Braid/Trace/ThreeTrace.lean` | B |
| `PropertyF/Ground/Calculus/UnitaryBlocks.lean` | `PropertyF/Braid/Trace/UnitaryBlocks.lean` | B |
| `PropertyF/Ground/Centre/Abelian.lean` | `PropertyF/Center/Abelian.lean` | E |
| `PropertyF/Ground/Centre/Averaging.lean` | `PropertyF/Symmetric/Averaging.lean` | F |
| `PropertyF/Ground/Centre/Basic.lean` | `PropertyF/Center/Basic.lean` | E |
| `PropertyF/Ground/Centre/Calculus/TypeA.lean` | `PropertyF/Symmetric/Permutation/TypeA.lean` | F |
| `PropertyF/Ground/Centre/Calculus/TypeANormalWords.lean` | `PropertyF/Symmetric/Permutation/TypeANormalWords.lean` | F |
| `PropertyF/Ground/Centre/Modular/Vafa.lean` | `PropertyF/Modular/Vafa.lean` | G |
| `PropertyF/Ground/Centre/Product.lean` | `PropertyF/Center/Embeddings/Product.lean` | E |
| `PropertyF/Ground/Centre/ProductClosure.lean` | `PropertyF/Center/Embeddings/ProductClosure.lean` | E |
| `PropertyF/Ground/Centre/ProductImages.lean` | `PropertyF/Center/Embeddings/ProductImages.lean` | E |
| `PropertyF/Ground/Centre/Rigid.lean` | `PropertyF/Center/Rigid.lean` | E |
| `PropertyF/Ground/Centre/SymmetricIntegrality.lean` | `PropertyF/Symmetric/SymmetricIntegrality.lean` | F |
| `PropertyF/Ground/CentreBundle/Fusion.lean` | `PropertyF/Center/Fusion/Fusion.lean` | E |
| `PropertyF/Ground/CentreCabling/CentralityClosure.lean` | `PropertyF/Center/Centralizer/CentralityClosure.lean` | E |
| `PropertyF/Ground/CentreCabling/ImageCore.lean` | `PropertyF/Center/Centralizer/ImageCore.lean` | E |
| `PropertyF/Ground/CentreCabling/RegularSupport.lean` | `PropertyF/Center/Centralizer/RegularSupport.lean` | E |
| `PropertyF/Ground/CentreCabling/TraceSaturation.lean` | `PropertyF/Center/Centralizer/TraceSaturation.lean` | E |
| `PropertyF/Ground/CentreCabling/TwistFinite.lean` | `PropertyF/Center/Centralizer/TwistFinite.lean` | E |
| `PropertyF/Ground/CentreCalculus/BraidRelations.lean` | `PropertyF/Symmetric/Trace/BraidRelations.lean` | F |
| `PropertyF/Ground/CentreCalculus/LeftTensorTrace.lean` | `PropertyF/Symmetric/Trace/LeftTensorTrace.lean` | F |
| `PropertyF/Ground/CentreCalculus/ParityDeletion.lean` | `PropertyF/Symmetric/Trace/ParityDeletion.lean` | F |
| `PropertyF/Ground/CentreCalculus/PermutationInsert.lean` | `PropertyF/Symmetric/Trace/PermutationInsert.lean` | F |
| `PropertyF/Ground/CentreCalculus/ProjectorReduction.lean` | `PropertyF/Symmetric/Trace/ProjectorReduction.lean` | F |
| `PropertyF/Ground/CentreCalculus/TwistSign.lean` | `PropertyF/Symmetric/Trace/TwistSign.lean` | F |
| `PropertyF/Ground/CentreDimensions/PivotalTwist.lean` | `PropertyF/Modular/PivotalTwist.lean` | G |
| `PropertyF/Ground/CentreInduction/ActualFusion.lean` | `PropertyF/Center/Induction/ActualFusion.lean` | E |
| `PropertyF/Ground/CentreInduction/AdjunctionAssembly.lean` | `PropertyF/Center/Induction/AdjunctionAssembly.lean` | E |
| `PropertyF/Ground/CentreInduction/BasisPairing.lean` | `PropertyF/Center/Induction/BasisPairing.lean` | E |
| `PropertyF/Ground/CentreInduction/CrossingBlocks.lean` | `PropertyF/Center/Induction/CrossingBlocks.lean` | E |
| `PropertyF/Ground/CentreInduction/CrossingCoherence.lean` | `PropertyF/Center/Induction/CrossingCoherence.lean` | E |
| `PropertyF/Ground/CentreInduction/CrossingUnit.lean` | `PropertyF/Center/Induction/CrossingUnit.lean` | E |
| `PropertyF/Ground/CentreInduction/DrinfeldTheorem.lean` | `PropertyF/Center/Induction/DrinfeldTheorem.lean` | E |
| `PropertyF/Ground/CentreInduction/FiniteSimples.lean` | `PropertyF/Center/Induction/FiniteSimples.lean` | E |
| `PropertyF/Ground/CentreInduction/ForgetDual.lean` | `PropertyF/Center/Induction/ForgetDual.lean` | E |
| `PropertyF/Ground/CentreInduction/ForgetDualTensor.lean` | `PropertyF/Center/Induction/ForgetDualTensor.lean` | E |
| `PropertyF/Ground/CentreInduction/PivotalCentrality.lean` | `PropertyF/Center/Induction/PivotalCentrality.lean` | E |
| `PropertyF/Ground/CentreInduction/PositivePivotal.lean` | `PropertyF/Center/Induction/PositivePivotal.lean` | E |
| `PropertyF/Ground/CentreInduction/Representatives.lean` | `PropertyF/Center/Induction/Representatives.lean` | E |
| `PropertyF/Ground/CentreInduction/SecondTriangle.lean` | `PropertyF/Center/Induction/SecondTriangle.lean` | E |
| `PropertyF/Ground/CentreIntegrate/TwistBalancing.lean` | `PropertyF/Modular/TwistBalancing.lean` | G |
| `PropertyF/Ground/CentreModular/TransparencyCriterion.lean` | `PropertyF/Modular/TransparencyCriterion.lean` | G |
| `PropertyF/Ground/Dimensions/BiproductTrace.lean` | `PropertyF/CategoryTheory/Rigid/BiproductTrace.lean` | D |
| `PropertyF/Ground/Dimensions/DefectExtension.lean` | `PropertyF/Fusion/Dimension/DefectExtension.lean` | C |
| `PropertyF/Ground/Dimensions/DefectNaturality.lean` | `PropertyF/Fusion/Dimension/DefectNaturality.lean` | C |
| `PropertyF/Ground/Dimensions/DimensionCharacter.lean` | `PropertyF/Fusion/Dimension/DimensionCharacter.lean` | C |
| `PropertyF/Ground/Dimensions/DoubleDualMonoidal.lean` | `PropertyF/CategoryTheory/Rigid/DoubleDualMonoidal.lean` | D |
| `PropertyF/Ground/Dimensions/DoubleDualPairing.lean` | `PropertyF/Fusion/Dimension/DoubleDualPairing.lean` | C |
| `PropertyF/Ground/Dimensions/DoubleDualUnitTensor.lean` | `PropertyF/Fusion/Dimension/DoubleDualUnitTensor.lean` | C |
| `PropertyF/Ground/Dimensions/DualBraiding.lean` | `PropertyF/CategoryTheory/Rigid/DualBraiding.lean` | D |
| `PropertyF/Ground/Dimensions/DualCoherence.lean` | `PropertyF/CategoryTheory/Rigid/DualCoherence.lean` | D |
| `PropertyF/Ground/Dimensions/DualTensorNaturality.lean` | `PropertyF/CategoryTheory/Rigid/DualTensorNaturality.lean` | D |
| `PropertyF/Ground/Dimensions/ENOMatrices.lean` | `PropertyF/Fusion/Dimension/ENOMatrices.lean` | C |
| `PropertyF/Ground/Dimensions/ENOReciprocity.lean` | `PropertyF/Fusion/Dimension/ENOReciprocity.lean` | C |
| `PropertyF/Ground/Dimensions/FourthDualUnit.lean` | `PropertyF/Fusion/Dimension/FourthDualUnit.lean` | C |
| `PropertyF/Ground/Dimensions/FourthTensorUnit.lean` | `PropertyF/Fusion/Dimension/FourthTensorUnit.lean` | C |
| `PropertyF/Ground/Dimensions/GroundNorm.lean` | `PropertyF/Fusion/Dimension/SquaredNorm.lean` | C |
| `PropertyF/Ground/Dimensions/MonodromyTensorCap.lean` | `PropertyF/Fusion/Dimension/MonodromyTensorCap.lean` | C |
| `PropertyF/Ground/Dimensions/MultiplicityDefect.lean` | `PropertyF/Fusion/Dimension/MultiplicityDefect.lean` | C |
| `PropertyF/Ground/Dimensions/Pivotal.lean` | `PropertyF/CategoryTheory/Rigid/Pivotal.lean` | D |
| `PropertyF/Ground/Dimensions/RootDualLabel.lean` | `PropertyF/Fusion/Dimension/RootDualLabel.lean` | C |
| `PropertyF/Ground/Dimensions/SimpleHomBasis.lean` | `PropertyF/Fusion/Dimension/SimpleHomBasis.lean` | C |
| `PropertyF/Ground/Dimensions/SimpleScalars.lean` | `PropertyF/Fusion/Dimension/SimpleScalars.lean` | C |
| `PropertyF/Ground/Dimensions/TensorExtension.lean` | `PropertyF/Fusion/Dimension/TensorExtension.lean` | C |
| `PropertyF/Ground/Dimensions/TensorMultiplicativity.lean` | `PropertyF/CategoryTheory/Rigid/TensorMultiplicativity.lean` | D |
| `PropertyF/Ground/Dimensions/Trace.lean` | `PropertyF/CategoryTheory/Rigid/Trace.lean` | D |
| `PropertyF/Ground/Final.lean` | `PropertyF/Theorem/Final.lean` | H |
| `PropertyF/Ground/Fusion/Agreement.lean` | `PropertyF/Fusion/Agreement.lean` | C |
| `PropertyF/Ground/Fusion/Multiplicity.lean` | `PropertyF/Fusion/Multiplicity.lean` | C |
| `PropertyF/Ground/Fusion/ObjectDimension.lean` | `PropertyF/Fusion/ObjectDimension.lean` | C |
| `PropertyF/Ground/Fusion/Reciprocity.lean` | `PropertyF/Fusion/Reciprocity.lean` | C |
| `PropertyF/Ground/Fusion/SemisimpleSplit.lean` | `PropertyF/Fusion/SemisimpleSplit.lean` | C |
| `PropertyF/Ground/Fusion/Simples.lean` | `PropertyF/Fusion/Simples.lean` | C |
| `PropertyF/Ground/Fusion/SpectralIntegral.lean` | `PropertyF/Fusion/SpectralIntegral.lean` | C |
| `PropertyF/Ground/Fusion/UnitPower.lean` | `PropertyF/Fusion/UnitPower.lean` | C |
| `PropertyF/Ground/Integrate/ActualCenterReduction.lean` | `PropertyF/Theorem/CenterReduction.lean` | H |
| `PropertyF/Ground/Integrate/CenterBundle.lean` | `PropertyF/Center/Fusion/Bundle.lean` | E |
| `PropertyF/Ground/Integrate/CharacterReality.lean` | `PropertyF/Fusion/CharacterReality.lean` | C |
| `PropertyF/Ground/Integrate/DependencyAudit.lean` | `PropertyF/Audit/DependencyAudit.lean` | A |
| `PropertyF/Ground/Integrate/ProjectAudit.lean` | `PropertyF/Audit/ProjectAudit.lean` | A |
| `PropertyF/Ground/Integrate/TargetAudit.lean` | `PropertyF/Audit/TargetAudit.lean` | A |
| `PropertyF/Ground/Integrate/TwistedRigidity.lean` | `PropertyF/Theorem/GaloisRigidity.lean` | H |
| `PropertyF/Ground/Integrate/UnitScalar.lean` | `PropertyF/Fusion/UnitScalar.lean` | C |
| `PropertyF/Ground/Modular/BraidFunctor.lean` | `PropertyF/Modular/BraidFunctor.lean` | G |
| `PropertyF/Ground/Modular/BraidIso.lean` | `PropertyF/Modular/BraidIso.lean` | G |
| `PropertyF/Ground/Modular/CharacterStar.lean` | `PropertyF/Modular/CharacterStar.lean` | G |
| `PropertyF/Ground/Modular/Classification.lean` | `PropertyF/Modular/Classification.lean` | G |
| `PropertyF/Ground/Modular/FusionTransport.lean` | `PropertyF/Modular/FusionTransport.lean` | G |
| `PropertyF/Ground/Modular/SAdditivity.lean` | `PropertyF/Modular/SAdditivity.lean` | G |
| `PropertyF/Ground/Modular/SMatrix.lean` | `PropertyF/Modular/SMatrix.lean` | G |
| `PropertyF/Ground/Modular/SSquare.lean` | `PropertyF/Modular/SSquare.lean` | G |
| `PropertyF/Ground/Modular/Verlinde.lean` | `PropertyF/Modular/Verlinde.lean` | G |
| `PropertyF/Ground/Target.lean` | `PropertyF/Ground/Target.lean` | A |
| `PropertyF/PowerBound.lean` | `PropertyF/Algebra/PowerBound.lean` | B |
