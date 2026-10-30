# Independent verification report: `PropertyF.Ground.target`

Worktree: `property-f-verify`, branch `verify/opus`, library snapshot at commit 75174961.
Toolchain: Lean 4.35.0, Mathlib v4.35.0 (all package checkouts clean at tag v4.35.0, with no local modifications).

## Verdict

The Lean theorem `PropertyF.Ground.target : TargetStatement` is a faithful formalization of Theorem 1.1 of
[the manuscript](../papers/property-f-weak-integrality/manuscript.pdf) ("a braided fusion category with property F and a pseudo-unitary Galois conjugate is
weakly integral"). The library builds from scratch, and the theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`. The kernel checker `leanchecker` independently replayed every declaration
in all 111 built project modules without error. I checked every definition in the frozen statement against the
standard (ENO/EGNO) definitions and found no critical or major deviation. The hypotheses are not contradictory:
I built in Lean a genuine instance (`Vec_ℂ` = `FGModuleCat ℂ`) of `BraidedFusionCategory`, and I built a genuine
`GaloisConjugate` with σ equal to complex conjugation (in fact for every σ and every C). Caveats, all minor:
(i) I did not formally prove in Lean that `Vec_ℂ` satisfies `PseudoUnitary` and `HasPropertyF`, although this is
mathematically clear (dimension 1, braid images are quotients of symmetric groups). (ii) Some docstrings in
`Target.lean` are stale and still describe the statement as unproved. (iii) The conjugate `D` must live in the
same universes as `C`; this is harmless because the conjugate can always be realized on the same carrier type.

## Exact Lean statement (as printed by Lean, `pp.universes true`)

```
target.{u_1, u_2} : TargetStatement.{u_1, u_2}

def PropertyF.Ground.TargetStatement.{v, u} : Prop :=
∀ (C : BraidedFusionCategory.{v, u}),
  HasPseudoUnitaryGaloisConjugate.{v, u} C →
    PropertyF.HasPropertyF.{v, u} (BraidedFusionCategory.Obj.{v, u} C) →
      PropertyF.WeaklyIntegral (globalFPDimension.{v, u} C)
```

The theorem is universe polymorphic in both the object and the morphism universe.

## Axioms

```
'PropertyF.Ground.target' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

Additionally, `lake env leanchecker PropertyF <all 111 PropertyF.* modules>` (the Lean 4.35 kernel replay tool
shipped with the toolchain) exited with status 0 after replaying all project declarations (3 min 21 s).
`PropertyF.Ground.Integrate.TargetAudit` is not part of the default build and was excluded; it only contains a
`run_cmd` check and no declarations used by `target`.

## Definition-by-definition faithfulness

All definitions are in `PropertyF/Ground/Target.lean` (T) or `PropertyF/Definitions.lean` (D). Target.lean imports
only `PropertyF.Definitions` and Mathlib; Definitions.lean declares no instances or notation, so all notation
(`⨁`, `≅`, `Simple`, `spectralRadius`, `Module.finrank`, `ᘁ`) elaborates to Mathlib constants. I confirmed this by
printing every definition with `pp.fullNames true`.

| Definition | Standard meaning | Verdict | Notes |
|---|---|---|---|
| `IsFusionCategory` (T:31) | ℂ-linear abelian rigid monoidal category, finite-dimensional Hom spaces, simple unit, semisimple with finitely many simples | Faithful | Abelian, `Linear ℂ`, `RigidCategory` (left and right duals), `MonoidalPreadditive`, `MonoidalLinear` (bilinear tensor) are Mathlib classes. `finite_semisimple`: a finite family of pairwise non-isomorphic simples such that every object is isomorphic to a finite biproduct of them. This is equivalent to semisimplicity with finitely many simple classes; every simple is isomorphic to exactly one `S i`. `End(S) = ℂ` follows from Schur over an algebraically closed field. |
| `BraidedFusionCategory` (T:43) | Bundled braided fusion category | Faithful | Instances are bundled consistently: `Linear` and `MonoidalPreadditive` use `Abelian.toPreadditive`. |
| `rank`, `simples` (T:62,64) | Number of simple classes, representatives | Faithful | Chosen by `Classical.choose`. The uniqueness clause makes `rank` the true number of simple classes. |
| `fusionMatrix` (T:68) | Left multiplication by `[S_i]` on K₀: entry (k,j) = N_{ij}^k = dim Hom(S_k, S_i ⊗ S_j) | Faithful | Column j is the class of S_i ⊗ S_j. The transpose convention would not change the spectral radius anyway. |
| `fpSimple` (T:72) | FPdim(S_i) = Perron–Frobenius eigenvalue of N_i | Faithful | Mathlib's `spectralRadius ℂ` is the supremum of norms over the (quasi)spectrum, an algebraic notion that does not depend on any matrix norm. For a non-negative matrix it equals the PF eigenvalue. Adding 0 to the quasispectrum does not change the supremum. |
| `globalFPDimension` (T:75) | FPdim(C) = Σ FPdim(S_i)² | Faithful | |
| `doubleDualIso` (T:79) | Some isomorphism X ≅ X** | Faithful (choice is irrelevant) | Uniqueness of right duals applied to the braided swap pairing (the Drinfeld isomorphism). Only used in `squaredNorm`, which does not depend on the choice for simple X (library lemma `squaredNorm_independent`, and directly visible from the definition below). |
| `unitScalar` (T:85) | The identification End(1) ≅ ℂ | Faithful | `Function.invFun (algebraMap ℂ (End 1))`. `algebraMap` is bijective because the unit is simple and Hom spaces are finite-dimensional over ℂ (proved in the library as `unit_algebraMap_bijective`). If it were not surjective, `invFun` would return junk, but this case cannot occur under the hypotheses. |
| `rightQuantumTrace`, `leftQuantumTrace` (D:66,71) | Tr(a) and Tr((a⁻¹)*) for a: X → X** | Faithful | The right trace is ev ∘ (a ⊗ id) ∘ coev. The left trace uses `j.inv`, which is exactly ENO's Tr((a⁻¹)*). Hence if a is rescaled by λ the factors scale by λ and λ⁻¹. |
| `squaredNorm` (T:88) | ENO squared norm \|X\|² = Tr(a)·Tr((a⁻¹)*) | Faithful | Independent of a for simple X. It equals d_X² for any spherical structure (library lemma `target_squaredNorm_eq_dimension_sq`). |
| `globalDimension` (T:92) | dim(C) = Σ \|S_i\|² | Faithful | |
| `PseudoUnitary` (T:94) | dim(C) = FPdim(C) | Faithful | Equality in ℂ. |
| `GaloisConjugate` (T:97) | C^σ: base change of C along a field automorphism σ | Faithful | A σ-semilinear braided monoidal equivalence C → D exists if and only if D is ℂ-linearly braided equivalent to C^σ. σ ranges over all of Aut(ℂ), including wild automorphisms. Their restrictions to Q̄ give every element of Gal(Q̄/Q), and C^σ depends only on that restriction, so this matches the paper. The notion is not trivial (it carries the twist) and not impossible for σ ≠ id: see the satisfiability section. |
| `HasPseudoUnitaryGaloisConjugate` (T:104) | Some Galois conjugate is pseudo-unitary | Faithful | Includes σ = id, which is intended. D is required to be in the same universes as C. This is harmless because `ScalarTwist.category C σ` realizes C^σ on the same carrier. |
| `tensorPower` (D:29) | X^{⊗n} | Faithful | Right-associated, with a trailing `𝟙` factor (X ⊗ (X ⊗ … ⊗ 𝟙)). This is isomorphic to the usual power and does not change the braid group image. |
| `braidGenerator` (D:35) | σ_i ↦ id^{⊗(i-1)} ⊗ c_{X,X} ⊗ id^{⊗(n-i-1)} | Faithful | Index n means n+2 strands, with generators indexed by Fin(n+1) (that is, σ_1..σ_{n+1}). The first generator is α⁻¹ ≫ (β ⊗ id) ≫ α. Higher generators are id_X ⊗ (previous generator). Associators are made explicit. |
| `braidImage` (D:47) | G_{X,n} = ρ(B_n) ⊆ Aut(X^{⊗n}) | Faithful | Subgroup generated by the generators, which equals the image of the Artin braid group. The trivial cases n = 0, 1 are omitted, and they are trivially finite. |
| `ObjectPropertyF`, `HasPropertyF` (D:52,56) | All G_{X,n} finite for all X | Faithful | `Finite` of the subgroup, quantified over all objects. |
| `WeaklyIntegral` (D:60) | FPdim(C) ∈ ℤ | Faithful | `∃ z : ℤ, globalFPDimension = z`. |

## Issues ranked by severity

**Critical:** none found.

**Major:** none found.

**Minor:**
1. `PropertyF/Ground/Target.lean:15-18,83-84,108`: the docstrings are stale. They say the identifications "still
   need proofs", call bijectivity of `algebraMap` "a pending obligation", and say "No proof is asserted here".
   The theorem is proved in `Final.lean:91`. These are documentation only.
2. `PropertyF/Ground/Target.lean:104-106`: the conjugate D must share the universes `v,u` with C. As explained
   above, this is harmless, but a reader should know the restriction exists.
3. `PropertyF/Definitions.lean:29-31`: `tensorPower X 0 = 𝟙`, so powers carry a trailing unit factor. This is
   harmless.
4. `PropertyF/Ground/Target.lean:85-86`: `unitScalar` uses `Function.invFun`. This is correct under the
   hypotheses (bijectivity is proved), but the definition is junk-valued outside them.
5. 219 occurrences of `set_option backward.isDefEq.respectTransparency false` and 28 occurrences of
   `backward.defeqAttrib.useBackward true` exist, including in `Final.lean`. These options affect only the
   elaborator, not the kernel; the leanchecker replay confirms that soundness is unaffected.

## Satisfiability evidence

The scratch file `scratch/VecExample.lean` (untracked) compiles against the built library with no errors and no
`sorry`. It proves the following:
- `Simple (𝟙_ (FGModuleCat ℂ))`, and every finite-dimensional space is isomorphic to `⨁` of copies of the unit,
  via an explicit bicone with total equal to the identity.
- `instance : IsFusionCategory (FGModuleCat ℂ)`, using Mathlib's `Abelian (FGModuleCat ℂ)`, its right rigidity
  together with `BraidedCategory.rigidCategoryOfRightRigidCategory`, its symmetric braiding, and `MonoidalLinear`.
  Hence `vec : BraidedFusionCategory.{0,1}` exists, so the class is inhabited by a genuine (non-degenerate)
  category; it cannot be the zero category because the unit must be simple.
- `conjTwist C σ : GaloisConjugate C (ScalarTwist.category C σ) σ` for every C and every σ. The identity functor
  with the library's twisted scalar action is σ-semilinear. In particular, a conjugate with σ = complex
  conjugation (`starRingAut`) exists for `vec`. So `GaloisConjugate` is satisfiable for σ ≠ id and is the
  standard C^σ construction.
- `PropertyF.Ground.target vec h hF` typechecks. This only confirms the shape of the statement.

Not formalized here, but mathematically clear: `vec` is pseudo-unitary (one simple with |𝟙|² = 1 = FPdim²) and
has property F (the braiding is the flip, so G_{X,n} is a quotient of S_n). Therefore the hypotheses of
`TargetStatement` are jointly satisfiable, and the theorem is not vacuous. More generally, every pseudo-unitary
braided fusion category, for example Rep(G) or unitary modular categories, is a model.

## Escape-hatch scan

- The `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, `opaque`, `csimp`,
  `debug.*` and `ofReduceBool` patterns have no occurrences in `PropertyF/` or `PropertyF.lean`. The only grep hits
  were the words "Kernel/Kernels" in mathematical identifiers.
- `macro`, `elab`, `syntax`, `notation` and `infix` declarations: none, except `local notation` abbreviations
  (`𝒵`, `Sₚ`, `κ`, `S`, `u`, `V`, and others) inside proof sections. None of these is in `Target.lean` or
  `Definitions.lean`, and none shadows standard notation used by the statement.
- Instance attributes: only `attribute [local instance]` for `Abelian.hasFiniteBiproducts`,
  `IsFusionCategory.hom_finite`, `IsFusionCategory.unit_simple` and `Centre.finiteDimensional_hom`. There are no
  `attribute [-instance]` declarations. `Target.lean` uses the same `Abelian.hasFiniteBiproducts` local instance
  for `⨁`; `HasBiproduct` is a `Prop`, so the choice of instance is irrelevant.
- `run_cmd`: occurs only in the audit modules (`DependencyAudit`, `ProjectAudit`, `TargetAudit`). These blocks
  read the environment and throw errors; they never call `setEnv` or `addDecl`. The `setImplementedBy` fixture
  operates on a local copy of the environment that is discarded.
- `lakefile.toml`: `moreLeanArgs = ["-j2", "-M3000"]` (threads and memory only). It has no plugins, no
  `--load-dynlib`, no precompiled modules and no extra targets. The manifest pins Mathlib v4.35.0 from the
  official repository. `scripts/*.sh` only call `lake build` with `taskset`.
- Non-Lean imports: only `Lean.Compiler.ExternAttr`, `ImplementedByAttr`, `Util.CollectAxioms` and `FoldConsts`,
  all used by the audit modules.

## Proof structure (lighter check)

`Final.lean:91` follows the paper's route:
- `positive_spherical_of_pseudoUnitary` gives a spherical structure with d = FPdim on the pseudo-unitary conjugate
  D (ENO 8.23).
- `rigidCenter`, `center_fusion_of_compatible_pivotal` and the lifted pivotal structure make Z(D) a fusion category
  with FP-valued spherical dimensions.
- `categoricalS_det_ne_zero_of_trivial_transparency` gives modularity of the centre.
- `center_globalDimension_square_of_actual_induction` gives dim Z(D) = FPdim(D)².
- `productLabels_doubleCentralizer_of_image_monodromy` and `actual_symmetricCore_integrality` (integrality of the
  symmetric core) correspond to Lemma 4.1.
- `weaklyIntegral_of_actual_center` combines `galois_rigidity_of_propertyF` (Lemma 3.2),
  `galois_fixed_of_smaller_conjugate_witness` and `integral_eq_int_of_complex_galois_fixed`.
- Property F and FPdim are transported from C to D along the conjugate (`conjugate_propertyF`,
  `conjugate_globalFPDimension`).

The internal `PivotalStructure` (natural, monoidal, unit-compatible double-dual isomorphisms) and `IsSpherical`
(left trace equals right trace) are standard. No key lemma I inspected has a vacuous statement or a degenerately
discharged hypothesis. Every intermediate hypothesis of `weaklyIntegral_of_actual_center` is produced by a
construction from D, not assumed.

## What was verified directly versus inferred

Directly verified:
- The build from a fresh `.lake/build`.
- `#print axioms`, `#check` and `#print` output.
- The leanchecker kernel replay of all project modules.
- The full-name elaboration of every statement definition.
- The grep scans, and the lakefile, manifest and package cleanliness.
- The Lean construction of the `Vec_ℂ` instance and of the semilinear Galois conjugates.

Inferred by mathematical reading:
- That `squaredNorm`, `fpSimple` and `GaloisConjugate` coincide with the ENO notions.
- That `Vec_ℂ` is pseudo-unitary and has property F.
- The faithfulness of the intermediate proof steps, which was only skimmed.
