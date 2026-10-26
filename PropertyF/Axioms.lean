module
public import PropertyF.BlockTrace
public import PropertyF.Definitions
public import PropertyF.CenterBasics
public import Mathlib.CategoryTheory.Monoidal.Center
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.GroupTheory.Index

/-!
# Explicit interfaces and standard inputs

There are no global `axiom` declarations in this file. Every unproved input is a
field of a named structure and therefore an explicit parameter of any result
using it. See FORMALIZATION.md: absence of `sorryAx` is not evidence that these
interfaces have been constructed for fusion categories.
-/

@[expose] public noncomputable section
open scoped BigOperators
open CategoryTheory
namespace PropertyF
universe v u

/-- Multiplicities in a simultaneous semisimple decomposition. The finite
Wedderburn decomposition of a finite group representation is standard Maschke /
Artin–Wedderburn theory, as used in the first paragraph of paper Lemma 3.2.
The categorical bound is [ENO, §8, especially 8.21]. These fields do not assert
any trace bound. -/
structure MultiplicityData (B : Blocks) where
  simpleCount : ℕ
  dimension : Fin simpleCount → ℝ
  fpDimension : Fin simpleCount → ℝ
  multiplicity : Fin simpleCount → Fin B.count → ℕ
  dimension_bound : ∀ W, |dimension W| ≤ fpDimension W

namespace MultiplicityData

def weight {B : Blocks} (M : MultiplicityData B) (r : Fin B.count) : ℝ :=
  ∑ W, (M.multiplicity W r : ℝ) * M.dimension W

def fpMass {B : Blocks} (M : MultiplicityData B) : ℝ :=
  ∑ r, (∑ W, (M.multiplicity W r : ℝ) * M.fpDimension W) * B.size r

end MultiplicityData

/-- Primitive spherical partial-trace laws for copies overlapping in one strand.
`stage k` represents `(k+1)(m-1)+1` strands. `source` is stage zero.

The two embeddings tensor with identities, hence are star algebra maps after
finite-group averaging. `partial_left` is the standard bimodule identity for
partial trace. `partial_right` is Schur's lemma for the simple surviving strand,
with its scalar determined by total trace. These are structural inputs, not
Lemma 3.1: the iterated product, trace recurrence, trace estimate and asymptotic
argument are proved separately. Spherical graphical calculus: [EGNO, §§4.7–4.8].

UNCONSTRUCTED BRIDGE: this structure is not yet obtained from a Mathlib braided
category and a finite braid-image hypothesis. -/
structure OverlapModel (d f : ℝ) (m : ℕ) where
  stage : ℕ → Blocks
  decomposition : ∀ k, MultiplicityData (stage k)
  fpMass_eq : ∀ k, (decomposition k).fpMass = f ^ ((k + 1) * (m - 1) + 1)
  left : ∀ k, (stage k).Algebra →⋆ₐ[ℂ] (stage (k + 1)).Algebra
  right : ∀ k, (stage 0).Algebra →⋆ₐ[ℂ] (stage (k + 1)).Algebra
  partialTrace : ∀ k, (stage (k + 1)).Algebra →ₗ[ℂ] (stage k).Algebra
  trace_partial : ∀ k v,
    (stage k).trace (decomposition k).weight (partialTrace k v) =
      (stage (k + 1)).trace (decomposition (k + 1)).weight v
  partial_left : ∀ k v t, partialTrace k (left k v * t) = v * partialTrace k t
  partial_right : ∀ k u, partialTrace k (right k u) =
    ((stage 0).trace (decomposition 0).weight u / (d : ℂ)) • 1

/-- Finite modular data with the *standard* Galois action on normalized columns.
[EGNO, 8.13.11 and 8.14.2]. The unnormalized S-square identity and character
permutation are inputs. The dimension identity and self-duality of the Galois
image of the unit (paper Proposition 2.1) are not fields; they are proved.
We use automorphisms of ℂ; restricting them to algebraic scalars gives the paper's
automorphisms of Qbar. -/
structure ModularData where
  rank : ℕ
  unit : Fin rank
  dual : Fin rank → Fin rank
  dimension : Fin rank → ℂ
  globalDimension : ℂ
  S : Matrix (Fin rank) (Fin rank) ℂ
  dimension_ne_zero : ∀ X, dimension X ≠ 0
  global_ne_zero : globalDimension ≠ 0
  global_eq : globalDimension = ∑ X, dimension X ^ 2
  S_symmetric : ∀ X Y, S X Y = S Y X
  S_unit : ∀ X, S X unit = dimension X
  unit_dimension : dimension unit = 1
  S_square : ∀ X Y, ∑ Z, S X Z * S Z Y =
    if X = dual Y then globalDimension else 0
  galoisLabel : (ℂ ≃+* ℂ) →* Equiv.Perm (Fin rank)
  galois_character : ∀ (τ : ℂ ≃+* ℂ) X Y,
    τ (S X Y / dimension Y) = S X (galoisLabel τ Y) / dimension (galoisLabel τ Y)

/-- Primitive two- and three-strand graphical calculus. These are the ordinary
spherical partial-trace identities [EGNO §§4.7–4.8], a representation of the
three-strand braid relation, and finite order of the squared braiding. They do
not assert centrality, trace saturation, or Galois rigidity.

UNCONSTRUCTED: realization from categorical braiding and finite braid images. -/
structure ThreeStrandModel (d f : ℝ) where
  overlap : OverlapModel d f 3
  pair : Blocks
  pair_nonzero : ∃ r, 0 < pair.size r
  cSquared : pair.Algebraˣ
  a : (overlap.stage 0).Algebraˣ
  b : (overlap.stage 0).Algebraˣ
  braid_relation : a * b * a = b * a * b
  a_unitary : (overlap.stage 0).IsUnitary (a : (overlap.stage 0).Algebra)
  b_unitary : (overlap.stage 0).IsUnitary (b : (overlap.stage 0).Algebra)
  leftPair : pair.Algebra →ₐ[ℂ] (overlap.stage 0).Algebra
  rightPair : pair.Algebra →ₐ[ℂ] (overlap.stage 0).Algebra
  left_cSquared : leftPair cSquared = (a ^ 2 : (overlap.stage 0).Algebraˣ)
  right_cSquared : rightPair cSquared = (b ^ 2 : (overlap.stage 0).Algebraˣ)
  pairTrace : pair.Algebra →ₗ[ℂ] ℂ
  simplePartial : pair.Algebra →ₗ[ℂ] ℂ
  pair_trace_partial : ∀ T, pairTrace T = (d : ℂ) * simplePartial T
  thirdPartial : (overlap.stage 0).Algebra →ₗ[ℂ] pair.Algebra
  trace_third : ∀ T, pairTrace (thirdPartial T) =
    (overlap.stage 0).trace (overlap.decomposition 0).weight T
  third_left : ∀ T, thirdPartial (leftPair T) = (d : ℂ) • T
  third_right : ∀ T, thirdPartial (rightPair T) = simplePartial T • 1
  third_bimodule : ∀ T U, thirdPartial (leftPair T * U) = T * thirdPartial U
  finite_order : ∃ n : ℕ, n ≠ 0 ∧ cSquared ^ n = 1

/-- Concrete witness that one image group is a quotient of a subgroup of a
product. In the centre this is supplied by the dominant braided product functor
[EGNO 8.6.1], restriction to summands and naturality of braiding. No finiteness
is asserted; the finite-image consequence is proved in Center.lean. -/
structure ProductImageWitness (G H K : Type*) [Group G] [Group H] [Group K] where
  subgroup : Subgroup (G × H)
  map : subgroup →* K
  surjective : Function.Surjective map

/-- Standard finite-group averaging / Wedderburn realization, together with the
spherical trace calculus for a specified simple object after Galois transport.
The S-matrix entry is the definition of the double-braiding trace [EGNO 8.13].
All numerical arguments from this data are proved in GaloisRigidity.lean. -/
structure ThreeStrandRealization (d f : ℝ) (σ : ℂ ≃+* ℂ) (SYY : ℂ) where
  model : ThreeStrandModel d f
  positive : ∀ W, 0 < (model.overlap.decomposition 0).fpDimension W
  transport : ∀ W, σ ((model.overlap.decomposition 0).fpDimension W : ℂ) =
    ((model.overlap.decomposition 0).dimension W : ℂ)
  retained : ∀ r, ∃ W, 0 < (model.overlap.decomposition 0).multiplicity W r
  trace_formula : model.pairTrace model.cSquared = σ SYY

/-- Standard centre inputs. Sources:
* canonical positive dimensions and dimension bounds: [ENO 8.21, 8.23];
* centre modularity and squared global dimension: [EGNO 7.16.6, 8.20.14, 9.3.4];
* integrality of the symmetric core, and preservation of dimensions by the
  forgetful functor: [DGNO 2.46], [ENO §8];
* S-matrix centralizer criterion and double centralizer: [EGNO 8.20.5, 8.21.1];
* the dominant product functor: [EGNO 8.6.1].

The two construction bridges `product_witness` and `realize` are explicitly
unproved. They describe morphisms / matrix realizations, not Lemma 4.1 or
Lemma 3.2 as conclusions. Their absence from `#print axioms` is not evidence
that Mathlib constructs them. -/
structure CenterInputs (C : BraidedFusionCategory.{v,u}) where
  data : ModularData
  object : Fin data.rank → CategoryTheory.Center C.Obj
  dim : Fin data.rank → ℝ
  dimension_real : ∀ Y, data.dimension Y = (dim Y : ℂ)
  positive : ∀ Y, 0 < dim Y
  at_least_one : ∀ Y, 1 ≤ dim Y
  conjugate_real : ∀ (σ : ℂ ≃+* ℂ) Y,
    (((σ (data.dimension Y)).re : ℝ) : ℂ) = σ (data.dimension Y)
  global_square : data.globalDimension = (C.fusion.globalFPDimension : ℂ) ^ 2
  generated : Set (Fin data.rank)
  symmetric_integrality : ∀ X, Transparent (object X).1 →
    ∃ z : ℤ, data.dimension X = z
  double_centralizer : ∀ Y, (∀ X, CentralizesPositive (object X) →
    CentralizesNegative (object X) → data.S X Y = data.dimension X * data.dimension Y) →
    Y ∈ generated
  product_witness : ∀ Y, Y ∈ generated → ∀ n, ∃ X Z : C.Obj,
    Nonempty (ProductImageWitness (braidImage X n) (braidImage Z n) (braidImage (object Y) n))
  realize : ∀ (σ : ℂ ≃+* ℂ) Y, ObjectPropertyF (object Y) →
    Nonempty (ThreeStrandRealization (σ (data.dimension Y)).re (dim Y) σ (data.S Y Y))

/-- A finite normal field containing the global dimension and extensions of its
Galois automorphisms to complex field automorphisms. Standard number-field descent
[ENO 2.30, 2.33], algebraic integrality [ENO §8], and normal-closure / extension
of embeddings from field theory. Integrality of a fixed element is *proved*
from this interface in Arithmetic.lean, rather than assumed. -/
structure DimensionField (δ : ℝ) where
  field : Subfield ℂ
  [finite : FiniteDimensional ℚ field]
  [galois : IsGalois ℚ field]
  element : field
  element_eq : (element : ℂ) = (δ : ℂ)
  integral : IsIntegral ℤ element
  extend : ∀ σ : field ≃ₐ[ℚ] field, ∃ τ : ℂ ≃+* ℂ,
    ∀ x : field, τ (x : ℂ) = (σ x : ℂ)

attribute [instance] DimensionField.finite DimensionField.galois

/-- Standard dimension facts for a pseudo-unitary category, retaining the
transported spherical structure on conjugates. These are [ENO 2.3, 2.5, 2.10,
8.21, 8.23]. They say only that conjugate global dimensions are positive and
at most the common FP dimension; equality for all conjugates is proved later. -/
structure PseudoUnitaryInputs (C : BraidedFusionCategory.{v,u}) where
  conjugateGlobal : (ℂ ≃+* ℂ) → ℝ
  conjugate_eq : ∀ σ, σ (C.fusion.globalFPDimension : ℂ) = (conjugateGlobal σ : ℂ)
  conjugate_positive : ∀ σ, 0 < conjugateGlobal σ
  conjugate_le : ∀ σ, conjugateGlobal σ ≤ C.fusion.globalFPDimension
  center : CenterInputs C
  arithmetic : DimensionField C.fusion.globalFPDimension

/-- Single explicit bundle of the literature and realization hypotheses used by
the main theorem. The final two fields are the concrete form of fusion-rule and
braid-matrix Galois invariance [ENO 2.30, 2.33; paper §2.1]. Their categorical
construction remains unproved and is listed in the assumption ledger. -/
structure StandardInputs where
  pseudo : ∀ C : BraidedFusionCategory.{v,u},
    PseudoUnitary C.globalDimension C.fusion.globalFPDimension → PseudoUnitaryInputs C
  conjugate_labels : ∀ {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ},
    GaloisConjugate C D σ → ∃ e : Fin C.fusion.rank ≃ Fin D.fusion.rank,
      ∀ i, C.fusion.fpSimple i = D.fusion.fpSimple (e i)
  conjugate_images : ∀ {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ},
    GaloisConjugate C D σ → ∀ (Y : D.Obj) n, ∃ X : C.Obj,
      Nonempty (braidImage Y n ≃* braidImage X n)

/-- The concrete pure-braid cabling diagram for a retract of a sum of tensor
powers. The pure braid image has finite index, since B_n/P_n = S_n. Its action
is a quotient of a subgroup of the product of the cabled image groups.

Only the diagram is supplied; no image finiteness or closure result is assumed.
This is the standard cabling construction used in [ERW 2.1(ii)]. Its construction
from categorical braidings is an explicit unproved realization input. -/
structure CablingWitness (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) (n : ℕ) where
  blockCount : ℕ
  lengths : Fin blockCount → Fin (n + 2) → ℕ
  pureImage : Subgroup (braidImage Y n)
  [finiteIndex : pureImage.FiniteIndex]
  cableImage : Subgroup (∀ r : Fin blockCount,
    braidImageAll X (∑ i, lengths r i))
  restriction : cableImage →* pureImage
  restriction_surjective : Function.Surjective restriction

attribute [instance] CablingWitness.finiteIndex

/-- Categorical cabling and the standard generated fusion subcategory.
The description of the subcategory by nonnegative powers is [EGNO 4.11.4].
The braid image identifications are naturality and coherence for the full
braided inclusion. The squared-dimension theorem is [ENO 8.27]. Faithful
strand inclusions come from tensoring by a nonzero object in a rigid category.

These are explicit construction inputs, not conclusions of Lemma 4.2 or
Corollary 4.3. See the ledger for the unproved cabling and inclusion bridges. -/
structure GeneratedInputs (C : BraidedFusionCategory.{v,u}) (X : C.Obj) where
  cabling : ∀ Y, GeneratedBy X Y → ∀ n, Nonempty (CablingWitness C X Y n)
  category : BraidedFusionCategory.{v,u}
  inclusion : category.Obj ⥤ C.Obj
  [inclusion_braided : inclusion.Braided]
  [inclusion_full : inclusion.Full]
  [inclusion_faithful : inclusion.Faithful]
  inclusion_generated : ∀ Y, GeneratedBy X (inclusion.obj Y)
  generated_essential_image : ∀ Y, GeneratedBy X Y →
    ∃ Z, Nonempty (inclusion.obj Z ≅ Y)
  image_equivalence : ∀ Y n,
    Nonempty (braidImage Y n ≃* braidImage (inclusion.obj Y) n)
  simple_square_integral : CategoryTheory.Simple X →
    WeaklyIntegral category.fusion.globalFPDimension →
    ∃ z : ℤ, C.fusion.fpDimension X ^ 2 = z
  strand_inclusion : CategoryTheory.Simple X → ∀ n m, n ≤ m →
    Nonempty (braidImage X n ↪ braidImage X m)

end PropertyF
