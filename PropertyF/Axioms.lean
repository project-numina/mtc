module
public import PropertyF.BlockTrace
public import Mathlib.CategoryTheory.Monoidal.Center
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Explicit interfaces and standard inputs

There are no global `axiom` declarations in this file. Every unproved input is a
field of a named structure and therefore an explicit parameter of any result
using it. See FORMALIZATION.md: absence of `sorryAx` is not evidence that these
interfaces have been constructed for fusion categories.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF

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
  galoisLabel : (ℂ ≃+* ℂ) → Fin rank → Fin rank
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

end PropertyF
