module
public import MTC.Braided.Definitions
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Ground target

This file gives a category-level statement without the numerical data fields in
`FusionData` or `GlobalDimensionData`. The simple representatives are chosen
from the finite semisimplicity property. FP dimension is the spectral radius of
left multiplication on the fusion ring. The categorical dimension uses the
canonical double-dual isomorphism afforded by braiding and rigidity.

The mathematical identifications and independence of representatives still
need proofs; see ground/integrate/LEDGER.md. In particular this statement must
not be advertised as established merely because its definition elaborates.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground
universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Exactly the finiteness and semisimplicity properties of a complex fusion
category, with no choice of numerical dimensions. The structural category
instances are supplied separately. -/
class IsFusionCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [Abelian C] [Linear ℂ C] [RigidCategory C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C] : Prop where
  hom_finite : ∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)
  unit_simple : Simple (𝟙_ C)
  finite_semisimple : ∃ (n : ℕ) (S : Fin n → C),
    (∀ i, Simple (S i)) ∧
    (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
    (∀ X : C, ∃ m : Fin n → ℕ,
      Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => S p.1)))

/-- A category carrying the usual structure and the fusion properties. -/
structure BraidedFusionCategory where
  Obj : Type u
  [category : Category.{v} Obj]
  [monoidal : MonoidalCategory Obj]
  [braided : BraidedCategory Obj]
  [abelian : Abelian Obj]
  [linear : Linear ℂ Obj]
  [rigid : RigidCategory Obj]
  [monoidalPreadditive : MonoidalPreadditive Obj]
  [monoidalLinear : MonoidalLinear ℂ Obj]
  [fusion : IsFusionCategory Obj]

attribute [instance] BraidedFusionCategory.category BraidedFusionCategory.monoidal
  BraidedFusionCategory.braided BraidedFusionCategory.abelian BraidedFusionCategory.linear
  BraidedFusionCategory.rigid BraidedFusionCategory.monoidalPreadditive
  BraidedFusionCategory.monoidalLinear BraidedFusionCategory.fusion

variable (C : BraidedFusionCategory.{v,u})

def rank : ℕ := Classical.choose (IsFusionCategory.finite_semisimple (C := C.Obj))

def simples : Fin (rank C) → C.Obj :=
  Classical.choose (Classical.choose_spec (IsFusionCategory.finite_semisimple (C := C.Obj)))

/-- Matrix of multiplication by a simple class in the Grothendieck ring. -/
def fusionMatrix (i : Fin (rank C)) : Matrix (Fin (rank C)) (Fin (rank C)) ℂ :=
  fun k j => (Module.finrank ℂ (simples C k ⟶ simples C i ⊗ simples C j) : ℂ)

/-- The Frobenius–Perron dimension is the spectral radius of the fusion matrix. -/
def fpSimple (i : Fin (rank C)) : ℝ :=
  (spectralRadius ℂ (fusionMatrix C i)).toReal

def globalFPDimension : ℝ := ∑ i, (fpSimple C i) ^ 2

/-- The braiding identifies X with its right double dual by uniqueness of right
 duals. This construction does not assume a pivotal structure. -/
def doubleDualIso (X : C.Obj) : X ≅ ((Xᘁ)ᘁ) :=
  rightDualIso (BraidedCategory.exactPairing_swap X (Xᘁ)) inferInstance

/-- The inverse of scalar multiplication by the identity of the tensor unit.
For a complex fusion category it is bijective by Schur's lemma; proving this
fact is a pending obligation, not a fusion-category field. -/
def unitScalar : End (𝟙_ C.Obj) → ℂ :=
  Function.invFun (algebraMap ℂ (End (𝟙_ C.Obj)))

def squaredNorm (X : C.Obj) : ℂ :=
  unitScalar C (rightQuantumTrace (doubleDualIso C X)) *
    unitScalar C (leftQuantumTrace (doubleDualIso C X))

def globalDimension : ℂ := ∑ i, squaredNorm C (simples C i)

def PseudoUnitary : Prop := globalDimension C = (globalFPDimension C : ℂ)

/-- Semilinear braided equivalence with respect to an automorphism of ℂ. -/
structure GaloisConjugate (D : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ) where
  equivalence : C.Obj ≌ D.Obj
  [monoidal : equivalence.functor.Monoidal]
  [braided : equivalence.functor.Braided]
  map_smul : ∀ {X Y : C.Obj} (z : ℂ) (f : X ⟶ Y),
    equivalence.functor.map (z • f) = σ z • equivalence.functor.map f

def HasPseudoUnitaryGaloisConjugate : Prop :=
  ∃ (D : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ),
    Nonempty (GaloisConjugate C D σ) ∧ PseudoUnitary D

/-- The intended, unconditional theorem. No proof is asserted here. -/
def TargetStatement : Prop :=
  ∀ C : BraidedFusionCategory.{v,u},
    HasPseudoUnitaryGaloisConjugate C → HasPropertyF C.Obj →
      WeaklyIntegral (globalFPDimension C)

end PropertyF.Ground
