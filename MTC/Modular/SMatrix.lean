module
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import MTC.CategoryTheory.Dimensions.SquaredNorm
public import MTC.CategoryTheory.Dimensions.Trace
public import MTC.Fusion.Multiplicity
public import MTC.Fusion.Reciprocity
public import MTC.Modular.FusionTransport

open MTC.Fusion

open MTC.Braided

/-!
# The categorical S matrix and nonvanishing of simple dimensions.
-/

@[expose] public noncomputable section

section
/-!
# Categorical S-matrix

The entries are the pivotal traces of actual categorical double braidings.
Symmetry uses cyclicity, and the unit column follows from the unitors. In a
spherical category the intrinsic global dimension is the sum of squares of
these simple dimensions. No modular nondegeneracy is required here.
-/
open scoped BigOperators
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open MTC.CategoryTheory.Dimensions

namespace MTC.Modular
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]

/-- Double braiding on a tensor product. -/
def doubleBraiding (X Y : C) : X ⊗ Y ⟶ X ⊗ Y :=
  (β_ X Y).hom ≫ (β_ Y X).hom

omit [RightRigidCategory C] in
/-- Double braiding is natural simultaneously in both strands. -/
theorem doubleBraiding_natural {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    doubleBraiding X Y ≫ (f ⊗ₘ g) = (f ⊗ₘ g) ≫ doubleBraiding X' Y' := by
  rw [doubleBraiding, doubleBraiding, Category.assoc, ← braiding_naturality g f,
    ← Category.assoc, ← braiding_naturality f g, Category.assoc]

/-- The unnormalized S entry, valued in endomorphisms of the tensor unit. -/
def SEntry (p : PivotalStructure (C := C)) (X Y : C) : End (𝟙_ C) :=
  p.rightTrace (doubleBraiding X Y)

/-- Cyclicity of the pivotal trace gives symmetry. -/
theorem SEntry_symmetric (p : PivotalStructure (C := C)) (X Y : C) :
    SEntry p X Y = SEntry p Y X :=
  p.rightTrace_cyclic (β_ X Y).hom (β_ Y X).hom

/-- The trace of double braiding depends only on the isomorphism class. -/
theorem SEntry_iso_right (p : PivotalStructure (C := C)) (X : C) {Y Z : C} (e : Y ≅ Z) :
    SEntry p X Y = SEntry p X Z :=
  let t := Iso.refl X ⊗ᵢ e
  have h := p.rightTrace_cyclic (doubleBraiding X Y ≫ t.hom) t.inv
  by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      show doubleBraiding X Y ≫ t.hom = t.hom ≫ doubleBraiding X Z from
        doubleBraiding_natural (𝟙 X) e.hom, Iso.inv_hom_id_assoc] at h
    exact h

omit [RightRigidCategory C] in
/-- The double braiding with the tensor unit is the identity. -/
theorem doubleBraiding_unit (X : C) : doubleBraiding X (𝟙_ C) = 𝟙 (X ⊗ 𝟙_ C) := by
  simp [doubleBraiding, braiding_tensorUnit_right, braiding_tensorUnit_left, Category.assoc]

/-- The unit column of the unnormalized S entry is categorical dimension. -/
theorem SEntry_unit (p : PivotalStructure (C := C)) (X : C) :
    SEntry p X (𝟙_ C) = p.rightTrace (𝟙 X) :=
  (congrArg p.rightTrace (doubleBraiding_unit X)).trans (p.rightTrace_id_iso (ρ_ X))

section
variable (C : MTC.Fusion.BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- Spherical dimension of a chosen simple representative. -/
def simpleDimension (i : Fin (rank C)) : ℂ :=
  MTC.unitScalarEquiv C (p.rightTrace (𝟙 (simples C i)))

/-- The simple pivotal dimensions agree with Frobenius–Perron dimensions. -/
abbrev HasFPSimpleDimensions : Prop :=
  ∀ i, simpleDimension C p i = (fpSimple C i : ℂ)

/-- A spherical pivotal structure whose simple dimensions are FP dimensions. -/
abbrev IsFPSpherical : Prop := p.IsSpherical ∧ HasFPSimpleDimensions C p

/-- The unnormalized categorical S-matrix, defined by double-braiding traces. -/
def categoricalS : Matrix (Fin (rank C)) (Fin (rank C)) ℂ :=
  fun i j => MTC.unitScalarEquiv C (SEntry p (simples C i) (simples C j))

/-- Two simple labels satisfy the numerical S-matrix centrality test. -/
abbrev sCentralizes (i j : Fin (rank C)) : Prop :=
  categoricalS C p i j = simpleDimension C p i * simpleDimension C p j

/-- The labels satisfying the numerical S-centrality test against a set. -/
abbrev sCentralizer (A : Set (Fin (rank C))) : Set (Fin (rank C)) :=
  {j | ∀ i ∈ A, sCentralizes C p i j}

/-- A normalized column of the categorical S-matrix. -/
def normalizedSColumn (j : Fin (rank C)) : Fin (rank C) → ℂ :=
  fun i ↦ categoricalS C p i j / simpleDimension C p j

/-- The categorical S-matrix is symmetric. -/
theorem categoricalS_symmetric (i j : Fin (rank C)) :
    categoricalS C p i j = categoricalS C p j i :=
  congrArg (MTC.unitScalarEquiv C) (SEntry_symmetric p _ _)

/-- The unit column consists of categorical dimensions. -/
theorem categoricalS_unit (i : Fin (rank C)) :
    categoricalS C p i (unitIndex C) = simpleDimension C p i :=
  (unitIndex_iso C).elim fun e ↦
    congrArg (MTC.unitScalarEquiv C)
      ((SEntry_iso_right p (simples C i) e).trans (SEntry_unit p (simples C i)))

/-- In the spherical case, global dimension is the sum of squared simple dimensions. -/
theorem categorical_global_eq_sum_squares (hp : p.IsSpherical) :
    MTC.Fusion.globalDimension C = ∑ i, simpleDimension C p i ^ 2 := by
  simpa only [simpleDimension, ← MTC.unitScalar_eq_equiv, ← rightTrace_id] using
    target_globalDimension_eq_sum_squares hp

end

end MTC.Modular
end

section
/-!
# Nonvanishing of simple pivotal dimensions

Rigidity identifies the Hom space from X ⊗ X* to the tensor unit with End(X),
which is one-dimensional by Schur. Semisimplicity splits coevaluation; the
nonzero evaluation must be a nonzero multiple of that splitting. Consequently
the pivotal dimension of a simple object cannot vanish.
-/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MTC.CategoryTheory.Dimensions

namespace MTC.Modular
universe v u
variable (C : MTC.Fusion.BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))


/-- A simple object has nonzero pivotal trace of the identity. -/
theorem pivotalTrace_simple_ne_zero (X : C.Obj) [Simple X] :
    p.rightTrace (𝟙 X) ≠ 0 := by
  simpa only [MTC.CategoryTheory.Dimensions.rightTrace_id] using
    MTC.CategoryTheory.Dimensions.rightQuantumTrace_simple_ne_zero (p.iso X)

/-- The scalar pivotal trace of a simple object is nonzero. -/
theorem unitScalar_rightTrace_ne_zero (X : C.Obj) [Simple X] :
    MTC.Fusion.unitScalar C (p.rightTrace (𝟙 X)) ≠ 0 := by
  rw [MTC.unitScalar_eq_equiv]
  simpa only [map_zero] using
    (MTC.unitScalarEquiv C).injective.ne (pivotalTrace_simple_ne_zero C p X)

/-- Every simple categorical dimension is nonzero, without pseudo-unitarity. -/
theorem simpleDimension_ne_zero (i : Fin (rank C)) :
    simpleDimension C p i ≠ 0 :=
  let : Simple (simples C i) := simples_simple C i
  by simpa only [simpleDimension, ← MTC.unitScalar_eq_equiv] using
    unitScalar_rightTrace_ne_zero C p (simples C i)

end MTC.Modular
end

@[expose] public noncomputable section
open MTC MTC.CategoryTheory.Dimensions MTC.Modular
namespace MTC.Modular
universe v u

/-- A spherical pivotal structure with nonzero determinant of its categorical S matrix. -/
def HasNondegenerateSphericalStructure (C : BraidedFusionCategory.{v,u}) : Prop :=
  ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ (categoricalS C p).det ≠ 0

/-- An explicit spherical structure and invertible S matrix give the predicate. -/
theorem hasNondegenerateSphericalStructure_of_data (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hs : p.IsSpherical)
    (hS : (categoricalS C p).det ≠ 0) : HasNondegenerateSphericalStructure C :=
  ⟨p, hs, hS⟩

end MTC.Modular
