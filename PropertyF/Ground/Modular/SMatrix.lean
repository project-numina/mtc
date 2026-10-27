module
public import PropertyF.Ground.Dimensions.Trace
public import PropertyF.Ground.Modular.Labels
public import PropertyF.Ground.Fusion.Multiplicity
public import PropertyF.Ground.Dimensions.GroundNorm

/-!
# Categorical S-matrix

The entries are the pivotal traces of actual categorical double braidings.
Symmetry uses cyclicity, and the unit column follows from the unitors. In a
spherical category the intrinsic global dimension is the sum of squares of
these simple dimensions. No modular nondegeneracy is required here.
-/
open scoped BigOperators
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground.Dimensions
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]

/-- Double braiding on a tensor product. -/
def doubleBraiding (X Y : C) : X ⊗ Y ⟶ X ⊗ Y :=
  (β_ X Y).hom ≫ (β_ Y X).hom

/-- The unnormalized S entry, valued in endomorphisms of the tensor unit. -/
def SEntry (p : PivotalStructure (C := C)) (X Y : C) : End (𝟙_ C) :=
  p.rightTrace (doubleBraiding X Y)

/-- Cyclicity of the pivotal trace gives symmetry. -/
theorem SEntry_symmetric (p : PivotalStructure (C := C)) (X Y : C) :
    SEntry p X Y = SEntry p Y X :=
  p.rightTrace_cyclic (β_ X Y).hom (β_ Y X).hom

omit [RightRigidCategory C] in
/-- Double braiding is natural in the second object. -/
theorem doubleBraiding_natural_right (X : C) {Y Z : C} (e : Y ≅ Z) :
    doubleBraiding X Y ≫ (𝟙 X ⊗ₘ e.hom) =
      (𝟙 X ⊗ₘ e.hom) ≫ doubleBraiding X Z := by
  unfold doubleBraiding
  rw [Category.assoc, ← braiding_naturality e.hom (𝟙 X), ← Category.assoc,
    ← braiding_naturality (𝟙 X) e.hom, Category.assoc]

/-- The trace of double braiding depends only on the isomorphism class. -/
theorem SEntry_iso_right (p : PivotalStructure (C := C)) (X : C) {Y Z : C} (e : Y ≅ Z) :
    SEntry p X Y = SEntry p X Z := by
  let t := Iso.refl X ⊗ᵢ e
  have hn : doubleBraiding X Y ≫ t.hom = t.hom ≫ doubleBraiding X Z := by
    exact doubleBraiding_natural_right X e
  have h := p.rightTrace_cyclic (doubleBraiding X Y ≫ t.hom) t.inv
  have hh : p.rightTrace (doubleBraiding X Y) =
      p.rightTrace (t.inv ≫ doubleBraiding X Y ≫ t.hom) := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  rw [hn, Iso.inv_hom_id_assoc] at hh
  exact hh

omit [RightRigidCategory C] in
/-- The double braiding with the tensor unit is the identity. -/
theorem doubleBraiding_unit (X : C) : doubleBraiding X (𝟙_ C) = 𝟙 (X ⊗ 𝟙_ C) := by
  simp [doubleBraiding, braiding_tensorUnit_right, braiding_tensorUnit_left, Category.assoc]

/-- The unit column of the unnormalized S entry is categorical dimension. -/
theorem SEntry_unit (p : PivotalStructure (C := C)) (X : C) :
    SEntry p X (𝟙_ C) = p.rightTrace (𝟙 X) := by
  rw [SEntry, doubleBraiding_unit]
  exact p.rightTrace_id_iso (ρ_ X)

/-- Spherical dimension of a chosen simple representative. -/
def simpleDimension (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) : ℂ :=
  Ground.unitScalarEquiv C (p.rightTrace (𝟙 (simples C i)))

/-- The unnormalized categorical S-matrix, defined by double-braiding traces. -/
def categoricalS (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) : Matrix (Fin (rank C)) (Fin (rank C)) ℂ :=
  fun i j => Ground.unitScalarEquiv C (SEntry p (simples C i) (simples C j))

/-- The categorical S-matrix is symmetric. -/
theorem categoricalS_symmetric (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (i j : Fin (rank C)) :
    categoricalS C p i j = categoricalS C p j i := by
  exact congrArg (Ground.unitScalarEquiv C) (SEntry_symmetric p _ _)

/-- The unit column consists of categorical dimensions. -/
theorem categoricalS_unit (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) :
    categoricalS C p i (unitIndex C) = simpleDimension C p i := by
  obtain ⟨e⟩ := unitIndex_iso C
  change Ground.unitScalarEquiv C (SEntry p (simples C i) (simples C (unitIndex C))) = _
  rw [SEntry_iso_right p (simples C i) e, SEntry_unit]
  rfl

/-- In the spherical case, global dimension is the sum of squared simple dimensions. -/
theorem categorical_global_eq_sum_squares (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical) :
    Ground.globalDimension C = ∑ i, simpleDimension C p i ^ 2 := by
  rw [target_globalDimension_eq_sum_squares C p hp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Ground.unitScalar_eq_equiv, ← rightTrace_id]
  rfl

end PropertyF.Ground.Modular
