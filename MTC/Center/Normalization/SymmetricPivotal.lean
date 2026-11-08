module
public import MTC.Center.Normalization.MugerCategory
public import MTC.Center.Induction.DrinfeldTheorem
public import MTC.PropertyF.Pivotal.SlopeTrace

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # The canonical pivotal structure of a symmetric braiding

The Drinfeld isomorphism is monoidal when the actual braiding is symmetric.
Its sphericality follows from invariance of the braided loop under duality.
Integer dimensions of this pivotal structure remain a separate obligation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [BraidedCategory D] [RightRigidCategory D]

/-- The Drinfeld isomorphism gives a pivotal structure when the actual
braiding of a right-rigid category is symmetric. -/
def canonicalSymmetricPivotal
    (hsym : ∀ X Y : D, MTC.Modular.doubleBraiding X Y = 𝟙 _) :
    PivotalStructure (C := D) where
  iso X := drinfeldIso X
  naturality f := drinfeldIso_natural f
  tensor X Y := by
    have h := (MTC.Center.Induction.drinfeld_tensor X Y).w
    simpa only [hsym X Y, Category.id_comp] using h
  unit := drinfeld_unit

/-- The actual braiding on the Müger category is symmetric. -/
theorem mugerBraiding_symmetric (C : BraidedFusionCategory.{v,u})
    (X Y : MugerCategory C) : MTC.Modular.doubleBraiding X Y = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  exact X.property Y.obj

/-- The actual symmetric Müger fusion category has its canonical Drinfeld
pivotal structure. -/
def mugerCanonicalPivotal (C : BraidedFusionCategory.{v,u}) :
    PivotalStructure (C := MugerCategory C) := canonicalSymmetricPivotal (mugerBraiding_symmetric C)

/-- The dimension of the canonical symmetric pivotal structure is the
underlying braided loop. -/
theorem canonicalSymmetricPivotal_dimension_loop
    (C : BraidedFusionCategory.{v,u})
    (hsym : ∀ X Y : C.Obj, MTC.Modular.doubleBraiding X Y = 𝟙 _) (X : C.Obj) :
    pivotalDimension C (canonicalSymmetricPivotal hsym) X =
      unitScalar C (End.of (MTC.PropertyF.Pivotal.braidedLoop X)) := by
  unfold pivotalDimension
  congr 1
  apply End.ext
  simp only [PivotalStructure.rightTrace, rightTraceWith, canonicalSymmetricPivotal,
    Category.id_comp, tensorHom_def, whiskerLeft_id, Category.comp_id,
    drinfeld_eval, MTC.PropertyF.Pivotal.braidedLoop]

/-- The canonical pivotal structure of a symmetric braided fusion category is
spherical. The symmetry hypothesis refers to its actual bundled braiding. -/
theorem canonicalSymmetricPivotal_spherical
    (C : BraidedFusionCategory.{v,u})
    (hsym : ∀ X Y : C.Obj, MTC.Modular.doubleBraiding X Y = 𝟙 _) :
    (canonicalSymmetricPivotal hsym).IsSpherical := by
  apply (pivotal_spherical_iff_simple_dimensions_real C (canonicalSymmetricPivotal hsym)).2
  intro i
  rw [← MTC.Center.Induction.pivotalDimension_simple_dual_conj (canonicalSymmetricPivotal hsym) i,
    canonicalSymmetricPivotal_dimension_loop C hsym ((simples C i)ᘁ),
    ← MTC.PropertyF.Pivotal.braidedLoop_eq_dual C (simples C i),
    ← canonicalSymmetricPivotal_dimension_loop C hsym (simples C i)]

/-- The actual Müger category's canonical pivotal structure is spherical. -/
theorem mugerCanonicalPivotal_spherical (C : BraidedFusionCategory.{v,u}) :
    (mugerCanonicalPivotal C).IsSpherical := by
  let h : ∀ X Y : (bundledMuger C).Obj, MTC.Modular.doubleBraiding X Y = 𝟙 _ :=
    mugerBraiding_symmetric C
  exact canonicalSymmetricPivotal_spherical (bundledMuger C) h

end MTC.Center.Normalization
end
