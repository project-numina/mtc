module
public import PropertyF.Ground.Integrate.ScalarTwist
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Integrate.Conjugacy
public import PropertyF.Ground.Modular.FusionTransport

/-! Pivotal traces and finite braid images under scalar twisting. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.ScalarTwist
universe v u
variable (C : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ)

/-- The original pivotal maps satisfy the same categorical equations. -/
def pivotal (p : Dimensions.PivotalStructure (C := C.Obj)) :
    Dimensions.PivotalStructure (C := (category C σ).Obj) := p

/-- Sphericality only refers to categorical morphisms. -/
theorem spherical (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical) :
    (pivotal C σ p).IsSpherical := hp

/-- The twisted inverse unit-scalar map applies σ to the original scalar. -/
theorem unitScalar_twist (f : End (𝟙_ C.Obj)) :
    unitScalar (category C σ) f = σ (unitScalar C f) := by
  let f' : End (𝟙_ (category C σ).Obj) := f
  change unitScalar (category C σ) f' = σ (unitScalar C f)
  apply (unit_algebraMap_bijective (category C σ)).1
  rw [algebraMap_unitScalar (category C σ) f']
  change f = _
  conv_lhs => rw [← algebraMap_unitScalar C f]
  simp only [Algebra.algebraMap_eq_smul_one]
  change (unitScalar C f) • (1 : End (𝟙_ C.Obj)) = σ.symm (σ (unitScalar C f)) • (1 : End (𝟙_ C.Obj))
  rw [σ.symm_apply_apply]

/-- Pivotal dimensions transform by the specified field automorphism. -/
theorem pivotalDimension_twist (p : Dimensions.PivotalStructure (C := C.Obj)) (X : C.Obj) :
    Dimensions.pivotalDimension (category C σ) (pivotal C σ p) X =
    σ (Dimensions.pivotalDimension C p X) := by
  exact unitScalar_twist C σ _

/-- Property F is preserved by scalar twisting. -/
theorem propertyF_twist (hF : HasPropertyF C.Obj) : HasPropertyF (category C σ).Obj :=
  Modular.conjugate_propertyF C (category C σ) (conjugate C σ) hF

/-- Individual braid images are unchanged as groups. -/
theorem objectPropertyF_twist (X : C.Obj) :
    ObjectPropertyF X ↔ ObjectPropertyF (show (category C σ).Obj from X) := Iff.rfl

/-- Match chosen simple representatives and transport both dimensions. -/
theorem labels (p : Dimensions.PivotalStructure (C := C.Obj)) :
    ∃ e : Fin (rank C) ≃ Fin (rank (category C σ)),
      ∀ i, fpSimple C i = fpSimple (category C σ) (e i) ∧
        Dimensions.pivotalDimension (category C σ) (pivotal C σ p)
          (simples (category C σ) (e i)) =
        σ (Dimensions.pivotalDimension C p (simples C i)) := by
  obtain ⟨e, he⟩ := Modular.simpleLabels_equiv C (category C σ) (conjugate C σ).equivalence
  refine ⟨e, fun i => ⟨Modular.conjugate_fpSimple C (category C σ) (conjugate C σ) e he i, ?_⟩⟩
  rw [← pivotalDimension_twist C σ p (simples C i)]
  exact (Dimensions.pivotalDimension_iso (category C σ) (pivotal C σ p) (he i).some).symm

end PropertyF.Ground.ScalarTwist
