module
public import PropertyF.Ground.Dimensions.IteratedTrace

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Closing the right tensor factor of an inserted endomorphism. -/
theorem rightPartialTrace_tensor_right (p : PivotalStructure (C := C)) (X Y : C) (b : Y ⟶ Y) :
    rightPartialTrace p X Y (End.of (𝟙 X ⊗ₘ b)) =
      End.of ((ρ_ X).inv ≫ X ◁ (p.rightTrace b).asHom ≫ (ρ_ X).hom) := by
  apply End.ext
  simp only [rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
    PivotalStructure.rightTrace, tensorHom_def, id_whiskerRight, Category.id_comp,
    whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  monoidal

/-- The right partial trace of an inserted right-factor endomorphism is scalar. -/
theorem rightPartialTrace_one_tensor (p : PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (X Y : C) (b : Y ⟶ Y) :
    rightPartialTrace p X Y (End.of (𝟙 X ⊗ₘ b)) = scalar (p.rightTrace b) • 1 := by
  have h := rightPartialTrace_tensor_right p X Y b
  rw [h]
  have hscalar : p.rightTrace b = scalar (p.rightTrace b) • (1 : End (𝟙_ C)) := by
    apply scalar.injective
    simp
  rw [hscalar]
  apply End.ext
  simp

/-- The partial trace of a tensor product is the left factor times the trace of the right. -/
theorem rightPartialTrace_tensor (p : PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (X Y : C) (a : X ⟶ X) (b : Y ⟶ Y) :
    rightPartialTrace p X Y (End.of (a ⊗ₘ b)) = scalar (p.rightTrace b) • End.of a := by
  have hf : End.of (a ⊗ₘ b) = End.of (𝟙 X ⊗ₘ b) * insertRightIdentity X Y (End.of a) := by
    apply End.ext
    simp [insertRightIdentity, tensorHom_def]
  rw [hf, rightPartialTrace_right, rightPartialTrace_one_tensor p scalar X Y b]
  simp

/-- Pivotal trace is multiplicative on tensor products of endomorphisms. -/
theorem pivotalTrace_tensor (p : PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (X Y : C) (a : X ⟶ X) (b : Y ⟶ Y) :
    scalar (p.rightTrace (a ⊗ₘ b)) = scalar (p.rightTrace a) * scalar (p.rightTrace b) := by
  have h := rightTrace_partialTrace p X Y (End.of (a ⊗ₘ b))
  rw [rightPartialTrace_tensor p scalar X Y a b] at h
  have hs : p.rightTrace (a ⊗ₘ b) = scalar (p.rightTrace b) • p.rightTrace a := by
    simpa [PivotalStructure.rightTrace_smul] using h.symm
  rw [hs, map_smul]
  simp [mul_comm]

end PropertyF.Ground.Dimensions
