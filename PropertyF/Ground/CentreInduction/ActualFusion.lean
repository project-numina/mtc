module
public import PropertyF.Ground.CentreInduction.UnitCentrality
public import PropertyF.Ground.CentreInduction.PseudoUnitary

/-! Centre fusion and FP dimension using the constructed induction adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u

/-- If the actual centre already has a fusion structure, its global FP
 dimension is the square of the base global FP dimension. -/
theorem globalFPDimension_square_of_actual_induction (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)] :
    globalFPDimension (Integrate.bundledCenter C) = (globalFPDimension C) ^ 2 :=
  globalFPDimension_square_of_adjunction C (induction C) (actualAdjunction C)
    (fun _ => ⟨Iso.refl _⟩)

/-- The actual centre is finite semisimple assuming the explicit loop-sliding
 identity and nonzero global categorical dimension. -/
theorem finite_semisimple_of_actual_induction (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0) :
    ∃ (n : ℕ) (S : Fin n → CategoryTheory.Center C.Obj),
      (∀ i, Simple (S i)) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      (∀ X, ∃ m : Fin n → ℕ,
        Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => S p.1))) :=
  finite_semisimple_of_adjunction_and_loop C p hp hslide hne (induction C) (actualAdjunction C)

/-- The actual centre has a fusion structure once rigidity, spherical loop
 sliding, and nonzero global categorical dimension are supplied. -/
theorem fusion_of_actual_induction (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0) :
    IsFusionCategory (CategoryTheory.Center C.Obj) :=
  fusion_of_adjunction_and_loop C p hp hslide hne (induction C) (actualAdjunction C)

/-- The above fusion structure has the expected global FP dimension. -/
theorem globalFPDimension_square_of_actual_assembled_fusion (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0) :
    letI : IsFusionCategory (CategoryTheory.Center C.Obj) := fusion_of_actual_induction C p hp hslide hne
    globalFPDimension (Integrate.bundledCenter C) = (globalFPDimension C) ^ 2 := by
  letI : IsFusionCategory (CategoryTheory.Center C.Obj) := fusion_of_actual_induction C p hp hslide hne
  exact globalFPDimension_square_of_actual_induction C

/-- Pseudo-unitarity supplies the nonzero dimension for the fusion assembly. -/
theorem fusion_of_pseudoUnitary_actual_induction (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)] (hPU : PseudoUnitary C)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) : IsFusionCategory (CategoryTheory.Center C.Obj) :=
  fusion_of_actual_induction C p hp hslide (globalDimension_ne_zero_of_pseudoUnitary C hPU)

end PropertyF.Ground.CentreInduction
