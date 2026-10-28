module
public import PropertyF.Ground.Dimensions.NaturalRoots
public import PropertyF.Ground.Dimensions.InvolutionTrace
public import PropertyF.Ground.Dimensions.NaturalSquareDefect

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Tensoring the components of the natural square root gives another
isomorphism from a tensor product to its double dual. -/
def rootTensorIso (C : Ground.BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    X ⊗ Y ≅ ((X ⊗ Y)ᘁ)ᘁ :=
  ((fourthDualRootNaturalIso C).app X ⊗ᵢ (fourthDualRootNaturalIso C).app Y) ≪≫
    doubleDualTensorIso X Y

/-- The defect of tensor compatibility of the chosen natural square root. -/
def rootTensorDefect (C : Ground.BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    X ⊗ Y ≅ X ⊗ Y :=
  (fourthDualRootNaturalIso C).app (X ⊗ Y) ≪≫ (rootTensorIso C X Y).symm

/-- The actual operator on each fusion multiplicity space induced by the tensor
defect. Its involutivity requires the still-unproved tensor compatibility of
the fourth-dual isomorphism. -/
def multiplicityDefect (C : Ground.BraidedFusionCategory.{v,u})
    (i j k : Fin (Ground.rank C)) :
    (Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) ≃ₗ[ℂ]
      (Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) :=
  Linear.homCongr ℂ (Iso.refl _) (rootTensorDefect C (Ground.simples C i) (Ground.simples C j))

/-- The multiplicity operator is composition with the tensor defect. -/
theorem multiplicityDefect_apply (C : Ground.BraidedFusionCategory.{v,u})
    (i j k : Fin (Ground.rank C))
    (f : Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) :
    multiplicityDefect C i j k f =
      f ≫ (rootTensorDefect C (Ground.simples C i) (Ground.simples C j)).hom := by
  simp [multiplicityDefect, Linear.homCongr_apply]

set_option backward.isDefEq.respectTransparency false in
/-- If the categorical multiplicity defect is involutive, its trace is an
integer bounded by the actual fusion coefficient. -/
theorem multiplicityDefect_trace_integer_bound
    (C : Ground.BraidedFusionCategory.{v,u}) (i j k : Fin (Ground.rank C))
    (hinv : (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) :
    ∃ n : ℤ, LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap = (n : ℂ) ∧
      |n| ≤ (Ground.fusionCoeff C i j k : ℤ) := by
  letI : FiniteDimensional ℂ
      (Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) :=
    Ground.IsFusionCategory.hom_finite _ _
  exact involution_trace_integer_bound _ hinv

/-- If the tensor of the simple root components has the expected fourth-dual
square, the resulting tensor defect is an involution. -/
theorem rootTensorDefect_involution_of_tensor_square
    (C : Ground.BraidedFusionCategory.{v,u}) (X Y : C.Obj)
    (hsq : (rootTensorIso C X Y).hom ≫ (((rootTensorIso C X Y).homᘁ)ᘁ) =
      (fourthDualIso C (X ⊗ Y)).hom) :
    (rootTensorDefect C X Y).hom ≫ (rootTensorDefect C X Y).hom = 𝟙 (X ⊗ Y) := by
  have ha := congrArg (fun n => (n.app (X ⊗ Y)).hom) (fourthDualRootNaturalSquare_eq C)
  change ((fourthDualRootNaturalIso C).app (X ⊗ Y)).hom ≫
    ((((fourthDualRootNaturalIso C).app (X ⊗ Y)).homᘁ)ᘁ) =
      (fourthDualIso C (X ⊗ Y)).hom at ha
  have h := natural_square_defect_involution (doubleDualFunctor C.Obj)
    (fourthDualRootNaturalIso C) (X ⊗ Y) (rootTensorIso C X Y) (ha.trans hsq.symm)
  exact h

/-- The tensor-square comparison implies involutivity of every corresponding
actual multiplicity-space operator. -/
theorem multiplicityDefect_involution_of_tensor_square
    (C : Ground.BraidedFusionCategory.{v,u}) (i j k : Fin (Ground.rank C))
    (hsq : (rootTensorIso C (Ground.simples C i) (Ground.simples C j)).hom ≫
      (((rootTensorIso C (Ground.simples C i) (Ground.simples C j)).homᘁ)ᘁ) =
        (fourthDualIso C (Ground.simples C i ⊗ Ground.simples C j)).hom) :
    (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1 := by
  have hd := rootTensorDefect_involution_of_tensor_square C _ _ hsq
  ext f
  change multiplicityDefect C i j k (multiplicityDefect C i j k f) = f
  rw [multiplicityDefect_apply, multiplicityDefect_apply, Category.assoc, hd, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor-square identity follows from naturality of the double-dual
tensor comparison and the corresponding tensor law for the fourth dual. -/
theorem rootTensor_square_of_fourthDual_tensor
    (C : Ground.BraidedFusionCategory.{v,u}) (X Y : C.Obj)
    (hnat : (doubleDualTensorIso X Y).hom ≫
        (((((fourthDualRootNaturalIso C).app X).hom ⊗ₘ
          ((fourthDualRootNaturalIso C).app Y).hom)ᘁ)ᘁ) =
      (((((fourthDualRootNaturalIso C).app X).homᘁ)ᘁ) ⊗ₘ
        ((((fourthDualRootNaturalIso C).app Y).homᘁ)ᘁ)) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom)
    (hfourth : (fourthDualIso C (X ⊗ Y)).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ)) :
    (rootTensorIso C X Y).hom ≫ (((rootTensorIso C X Y).homᘁ)ᘁ) =
      (fourthDualIso C (X ⊗ Y)).hom := by
  have hx := congrArg (fun n => (n.app X).hom) (fourthDualRootNaturalSquare_eq C)
  have hy := congrArg (fun n => (n.app Y).hom) (fourthDualRootNaturalSquare_eq C)
  change ((fourthDualRootNaturalIso C).app X).hom ≫
    ((((fourthDualRootNaturalIso C).app X).homᘁ)ᘁ) = (fourthDualIso C X).hom at hx
  change ((fourthDualRootNaturalIso C).app Y).hom ≫
    ((((fourthDualRootNaturalIso C).app Y).homᘁ)ᘁ) = (fourthDualIso C Y).hom at hy
  rw [hfourth, ← hx, ← hy]
  simp only [rootTensorIso, Iso.trans_hom, tensorIso_hom, comp_rightAdjointMate,
    Category.assoc]
  have hn2 := congrArg (fun f =>
    (((fourthDualRootNaturalIso C).app X).hom ⊗ₘ
      ((fourthDualRootNaturalIso C).app Y).hom) ≫ f ≫
      (((doubleDualTensorIso X Y).homᘁ)ᘁ)) hnat
  simp only [Category.assoc] at hn2
  rw [hn2]
  rw [tensorHom_comp_tensorHom_assoc]

end PropertyF.Ground.Dimensions
