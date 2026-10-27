module
public import PropertyF.Ground.Dimensions.NaturalRoots
public import PropertyF.Ground.Dimensions.InvolutionTrace

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
/-- If every operator on the multiplicity spaces for a pair is the identity,
the natural square root is tensor compatible on that pair of simple objects. -/
theorem rootTensor_compatible_of_multiplicityDefects
    (C : Ground.BraidedFusionCategory.{v,u}) (i j : Fin (Ground.rank C))
    (h : ∀ k, (multiplicityDefect C i j k).toLinearMap = LinearMap.id) :
    (fourthDualRootNaturalIso C).app (Ground.simples C i ⊗ Ground.simples C j) =
      rootTensorIso C (Ground.simples C i) (Ground.simples C j) := by
  classical
  let X := Ground.simples C i ⊗ Ground.simples C j
  let e := simpleDecomposition C X
  let V := simplePiecesObject C X
  have hd : (rootTensorDefect C (Ground.simples C i) (Ground.simples C j)).hom = 𝟙 X := by
    apply (cancel_epi e.inv).1
    apply biproduct.hom_ext'
    intro a
    let f : Ground.simples C a.1 ⟶ X := biproduct.ι V a ≫ e.inv
    have hf := congrArg (fun L => L f) (h a.1)
    simpa [f, multiplicityDefect_apply, Category.assoc] using hf
  apply Iso.ext
  have hd' : ((fourthDualRootNaturalIso C).app X).hom ≫ (rootTensorIso C _ _).inv = 𝟙 X := hd
  apply (cancel_mono (rootTensorIso C _ _).inv).1
  simpa [X] using hd'

/-- Once the actual multiplicity defects are involutions, maximal traces force
tensor compatibility on the corresponding simple pair. -/
theorem rootTensor_compatible_of_involution_trace_saturation
    (C : Ground.BraidedFusionCategory.{v,u}) (i j : Fin (Ground.rank C))
    (hinv : ∀ k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (htrace : ∀ k, LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap =
      (Ground.fusionCoeff C i j k : ℂ)) :
    (fourthDualRootNaturalIso C).app (Ground.simples C i ⊗ Ground.simples C j) =
      rootTensorIso C (Ground.simples C i) (Ground.simples C j) := by
  apply rootTensor_compatible_of_multiplicityDefects C i j
  intro k
  letI : FiniteDimensional ℂ
      (Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) :=
    Ground.IsFusionCategory.hom_finite _ _
  apply involution_eq_one_of_trace_eq_finrank _ (hinv k)
  exact htrace k

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

end PropertyF.Ground.Dimensions
