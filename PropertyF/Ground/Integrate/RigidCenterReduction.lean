module
public import PropertyF.Ground.Integrate.CompatibleCenterReduction
public import PropertyF.Ground.CentreRigid.ForgetComparison

/-! Eliminate centre rigidity using the actual normalized mate construction. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- The constructed centre rigid structure removes an independent rigidity
premise from the numerical-core route. -/
theorem target_of_fusion_center_integral_numerical_core
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj →
      letI := CentreRigid.rigidCenter (C := C.Obj)
      ∃ (hFusion : IsFusionCategory (CategoryTheory.Center C.Obj)),
        letI := hFusion
        let Z := Integrate.bundledCenter C
        ∃ (p : Dimensions.PivotalStructure (C := Z.Obj)),
          p.IsSpherical ∧
          (∀ i, Modular.simpleDimension Z p i = (fpSimple Z i : ℂ)) ∧
          (Modular.categoricalS Z p).det ≠ 0 ∧
          (∀ y ∈ numericalProductCore C p,
            ∃ z : ℤ, Modular.simpleDimension Z p y = z)) : TargetStatement.{v,u} := by
  apply target_of_integral_numerical_center_core
  intro C hPU hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  obtain ⟨hFusion, p, hp, hdim, hdet, hintegral⟩ := hCenter C hPU hF
  exact ⟨inferInstance, hFusion, p, hp, hdim, hdet, hintegral⟩

/-- A compatible pivotal lift now supplies centre fusion and its positive
spherical structure without a separate rigidity or pseudo-unitarity premise. -/
theorem target_of_pivotal_lift_and_integral_numerical_core
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj →
      letI := CentreRigid.rigidCenter (C := C.Obj)
      ∃ (p : Dimensions.PivotalStructure (C := C.Obj))
        (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
        (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
        (hcompat : ∀ Z : CategoryTheory.Center C.Obj,
          (pZ.iso Z).hom.f ≫ (CentreInduction.forgetDoubleDualIso C Z).hom = (p.iso Z.1).hom),
        letI := compatibleCenterFusion C p hsimple pZ hcompat
        let D := Integrate.bundledCenter C
        (Modular.categoricalS D pZ).det ≠ 0 ∧
        (∀ y ∈ numericalProductCore C pZ,
          ∃ z : ℤ, Modular.simpleDimension D pZ y = z)) : TargetStatement.{v,u} := by
  apply target_of_compatible_center_and_integral_numerical_core
  intro C hPU hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  obtain ⟨p, hsimple, pZ, hcompat, hdet, hintegral⟩ := hCenter C hPU hF
  exact ⟨inferInstance, p, hsimple, pZ, hcompat, hdet, hintegral⟩

end PropertyF.Ground
