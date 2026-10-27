module
public import PropertyF.Ground.Integrate.PivotalOnlyReduction
public import PropertyF.Ground.CentreIntegrate.TwistDual
public import PropertyF.Ground.CentreCalculus.LeftTensorTrace

/-! The actual symmetric-core integrality follows from dual-pair balancing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- A self-transparent simple has integral dimension if twist balancing holds
on its dual pair. The balancing identity remains an explicit hypothesis. -/
theorem simple_integral_of_self_transparency_and_dual_balancing
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hp : p.IsSpherical)
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (i : Fin (rank C))
    (hself : Modular.doubleBraiding (simples C i) (simples C i) = 𝟙 _)
    (hbal : (Dimensions.pivotalBraidedTwist C p ((simples C i) ⊗ ((simples C i)ᘁ))).hom =
      Modular.doubleBraiding (simples C i) ((simples C i)ᘁ) ≫
        ((Dimensions.pivotalBraidedTwist C p (simples C i)).hom ⊗ₘ
          (Dimensions.pivotalBraidedTwist C p ((simples C i)ᘁ)).hom)) :
    ∃ z : ℤ, Modular.simpleDimension C p i = z := by
  letI : Simple (simples C i) := simples_simple C i
  have hs := CentreIntegrate.twist_sign_of_spherical_self_transparency_and_balancing C p hp i hself hbal
  have hm := CentreCalculus.integral_of_spherical_and_twist_sign C p hp hdim (simples C i) hself hs
  obtain ⟨m, hm⟩ := hm
  rw [fpDimension_simple] at hm
  refine ⟨m, ?_⟩
  rw [hdim i, hm]
  norm_cast

/-- Every actual symmetric-core simple has integral dimension provided twist
balancing holds on its dual pair. -/
theorem symmetricCore_integral_of_dual_balancing
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hp : p.IsSpherical)
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ))
    (hbal : ∀ i ∈ CentreCabling.symmetricCore C,
      let Z := Integrate.bundledCenter C
      (Dimensions.pivotalBraidedTwist Z p ((simples Z i) ⊗ ((simples Z i)ᘁ))).hom =
        Modular.doubleBraiding (simples Z i) ((simples Z i)ᘁ) ≫
          ((Dimensions.pivotalBraidedTwist Z p (simples Z i)).hom ⊗ₘ
            (Dimensions.pivotalBraidedTwist Z p ((simples Z i)ᘁ)).hom)) :
    ∀ i ∈ CentreCabling.symmetricCore C,
      ∃ z : ℤ, Modular.simpleDimension (Integrate.bundledCenter C) p i = z := by
  intro i hi
  apply simple_integral_of_self_transparency_and_dual_balancing (Integrate.bundledCenter C) p hp hdim i
  · exact CentreCalculus.commonCentralizer_self (simples (Integrate.bundledCenter C) i) hi.1 hi.2
  · exact hbal i hi

/-- The target follows from base pivotal existence and three explicit centre
conditions: nondegenerate S, dual-pair twist balancing on the symmetric core,
and finite mixed monodromy on the specified canonical-image labels. -/
theorem target_of_pivotal_base_balancing_and_image_monodromy
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}) (hpu : PseudoUnitary C),
      HasPropertyF C.Obj →
      ∃ (p : Dimensions.PivotalStructure (C := C.Obj)),
        letI := CentreRigid.rigidCenter (C := C.Obj)
        letI := centerFusionOfPivotalPseudoUnitary C p hpu
        let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
        let D := Integrate.bundledCenter C
        (Modular.categoricalS D pZ).det ≠ 0 ∧
        (∀ i ∈ CentreCabling.symmetricCore C,
          (Dimensions.pivotalBraidedTwist D pZ ((simples D i) ⊗ ((simples D i)ᘁ))).hom =
            Modular.doubleBraiding (simples D i) ((simples D i)ᘁ) ≫
              ((Dimensions.pivotalBraidedTwist D pZ (simples D i)).hom ⊗ₘ
                (Dimensions.pivotalBraidedTwist D pZ ((simples D i)ᘁ)).hom)) ∧
        (∀ y, (∀ a ∈ CentreCabling.imageLabels C,
          Modular.categoricalS D pZ a y = Modular.simpleDimension D pZ a * Modular.simpleDimension D pZ y) →
          ∀ a ∈ CentreCabling.imageLabels C,
            IsOfFinOrder (End.of (Modular.doubleBraiding (simples D a) (simples D y))))) :
    TargetStatement.{v,u} := by
  apply target_of_center_image_monodromy_no_square
  intro C hpu hF
  obtain ⟨p, hdet, hbal, hfinite⟩ := hCenter C hpu hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
  have hs := Classical.choose_spec (Classical.choose_spec
    (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu))
  obtain ⟨hspherical, hd, _, _⟩ := hs
  change ∀ i, Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ
    (simples (Integrate.bundledCenter C) i) = (fpSimple (Integrate.bundledCenter C) i : ℂ) at hd
  have hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) pZ i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ) := by
    intro i
    simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
      Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv] using hd i
  exact ⟨CentreRigid.rigidCenter, inferInstance, pZ, hspherical, hdim, hdet,
    symmetricCore_integral_of_dual_balancing C pZ hspherical hdim hbal, hfinite⟩

end PropertyF.Ground
