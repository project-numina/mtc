module
public import PropertyF.Ground.Integrate.RigidCenterReduction
public import PropertyF.Ground.CentreInduction.PivotalLift

/-! A pivotal-component centrality test supplies the centre structure. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- Centre rigidity is constructed. A central FP-valued base pivotal
structure supplies centre fusion and sphericality; the remaining premises
are S-invertibility and integrality on the numerical product core. -/
theorem target_of_pivotal_centrality_and_integral_numerical_core
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj →
      letI := CentreRigid.rigidCenter (C := C.Obj)
      ∃ (p : Dimensions.PivotalStructure (C := C.Obj))
        (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
        (hc : CentreInduction.PivotalComponentsCentral C p),
        let pZ := CentreInduction.liftedPivotalStructure C p hc
        let hcompat := CentreInduction.liftedPivotalStructure_compatible C p hc
        letI := compatibleCenterFusion C p hsimple pZ hcompat
        let D := Integrate.bundledCenter C
        (Modular.categoricalS D pZ).det ≠ 0 ∧
        (∀ y ∈ numericalProductCore C pZ,
          ∃ z : ℤ, Modular.simpleDimension D pZ y = z)) : TargetStatement.{v,u} := by
  apply target_of_pivotal_lift_and_integral_numerical_core
  intro C hPU hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  obtain ⟨p, hsimple, hc, hdet, hintegral⟩ := hCenter C hPU hF
  exact ⟨p, hsimple, CentreInduction.liftedPivotalStructure C p hc,
    CentreInduction.liftedPivotalStructure_compatible C p hc, hdet, hintegral⟩

end PropertyF.Ground
