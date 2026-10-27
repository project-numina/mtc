module
public import PropertyF.Ground.CentreDimensions.InvolutionTrace
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground PropertyF.Ground.Dimensions
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreIntegrate
set_option linter.style.haveILetI false
universe v u
set_option backward.isDefEq.respectTransparency false

/-- Coevaluation of a simple is nonzero. -/
theorem simple_coevaluation_ne_zero (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (i : Fin (rank C)) :
    η_ (simples C i) ((simples C i)ᘁ) ≠ 0 := by
  let X := simples C i
  have hd := pivotalDimension_simple_ne_zero C p i
  intro hz
  apply hd
  unfold pivotalDimension
  simp [PivotalStructure.rightTrace, hz, unitScalar_eq_equiv]
  rfl

/-- If the twist on the dual pair has scalar z², naturality on its cup
forces z to be a sign. -/
theorem sign_of_twist_dual_pair_scalar (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (i : Fin (rank C)) (z : ℂ)
    (htwist : (pivotalBraidedTwist C p ((simples C i) ⊗ ((simples C i)ᘁ))).hom =
      (z ^ 2) • 𝟙 _) : z = 1 ∨ z = -1 := by
  let X := simples C i
  have hn := pivotalBraidedTwist_natural C p (η_ X (Xᘁ))
  rw [pivotalBraidedTwist_unit] at hn
  simp only [Iso.refl_hom, Category.id_comp] at hn
  change η_ X (Xᘁ) ≫ (pivotalBraidedTwist C p (X ⊗ Xᘁ)).hom = η_ X (Xᘁ) at hn
  rw [htwist] at hn
  have hscalar : (z ^ 2) • η_ X (Xᘁ) = (1 : ℂ) • η_ X (Xᘁ) := by
    dsimp only [X] at hn ⊢
    simpa [Linear.comp_smul, Linear.smul_comp] using hn
  have hz : z ^ 2 = 1 := smul_left_injective ℂ (simple_coevaluation_ne_zero C p i) hscalar
  have h := sq_eq_one_iff.mp hz
  exact h

/-- Dual twist compatibility and multiplicativity on the dual pair imply the
parity sign. These two conditions remain explicit hypotheses. -/
theorem twist_sign_of_dual_and_tensor (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (i : Fin (rank C))
    (hdual : letI : Simple (simples C i) := simples_simple C i
      (pivotalBraidedTwist C p ((simples C i)ᘁ)).hom =
        pivotalBraidedTwistScalar C p (simples C i) • 𝟙 _)
    (htensor : (pivotalBraidedTwist C p ((simples C i) ⊗ ((simples C i)ᘁ))).hom =
      (pivotalBraidedTwist C p (simples C i)).hom ⊗ₘ
        (pivotalBraidedTwist C p ((simples C i)ᘁ)).hom) :
    letI : Simple (simples C i) := simples_simple C i
    pivotalBraidedTwistScalar C p (simples C i) = 1 ∨
      pivotalBraidedTwistScalar C p (simples C i) = -1 := by
  letI : Simple (simples C i) := simples_simple C i
  apply sign_of_twist_dual_pair_scalar
  rw [htensor, pivotalBraidedTwist_simple, hdual]
  simp [tensorHom_def, smul_smul, pow_two]

end PropertyF.Ground.CentreIntegrate
