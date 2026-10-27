module
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Fusion.Reciprocity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Nonvanishing of simple pivotal dimensions

Rigidity identifies the Hom space from X ⊗ X* to the tensor unit with End(X),
which is one-dimensional by Schur. Semisimplicity splits coevaluation; the
nonzero evaluation must be a nonzero multiple of that splitting. Consequently
the pivotal dimension of a simple object cannot vanish.
-/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open PropertyF.Ground.Dimensions
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u

/-- A simple object has nonzero pivotal trace of the identity. -/
theorem pivotalTrace_simple_ne_zero (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] :
    p.rightTrace (𝟙 X) ≠ 0 := by
  let _ : Simple (𝟙_ C.Obj) := Ground.IsFusionCategory.unit_simple
  let _ : FiniteDimensional ℂ (X ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  let s : 𝟙_ C.Obj ⟶ X ⊗ (Xᘁ) := ExactPairing.coevaluation X (Xᘁ)
  have hs : s ≠ 0 := by
    intro hz
    have ht := ExactPairing.evaluation_coevaluation X (Xᘁ)
    change ExactPairing.coevaluation X (Xᘁ) = 0 at hz
    rw [hz] at ht
    simp at ht
    have ht' := congrArg (fun t => (λ_ X).inv ≫ t ≫ (ρ_ X).hom) ht
    have hid : 𝟙 X = 0 := by simpa [Category.assoc] using ht'.symm
    exact id_nonzero X hid
  obtain ⟨r₀, hr₀⟩ := Ground.split_from_simple s hs
  have hr₀ne : r₀ ≠ 0 := by
    intro h
    rw [h] at hr₀
    simp at hr₀
    exact id_nonzero (𝟙_ C.Obj) hr₀.symm
  let t : X ⊗ (Xᘁ) ≅ ((Xᘁ)ᘁ) ⊗ (Xᘁ) := p.iso X ⊗ᵢ Iso.refl _
  let ev : ((Xᘁ)ᘁ) ⊗ (Xᘁ) ⟶ 𝟙_ C.Obj := ExactPairing.evaluation (Xᘁ) ((Xᘁ)ᘁ)
  have hev : ev ≠ 0 := by
    let _ : Simple ((Xᘁ)ᘁ) := Simple.of_iso (p.iso X).symm
    intro hz
    have ht := ExactPairing.coevaluation_evaluation (Xᘁ) ((Xᘁ)ᘁ)
    change ExactPairing.evaluation (Xᘁ) ((Xᘁ)ᘁ) = 0 at hz
    rw [hz] at ht
    simp at ht
    have ht' := congrArg (fun q => (ρ_ ((Xᘁ)ᘁ)).inv ≫ q ≫ (λ_ ((Xᘁ)ᘁ)).hom) ht
    have hid : 𝟙 ((Xᘁ)ᘁ) = 0 := by simpa [Category.assoc] using ht'.symm
    exact id_nonzero ((Xᘁ)ᘁ) hid
  let r : X ⊗ (Xᘁ) ⟶ 𝟙_ C.Obj := t.hom ≫ ev
  have hr : r ≠ 0 := by
    intro hz
    have h := congrArg (fun f => t.inv ≫ f) hz
    have : ev = 0 := by simpa [r, Category.assoc] using h
    exact hev this
  let e₁ := Ground.tensorRightHomLinearEquiv X (Xᘁ) ((Xᘁ)ᘁ) (𝟙_ C.Obj)
  let e₂ := CategoryTheory.Linear.homCongr ℂ (Iso.refl X) (λ_ ((Xᘁ)ᘁ))
  let e₃ := CategoryTheory.Linear.homCongr ℂ (Iso.refl X) (p.iso X).symm
  have hfin : Module.finrank ℂ (X ⊗ (Xᘁ) ⟶ 𝟙_ C.Obj) = 1 := by
    calc
      _ = Module.finrank ℂ (X ⟶ X) := (e₁.trans (e₂.trans e₃)).finrank_eq
      _ = 1 := CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X
  obtain ⟨z, hz⟩ := exists_smul_eq_of_finrank_eq_one hfin hr₀ne r
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_smul] at hz
    exact hr hz.symm
  intro hzero
  have hhom : s ≫ r = 0 := by
    have h := congrArg End.asHom hzero
    simpa [PivotalStructure.rightTrace, s, r, t, ev, tensorIso_hom] using h
  rw [← hz, Linear.comp_smul, hr₀] at hhom
  have : z • (𝟙 (𝟙_ C.Obj)) ≠ 0 := smul_ne_zero hz0 (id_nonzero _)
  exact this hhom

/-- Every simple categorical dimension is nonzero, without pseudo-unitarity. -/
theorem simpleDimension_ne_zero (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) :
    simpleDimension C p i ≠ 0 := by
  let _ : Simple (simples C i) := simples_simple C i
  have h := pivotalTrace_simple_ne_zero C p (simples C i)
  have h' := (Ground.unitScalarEquiv C).injective.ne h
  simpa [simpleDimension] using h'

end PropertyF.Ground.Modular
