module
public import PropertyF.Ground.Dimensions.IteratedTrace
public import PropertyF.Ground.Dimensions.PivotalDual

/-! Left partial trace for the strand-deletion identity. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Close the first factor using the pivotal left dual. -/
def leftPartialTrace (p : Dimensions.PivotalStructure (C := C)) (X Y : C) :
    End (X ⊗ Y) →ₗ[ℂ] End Y where
  toFun f := End.of ((λ_ Y).inv ≫
    ((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ ((Xᘁ) ◁ (p.iso X).inv)) ▷ Y) ≫
    (α_ (Xᘁ) X Y).hom ≫ ((Xᘁ) ◁ f.asHom) ≫
    (α_ (Xᘁ) X Y).inv ≫ (ε_ X (Xᘁ) ▷ Y) ≫ (λ_ Y).hom)
  map_add' f g := by
    apply End.ext
    simp
  map_smul' z f := by
    apply End.ext
    simp

/-- Inserting a map on the untraced right factor. -/
def insertLeftIdentity (X Y : C) (a : End Y) : End (X ⊗ Y) :=
  End.of (X ◁ a.asHom)

theorem leftPartialTrace_right (p : Dimensions.PivotalStructure (C := C))
    (X Y : C) (a : End Y) (f : End (X ⊗ Y)) :
    leftPartialTrace p X Y (f * insertLeftIdentity X Y a) =
      leftPartialTrace p X Y f * a := by
  apply End.ext
  simp only [leftPartialTrace, insertLeftIdentity, LinearMap.coe_mk, AddHom.coe_mk,
    End.mul_asHom, whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_right_assoc]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]

/-- Closing the first factor commutes with a spectator factor on the right. -/
theorem leftPartialTrace_whiskerRight (p : Dimensions.PivotalStructure (C := C))
    (X Y Z : C) (f : End (X ⊗ Y)) :
    leftPartialTrace p X (Y ⊗ Z) (End.of
      ((α_ X Y Z).inv ≫ (f.asHom ▷ Z) ≫ (α_ X Y Z).hom)) =
      End.of ((leftPartialTrace p X Y f).asHom ▷ Z) := by
  apply End.ext
  simp only [leftPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

/-- Schur's lemma identifies the partial trace on a simple surviving strand
once compatibility with total trace is known. -/
theorem leftPartialTrace_simple_of_trace_compatibility [CategoryTheory.Limits.HasKernels C]
    (X Y : C) [Simple Y] [FiniteDimensional ℂ (Y ⟶ Y)]
    (p : Dimensions.PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (f : End (X ⊗ Y))
    (hd : scalar (p.rightTrace (𝟙 Y)) ≠ 0)
    (htrace : p.rightTrace (leftPartialTrace p X Y f).asHom = p.rightTrace f.asHom) :
    leftPartialTrace p X Y f =
      (scalar (p.rightTrace f.asHom) / scalar (p.rightTrace (𝟙 Y))) • (1 : End Y) := by
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ
    (leftPartialTrace p X Y f).asHom
  have hscalar : scalar (p.rightTrace (leftPartialTrace p X Y f).asHom) =
      c * scalar (p.rightTrace (𝟙 Y)) := by
    rw [← hc, p.rightTrace_smul]
    simp
  have hcval : c = scalar (p.rightTrace f.asHom) / scalar (p.rightTrace (𝟙 Y)) := by
    apply (eq_div_iff hd).2
    exact hscalar.symm.trans (congrArg scalar htrace)
  apply End.ext
  simpa [← hcval] using hc.symm

end PropertyF.Ground.CentreCalculus
