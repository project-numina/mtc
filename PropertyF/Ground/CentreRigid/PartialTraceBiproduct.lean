module
public import PropertyF.Ground.CentreRigid.PartialTrace
public import PropertyF.Ground.CentreInduction.SimpleDetection

/-! Decomposition of the closed factor in pivotal partial traces. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreRigid
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false in
/-- A partial trace over a finite biproduct is the sum of its diagonal partial traces. -/
theorem partialTraceHom_biproduct {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasFiniteBiproducts C] (p : Dimensions.PivotalStructure (C := C))
    {ι : Type} [Fintype ι] [DecidableEq ι] (V : ι → C) (X Y : C)
    (g : X ⊗ (⨁ V) ⟶ Y ⊗ (⨁ V)) :
    CentreInduction.partialTraceHom p X Y (⨁ V) g =
      ∑ i, CentreInduction.partialTraceHom p X Y (V i)
        ((X ◁ biproduct.ι V i) ≫ g ≫ (Y ◁ biproduct.π V i)) := by
  classical
  have hd (i : ι) := CentreRigid.partialTraceHom_dinatural p X Y
    (biproduct.ι V i) (g ≫ (Y ◁ biproduct.π V i))
  simp only [Category.assoc, ← whiskerLeft_comp] at hd
  simp_rw [hd]
  rw [← map_sum]
  congr 1
  rw [← Preadditive.comp_sum, ← whiskerLeft_sum]
  simp

end PropertyF.Ground.CentreRigid
