module
public import PropertyF.Ground.Cabling.FusionCycle
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF.Ground.Cabling
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every generator has its right dual in its generated subcategory. -/
theorem generatedBy_rightDual (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) :
    GeneratedBy X (Xᘁ) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Ground.simples_decompose D X
  let V : (Σ i, Fin (m i)) → D.Obj := fun p => Ground.simples D p.1
  let B : D.Obj := ⨁ V
  let r : Retract (Xᘁ) (Bᘁ) := {
    i := e.invᘁ
    r := e.homᘁ
    retract := by rw [← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id] }
  let rb : Retract (Bᘁ) (⨁ fun i => (V i)ᘁ) := {
    i := biproduct.lift fun i => (biproduct.ι V i)ᘁ
    r := biproduct.desc fun i => (biproduct.π V i)ᘁ
    retract := by
      rw [biproduct.lift_desc]
      simp only [← comp_rightAdjointMate, ← rightAdjointMate_sum]
      change (∑ i, biproduct.π V i ≫ biproduct.ι V i)ᘁ = 𝟙 (Bᘁ)
      rw [biproduct.total, rightAdjointMate_id] }
  have hg : GeneratedBy X (⨁ fun i => (V i)ᘁ) := by
    apply generatedBy_finiteBiproduct
    intro i
    have hi : Retract (V i) X := (Retract.mk (biproduct.ι V i) (biproduct.π V i)
      (by simp)).trans (Retract.ofIso e.symm)
    have hV : GeneratedBy X (V i) := generatedBy_retract (generatedBy_self X) hi
    letI : Simple (V i) := Ground.simples_simple D i.1
    exact generatedBy_trans hV (generatedBy_rightDual_of_simple D (V i))
  exact generatedBy_retract hg (r.trans rb)

/-- Generated full subcategories of genuine braided fusion categories are rigid. -/
@[instance_reducible] def generatedCategoryRigid
    (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) :
    RigidCategory (generatedCategory X) :=
  generatedCategoryRigidOfGeneratorDual X (generatedBy_rightDual D X)
end PropertyF.Ground.Cabling
