module
public import PropertyF.Ground.CentreRigid.SimpleTensor
public import PropertyF.Ground.CentreRigid.Unit
public import PropertyF.Ground.CentreInduction.UnitTest

/-! The normalized mate supplies the chosen base dual in rank one. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreRigid
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false in
/-- The tensor law holds when the first test object is isomorphic to the unit. -/
theorem tensor_iso_unit_left (C : BraidedFusionCategory.{v,u}) (Z : Center C.Obj) (U V : C.Obj)
    (e : U ≅ 𝟙_ C.Obj) :
    (CentreRigid.leftNatU C Z V).app U = (CentreRigid.rightNatU C Z V).app U := by
  let F := tensorRight V ⋙ tensorLeft Z.1ᘁ
  let G := tensorRight V ⋙ tensorRight Z.1ᘁ
  let a := CentreRigid.leftNatU C Z V
  let b := CentreRigid.rightNatU C Z V
  have hu : a.app (𝟙_ C.Obj) = b.app (𝟙_ C.Obj) := CentreRigid.dualCrossing_tensor_unit_left Z V
  apply (cancel_mono (G.map e.hom)).1
  rw [← a.naturality, ← b.naturality, hu]

set_option backward.isDefEq.respectTransparency false in
/-- In rank one the normalized dual mate satisfies the tensor law. -/
theorem tensor_of_rank_one (C : BraidedFusionCategory.{v,u}) [Subsingleton (Fin (rank C))]
    (Z : Center C.Obj) :
  ∀ U V, ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
    (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
      (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫
        (α_ _ _ _).inv := by
  intro U V
  change (CentreRigid.leftNatU C Z V).app U = (CentreRigid.rightNatU C Z V).app U
  have h : CentreRigid.leftNatU C Z V = CentreRigid.rightNatU C Z V := by
    apply CentreInduction.natTrans_ext_on_simples C
    intro i
    have hi : i = unitIndex C := Subsingleton.elim _ _
    subst i
    obtain ⟨e⟩ := unitIndex_iso C
    let G := tensorRight V ⋙ tensorRight Z.1ᘁ
    let a := CentreRigid.leftNatU C Z V
    let b := CentreRigid.rightNatU C Z V
    have hu : a.app (𝟙_ C.Obj) = b.app (𝟙_ C.Obj) := CentreRigid.dualCrossing_tensor_unit_left Z V
    apply (cancel_mono (G.map e.hom)).1
    rw [← a.naturality, ← b.naturality, hu]
  exact congrArg (fun a => a.app U) h

set_option backward.isDefEq.respectTransparency false in
/-- The normalized mate gives the actual centre a rigid structure in rank one,
with underlying right dual, evaluation and coevaluation inherited from the base. -/
@[instance_reducible] def rigidOfRankOne (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] : RigidCategory (Center C.Obj) := by
  apply rigidOfMateCoherence
  intro Z
  let hTensor := tensor_of_rank_one C Z
  refine ⟨hTensor, ?_, ?_⟩
  · exact CentreInduction.all_maps_central_of_rank_one C (𝟙_ (Center C.Obj))
      (Z ⊗ dualObject Z hTensor) (η_ Z.1 Z.1ᘁ)
  · exact CentreInduction.all_maps_central_of_rank_one C (dualObject Z hTensor ⊗ Z)
      (𝟙_ (Center C.Obj)) (ε_ Z.1 Z.1ᘁ)

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the selected centre right dual gives the selected base dual. -/
theorem rigidOfRankOne_forget_dual (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] (Z : Center C.Obj) :
    letI := rigidOfRankOne C
    (Zᘁ).1 = Z.1ᘁ := by rfl

set_option backward.isDefEq.respectTransparency false in
/-- The selected coevaluation forgets to the base coevaluation. -/
theorem rigidOfRankOne_forget_coevaluation (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] (Z : Center C.Obj) :
    letI := rigidOfRankOne C
    (η_ Z (Zᘁ)).f = η_ Z.1 Z.1ᘁ := by rfl

set_option backward.isDefEq.respectTransparency false in
/-- The selected evaluation forgets to the base evaluation. -/
theorem rigidOfRankOne_forget_evaluation (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] (Z : Center C.Obj) :
    letI := rigidOfRankOne C
    (ε_ Z (Zᘁ)).f = ε_ Z.1 Z.1ᘁ := by rfl

end PropertyF.Ground.CentreRigid
