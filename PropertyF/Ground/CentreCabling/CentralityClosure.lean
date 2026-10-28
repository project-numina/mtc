module
public import PropertyF.Ground.Calculus.ThreeRigidity
public import PropertyF.Ground.Modular.SAdditivity
public import PropertyF.Ground.Centre.ProductClosure
public import PropertyF.Ground.Fusion.UnitPower
public import PropertyF.Ground.Integrate.CenterBundle

/-!
# Centrality of product retracts

Double-braiding centrality is preserved by retracts and finite biproducts, so
it extends from simple constituents to all objects in a retract-closed class.
-/

@[expose] public noncomputable section
open PropertyF.Ground.Modular (doubleBraiding)
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreCabling
universe v u
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Double braiding is natural simultaneously in both strands. -/
theorem doubleBraiding_natural {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    doubleBraiding X Y ≫ (f ⊗ₘ g) =
      (f ⊗ₘ g) ≫ doubleBraiding X' Y' := by
  rw [doubleBraiding, doubleBraiding, Category.assoc,
    ← BraidedCategory.braiding_naturality g f, ← Category.assoc,
    ← BraidedCategory.braiding_naturality f g, Category.assoc]


/-- Centrality descends along a split inclusion. -/
theorem doubleBraiding_eq_one_of_retract {X Z : D} (r : Retract X Z) {Y : D}
    (h : doubleBraiding Z Y = 𝟙 _) : doubleBraiding X Y = 𝟙 _ := by
  have hh := Modular.doubleBraiding_natural_left r.i Y
  rw [h, Category.comp_id] at hh
  simpa only [Category.assoc, ← comp_whiskerRight, r.retract, id_whiskerRight,
    Category.comp_id] using congrArg (fun t ↦ t ≫ (r.r ▷ Y)) hh

/-- If all the components of a finite biproduct centralize an object, their
biproduct centralizes it. -/
theorem doubleBraiding_eq_one_biproduct [Abelian D] [MonoidalPreadditive D]
    {J : Type} [Fintype J] {V : J → D} {Y : D}
    (h : ∀ i, doubleBraiding (V i) Y = 𝟙 _) :
    doubleBraiding (⨁ V) Y = 𝟙 _ := by
  classical
  apply (cancel_epi (rightDistributor V Y).inv).mp
  apply biproduct.hom_ext'
  intro i
  rw [biproduct_ι_comp_rightDistributor_inv_assoc,
    ← Modular.doubleBraiding_natural_left (biproduct.ι V i) Y, h i]
  simp

/-- Any retract-closed object class centralizes Y when its simple members do. -/
theorem doubleBraiding_eq_one_of_simple_constituents
    (D : Ground.BraidedFusionCategory.{v,u}) (P : D.Obj → Prop)
    (hP : ∀ {X Z : D.Obj}, Retract X Z → P Z → P X)
    {X Y : D.Obj} (hX : P X)
    (h : ∀ i, P (simples D i) → doubleBraiding (simples D i) Y = 𝟙 _) :
    doubleBraiding X Y = 𝟙 _ := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  let V : (Σ i, Fin (m i)) → D.Obj := fun a => simples D a.1
  apply doubleBraiding_eq_one_of_retract (Retract.ofIso e)
  apply doubleBraiding_eq_one_biproduct
  intro a
  exact h a.1 <| hP
    ((Retract.mk (biproduct.ι V a) (biproduct.π V a) (by simp)).trans (Retract.ofIso e.symm)) hX

end PropertyF.Ground.CentreCabling

namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C]
attribute [local instance] Abelian.hasFiniteBiproducts

omit [RigidCategory C] in
/-- Once the actual centre is a rigid fusion category, duals of product
retracts are product retracts, using fusion-category generation. -/
theorem productRetract_rightDual (D : Ground.BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center D.Obj)]
    [IsFusionCategory (CategoryTheory.Center D.Obj)]
    {Z : CategoryTheory.Center D.Obj} (hZ : ProductRetract Z) :
    ProductRetract (Zᘁ) :=
  productRetract_generatedBy hZ (Ground.generatedBy_rightDual (Integrate.bundledCenter D) Z)

end PropertyF.Ground.Centre
