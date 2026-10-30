module
public import MTC.Braided.Trace.ThreeRigidity
public import MTC.Modular.SAdditivity
public import MTC.Center.ProductClosure
public import MTC.Fusion.UnitPower
public import MTC.PropertyF.Reduction.CenterBundle

/-!
# Centrality of product retracts

Double-braiding centrality is preserved by retracts and finite biproducts, so
it extends from simple constituents to all objects in a retract-closed class.
-/

@[expose] public noncomputable section
open PropertyF.Ground.Modular (doubleBraiding)
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreCabling
universe v u
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Centrality descends along a split inclusion. -/
theorem doubleBraiding_eq_one_of_retract {X Z : D} (r : Retract X Z) {Y : D}
    (h : doubleBraiding Z Y = 𝟙 _) : doubleBraiding X Y = 𝟙 _ := by
  simpa [h, Category.assoc, ← comp_whiskerRight, r.retract] using
    congrArg (fun t ↦ t ≫ (r.r ▷ Y)) (Modular.doubleBraiding_natural_left r.i Y)

open scoped Classical in
/-- If all the components of a finite biproduct centralize an object, their
biproduct centralizes it. -/
theorem doubleBraiding_eq_one_biproduct [Abelian D] [MonoidalPreadditive D]
    {J : Type} [Fintype J] {V : J → D} {Y : D}
    (h : ∀ i, doubleBraiding (V i) Y = 𝟙 _) :
    doubleBraiding (⨁ V) Y = 𝟙 _ :=
  (cancel_epi (rightDistributor V Y).inv).mp <| biproduct.hom_ext' _ _ fun i ↦ by
    rw [biproduct_ι_comp_rightDistributor_inv_assoc,
      ← Modular.doubleBraiding_natural_left (biproduct.ι V i) Y, h i]
    simp

/-- A retract-closed object class centralizes Y when the constituents of a
finite decomposition of X do. -/
theorem doubleBraiding_eq_one_of_constituents [Abelian D] [MonoidalPreadditive D]
    {ι : Type} [Fintype ι] (S : ι → D) {m : ι → ℕ} {X Y : D}
    (e : X ≅ ⨁ (fun a : Σ i, Fin (m i) ↦ S a.1)) (P : D → Prop)
    (hP : ∀ {X Z : D}, Retract X Z → P Z → P X) (hX : P X)
    (h : ∀ i, P (S i) → doubleBraiding (S i) Y = 𝟙 _) :
    doubleBraiding X Y = 𝟙 _ := by
  classical
  let V : (Σ i, Fin (m i)) → D := fun a ↦ S a.1
  exact doubleBraiding_eq_one_of_retract (Retract.ofIso e) <|
    doubleBraiding_eq_one_biproduct fun a ↦ h a.1 <| hP
      ((Retract.mk (biproduct.ι V a) (biproduct.π V a) (biproduct.ι_π_self V a)).trans (Retract.ofIso e.symm)) hX

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
    {Z : CategoryTheory.Center D.Obj} (hZ : ProductRetract Z) : ProductRetract (Zᘁ) :=
  productRetract_generatedBy hZ (Ground.generatedBy_rightDual Z)

end PropertyF.Ground.Centre
