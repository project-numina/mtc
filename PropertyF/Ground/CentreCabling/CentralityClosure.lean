module
public import PropertyF.Ground.CentreCabling.FiniteMonodromy
public import PropertyF.Ground.CentreCabling.ProductGenerated

/-! Extend centrality from simple constituents to all product retracts. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreCabling
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Centrality descends along a split inclusion. -/
theorem doubleBraiding_eq_one_of_retract
    {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    {X Z : D} (r : Retract X Z) (Y : D)
    (h : Modular.doubleBraiding Z Y = 𝟙 _) : Modular.doubleBraiding X Y = 𝟙 _ := by
  have hh := Modular.doubleBraiding_natural_left r.i Y
  rw [h, Category.comp_id] at hh
  have hh' := congrArg (fun t => t ≫ (r.r ▷ Y)) hh
  simpa only [Category.assoc, ← comp_whiskerRight, r.retract, id_whiskerRight,
    Category.comp_id] using hh' 

/-- If all the components of a finite biproduct centralize an object, their
biproduct centralizes it. -/
theorem doubleBraiding_eq_one_biproduct
    {D : Type u} [Category.{v} D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive D] [BraidedCategory D]
    {J : Type} [Fintype J] (V : J → D) (Y : D)
    (h : ∀ i, Modular.doubleBraiding (V i) Y = 𝟙 _) :
    Modular.doubleBraiding (⨁ V) Y = 𝟙 _ := by
  classical
  apply (cancel_epi (rightDistributor V Y).inv).mp
  apply biproduct.hom_ext'
  intro i
  simp only [biproduct_ι_comp_rightDistributor_inv_assoc]
  rw [← Modular.doubleBraiding_natural_left (biproduct.ι V i) Y, h i]
  simp

/-- Any retract-closed object class centralizes Y when its simple members do. -/
theorem doubleBraiding_eq_one_of_simple_constituents
    (D : Ground.BraidedFusionCategory.{v,u}) (P : D.Obj → Prop)
    (hP : ∀ {X Z : D.Obj}, Retract X Z → P Z → P X)
    (X Y : D.Obj) (hX : P X)
    (h : ∀ i, P (simples D i) → Modular.doubleBraiding (simples D i) Y = 𝟙 _) :
    Modular.doubleBraiding X Y = 𝟙 _ := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  let V : (Σ i, Fin (m i)) → D.Obj := fun a => simples D a.1
  have hv (a : Σ i, Fin (m i)) : P (V a) := by
    apply hP ((Retract.mk (biproduct.ι V a) (biproduct.π V a) (by simp)).trans (Retract.ofIso e.symm)) hX
  have hb : Modular.doubleBraiding (⨁ V) Y = 𝟙 _ :=
    doubleBraiding_eq_one_biproduct V Y (fun a => h a.1 (hv a))
  exact doubleBraiding_eq_one_of_retract (Retract.ofIso e) Y hb

end PropertyF.Ground.CentreCabling
