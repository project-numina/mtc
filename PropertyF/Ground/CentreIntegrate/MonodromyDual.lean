module
public import PropertyF.Ground.CentreCabling.ImageCore
public import PropertyF.Ground.Cabling.GeneralDual
public import PropertyF.Ground.Fusion.GeneratedRigidity
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open PropertyF.Ground
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreIntegrate
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false

/-- Trivial double braiding is symmetric. -/
theorem doubleBraiding_eq_one_symm {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (X Y : D) (h : Modular.doubleBraiding X Y = 𝟙 _) :
    Modular.doubleBraiding Y X = 𝟙 _ := by
  unfold Modular.doubleBraiding at *
  apply (cancel_epi (β_ X Y).hom).mp
  simp only [← Category.assoc, h, Category.id_comp, Category.comp_id]

/-- A self-transparent object centralizes the objects it generates. -/
theorem self_doubleBraiding_eq_one_generated (D : BraidedFusionCategory.{v,u}) (X Y : D.Obj)
    (h : Modular.doubleBraiding X X = 𝟙 _) (hY : PropertyF.GeneratedBy X Y) :
    Modular.doubleBraiding X Y = 𝟙 _ := by
  have hpow (n : ℕ) : Modular.doubleBraiding X (PropertyF.tensorPower X n) = 𝟙 _ := by
    induction n with
    | zero => exact Modular.doubleBraiding_unit X
    | succ n ih =>
      change Modular.doubleBraiding X (X ⊗ PropertyF.tensorPower X n) = 𝟙 _
      exact CentreCabling.doubleBraiding_eq_one_tensor_right X X _ h ih
  obtain ⟨n, k, ⟨r⟩⟩ := hY
  have hb : Modular.doubleBraiding (⨁ (fun i : Fin n => PropertyF.tensorPower X (k i))) X = 𝟙 _ := by
    apply CentreCabling.doubleBraiding_eq_one_biproduct
    intro i
    exact doubleBraiding_eq_one_symm X _ (hpow (k i))
  exact doubleBraiding_eq_one_symm _ _ (CentreCabling.doubleBraiding_eq_one_of_retract r X hb)

/-- The dual of a self-transparent object is transparent to it. -/
theorem self_doubleBraiding_eq_one_rightDual (D : BraidedFusionCategory.{v,u}) (X : D.Obj)
    (h : Modular.doubleBraiding X X = 𝟙 _) :
    Modular.doubleBraiding X (Xᘁ) = 𝟙 _ :=
  self_doubleBraiding_eq_one_generated D X _ h (Ground.generatedBy_rightDual D X)

end PropertyF.Ground.CentreIntegrate
