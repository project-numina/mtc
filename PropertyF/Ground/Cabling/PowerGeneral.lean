module
public import PropertyF.Ground.Cabling.Generated
public import PropertyF.Ground.Cabling.Strands
public import PropertyF.Ground.Calculus.StrandCoherence
public import Mathlib.Tactic
open CategoryTheory CategoryTheory.MonoidalCategory
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C]

theorem castIso_hom_comp {A B D : C} (h : B = D) (e : A ≅ D) :
    (cast (congrArg (fun Z : C => A ≅ Z) h.symm) e).hom ≫ eqToHom h = e.hom := by
  cases h
  simp

/-- Expand the standard tensor-power comparison one factor on the left. -/
theorem powerTensor_succ_general (X : C) (n m : ℕ) :
    (tensorPowerTensorIso X (n+1) m).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : (n+1)+m = (n+m)+1)) =
    ((α_ X (tensorPower X n) (tensorPower X m)) ≪≫
      (Iso.refl X ⊗ᵢ tensorPowerTensorIso X n m)).hom := by
  have h : tensorPower X ((n+1)+m) = X ⊗ tensorPower X (n+m) := by
    change tensorPower X ((n+1)+m) = tensorPower X ((n+m)+1)
    congr 1
    omega
  let e := (α_ X (tensorPower X n) (tensorPower X m)) ≪≫
    (Iso.refl X ⊗ᵢ tensorPowerTensorIso X n m)
  change (cast (congrArg (fun Z : C => ((X ⊗ tensorPower X n) ⊗ tensorPower X m) ≅ Z) h.symm) e).hom ≫ eqToHom h = e.hom
  exact castIso_hom_comp h e
end PropertyF
