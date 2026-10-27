module
public import PropertyF.Ground.Cabling.MoveHeadContext
public import PropertyF.Ground.Cabling.PowerGeneral
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The crossing of two tensor-power blocks, expressed on their common
right-associated tensor power. -/
def blockSwap (X : C) (a b : ℕ) : Aut (tensorPower X (a+b)) := Aut.of (
  (tensorPowerTensorIso X a b).symm ≪≫
    β_ (tensorPower X a) (tensorPower X b) ≪≫
      tensorPowerTensorIso X b a ≪≫
        eqToIso (congrArg (tensorPower X) (Nat.add_comm b a)))

/-- The left-empty power comparison reduces to the left unitor. -/
theorem powerTensor_zero_left (X : C) (n : ℕ) :
    (tensorPowerTensorIso X 0 n).hom ≫
      eqToHom (congrArg (tensorPower X) (Nat.zero_add n)) = (λ_ (tensorPower X n)).hom := by
  let h : tensorPower X (0+n) = tensorPower X n := congrArg (tensorPower X) (Nat.zero_add n)
  change (cast (congrArg (fun Z : C => (𝟙_ C ⊗ tensorPower X n) ≅ Z) h.symm)
    (λ_ (tensorPower X n))).hom ≫ eqToHom h = _
  exact castIso_hom_comp h (λ_ (tensorPower X n))

set_option backward.isDefEq.respectTransparency false in
/-- Crossing an empty block is the identity. -/
theorem blockSwap_zero_left (X : C) (b : ℕ) : blockSwap X 0 b = 1 := by
  let E := tensorPowerTensorIso X 0 b
  let h : tensorPower X (0+b) = tensorPower X b := congrArg (tensorPower X) (Nat.zero_add b)
  have hE : E ≪≫ eqToIso h = λ_ (tensorPower X b) := by
    apply Iso.ext
    exact powerTensor_zero_left X b
  have hEinv : E.inv = eqToHom h ≫ (λ_ (tensorPower X b)).inv := by
    have he : E.symm = (eqToIso h) ≪≫ (λ_ (tensorPower X b)).symm := by
      rw [← hE]
      apply Iso.ext
      simp
    exact congrArg Iso.hom he
  apply Aut.ext
  apply Iso.ext
  change E.inv ≫ (β_ (𝟙_ C) (tensorPower X b)).hom ≫
    (tensorPowerTensorIso X b 0).hom ≫ eqToHom h.symm = 𝟙 _
  rw [hEinv, braiding_tensorUnit_left, powerTensor_zero_right X b]
  simp [Category.assoc]
set_option backward.isDefEq.respectTransparency false in
/-- Crossing an empty block on the right is the identity. -/
theorem blockSwap_zero_right (X : C) (a : ℕ) : blockSwap X a 0 = 1 := by
  let E := tensorPowerTensorIso X a 0
  let h : tensorPower X (0+a) = tensorPower X a := congrArg (tensorPower X) (Nat.zero_add a)
  have hE : E = ρ_ (tensorPower X a) := Iso.ext (powerTensor_zero_right X a)
  apply Aut.ext
  apply Iso.ext
  change E.inv ≫ (β_ (tensorPower X a) (𝟙_ C)).hom ≫
    (tensorPowerTensorIso X 0 a).hom ≫ eqToHom h = 𝟙 _
  rw [hE, braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [powerTensor_zero_left X a]
  simp
end PropertyF
