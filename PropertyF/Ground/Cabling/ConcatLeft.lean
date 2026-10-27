module
public import PropertyF.Ground.Cabling.ConcatBase
public import PropertyF.Ground.Cabling.PowerGeneral
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

set_option backward.isDefEq.respectTransparency false in
theorem concatPowerIso_zero_left (X : C) (n : ℕ) :
    (concatPowerIso X 0 n).hom ≫
      eqToHom (congrArg (tensorPower X) (Nat.zero_add n)) = (λ_ (tensorPower X n)).hom := by
  induction n with
  | zero =>
    simp only [concatPowerIso, tensorPower, eqToHom_refl, Category.comp_id]
    change (ρ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom
    monoidal
  | succ n ih =>
    have hmapGen {A B : C} (h : A = B) : (eqToHom h ▷ X) =
      eqToHom (congrArg (fun Z : C => Z ⊗ X) h) := by cases h; simp
    have h₁ : tensorPower X (0+n) = tensorPower X n := congrArg (tensorPower X) (Nat.zero_add n)
    have h₂ : tensorPower X (0+(n+1)) = tensorPower X (n+1) := congrArg (tensorPower X) (Nat.zero_add (n+1))
    have hnatGen (p q : ℕ) (h : p = q) :
        (appendIso X p).hom ≫ eqToHom (congrArg (fun v => tensorPower X (v+1)) h) =
          (eqToHom (congrArg (tensorPower X) h) ▷ X) ≫ (appendIso X q).hom := by
      cases h
      simp
    have hnat : (appendIso X (0+n)).hom ≫ eqToHom h₂ =
        (eqToHom h₁ ▷ X) ≫ (appendIso X n).hom := hnatGen _ _ (Nat.zero_add n)
    have hl : (concatPowerIso X 0 (n+1)).hom =
      ((𝟙 (𝟙_ C) ⊗ₘ (appendIso X n).inv) ≫ (α_ (𝟙_ C) (tensorPower X n) X).inv ≫
        ((concatPowerIso X 0 n).hom ▷ X) ≫ (appendIso X (0+n)).hom) := by
      dsimp [concatPowerIso, tensorIso_hom, Iso.trans_hom, Iso.symm_hom]
      simp [tensorPower, tensorHom_id]
    rw [hl]
    simp only [Category.assoc, hnat, ← comp_whiskerRight_assoc, ih]
    change (𝟙 (𝟙_ C) ⊗ₘ (appendIso X n).inv) ≫
      (α_ (𝟙_ C) (tensorPower X n) X).inv ≫
        ((λ_ (tensorPower X n)).hom ▷ X) ≫ (appendIso X n).hom =
          (λ_ (X ⊗ tensorPower X n)).hom
    have ht : (α_ (𝟙_ C) (tensorPower X n) X).inv ≫ ((λ_ (tensorPower X n)).hom ▷ X) =
        (λ_ (tensorPower X n ⊗ X)).hom := by monoidal
    simp only [id_tensorHom, Category.assoc]
    rw [reassoc_of% ht]
    rw [leftUnitor_naturality_assoc]
    simp only [Iso.inv_hom_id, Category.comp_id]
    rfl
/-- Both normalizations agree when the left block is empty. -/
theorem concatPowerIso_eq_zero_left (X : C) (n : ℕ) :
    concatPowerIso X 0 n = tensorPowerTensorIso X 0 n := by
  apply Iso.ext
  apply (cancel_mono (eqToHom (congrArg (tensorPower X) (Nat.zero_add n)))).mp
  rw [concatPowerIso_zero_left, powerTensor_zero_left]
end PropertyF
