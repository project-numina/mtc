module
public import PropertyF.Ground.Cabling.BlockSwap
public import PropertyF.Ground.Cabling.CablingDiagram
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

set_option backward.isDefEq.respectTransparency false in
/-- Normalizing a left singleton agrees with removal of its unit factor. -/
theorem powerTensor_one_left (X : C) (b : ℕ) :
    (tensorPowerTensorIso X 1 b).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : 1+b=b+1)) =
        (ρ_ X).hom ▷ tensorPower X b := by
  let h₁ : tensorPower X (1+b) = X ⊗ tensorPower X (0+b) := by
    change tensorPower X (1+b) = tensorPower X ((0+b)+1)
    congr 1; omega
  let h₂ : tensorPower X (0+b) = tensorPower X b := congrArg (tensorPower X) (Nat.zero_add b)
  have h := powerTensor_succ_general X 0 b
  change (tensorPowerTensorIso X 1 b).hom ≫ eqToHom h₁ =
    (α_ X (𝟙_ C) (tensorPower X b)).hom ≫
      (𝟙 X ⊗ₘ (tensorPowerTensorIso X 0 b).hom) at h
  have hmapGen {A B : C} (h : A = B) : (𝟙 X ⊗ₘ eqToHom h) =
      eqToHom (congrArg (fun Z : C => X ⊗ Z) h) := by
    cases h
    simp
  have hmap := hmapGen h₂
  have htrans : eqToHom h₁ ≫ (𝟙 X ⊗ₘ eqToHom h₂) =
      eqToHom (congrArg (tensorPower X) (by omega : 1+b=b+1)) := by
    rw [hmap, eqToHom_trans]
  calc
    (tensorPowerTensorIso X 1 b).hom ≫ eqToHom (congrArg (tensorPower X) (by omega : 1+b=b+1)) =
        ((tensorPowerTensorIso X 1 b).hom ≫ eqToHom h₁) ≫ (𝟙 X ⊗ₘ eqToHom h₂) := by
      rw [← htrans, Category.assoc]
    _ = ((α_ X (𝟙_ C) (tensorPower X b)).hom ≫
        (𝟙 X ⊗ₘ (tensorPowerTensorIso X 0 b).hom)) ≫ (𝟙 X ⊗ₘ eqToHom h₂) := by rw [h]
    _ = _ := by
      simp only [id_tensorHom, Category.assoc, ← whiskerLeft_comp]
      rw [powerTensor_zero_left X b]
      monoidal
set_option backward.isDefEq.respectTransparency false in
/-- Crossing a singleton block with a tensor-power block is the one-strand
crossing after transporting the common total strand count. -/
theorem blockSwap_one_left (X : C) (b : ℕ) :
    (eqToIso (congrArg (tensorPower X) (by omega : 1+b=b+1))).conjAut
      (blockSwap X 1 b) = moveHead X b := by
  let h : tensorPower X (1+b) = tensorPower X (b+1) :=
    congrArg (tensorPower X) (by omega : 1+b=b+1)
  let q := eqToIso h
  let e := tensorPowerTensorIso X 1 b
  let u := (ρ_ X) ⊗ᵢ Iso.refl (tensorPower X b)
  have he : e ≪≫ q = u := by
    apply Iso.ext
    change e.hom ≫ eqToHom h = (ρ_ X).hom ⊗ₘ 𝟙 (tensorPower X b)
    rw [tensorHom_id]
    exact powerTensor_one_left X b
  have hinv : q.inv ≫ e.inv = u.inv := by
    have hs := congrArg (fun x => x.inv) he
    simpa using hs
  apply Aut.ext
  apply Iso.ext
  change q.inv ≫ (e.inv ≫ (β_ (tensorPower X 1) (tensorPower X b)).hom ≫
    (tensorPowerTensorIso X b 1).hom ≫ eqToHom h.symm) ≫ q.hom =
    (β_ X (tensorPower X b)).hom ≫ (𝟙 (tensorPower X b) ⊗ₘ (ρ_ X).inv) ≫
      (tensorPowerTensorIso X b 1).hom
  have hcancel : eqToHom h.symm ≫ q.hom = 𝟙 _ := by simp [q]
  simp only [Category.assoc, hcancel, Category.comp_id]
  rw [← Category.assoc q.inv e.inv, hinv]
  have hn := braiding_naturality ((ρ_ X).inv) (𝟙 (tensorPower X b))
  change ((ρ_ X).inv ⊗ₘ 𝟙 (tensorPower X b)) ≫
      (β_ (tensorPower X 1) (tensorPower X b)).hom =
    (β_ X (tensorPower X b)).hom ≫
      (𝟙 (tensorPower X b) ⊗ₘ (ρ_ X).inv) at hn
  simpa [u, tensorIso_inv, Iso.refl_inv, Category.assoc] using
    congrArg (fun z => z ≫ (tensorPowerTensorIso X b 1).hom) hn
/-- Changing a strand count by equality transports membership of the braid
image along the corresponding tensor-power identification. -/
theorem braidImageAllSubgroup_transport (X : C) {m n : ℕ} (h : m = n)
    (a : Aut (tensorPower X m)) :
    a ∈ braidImageAllSubgroup X m ↔
      (eqToIso (congrArg (tensorPower X) h)).conjAut a ∈ braidImageAllSubgroup X n := by
  cases h
  have heq : (Iso.refl (tensorPower X m)).conjAut a = a := by
    apply Aut.ext
    apply Iso.ext
    simp [Iso.conjAut_apply]
  simpa only [eqToIso_refl, heq]

/-- A normalized crossing with a singleton left block is an X braid. -/
theorem blockSwap_one_left_mem (X : C) (b : ℕ) :
    blockSwap X 1 b ∈ braidImageAllSubgroup X (1+b) := by
  apply (braidImageAllSubgroup_transport X (by omega : 1+b=b+1) (blockSwap X 1 b)).mpr
  rw [blockSwap_one_left]
  cases b with
  | zero => simp [moveHead_zero, braidImageAllSubgroup]
  | succ b => simpa [braidImageAllSubgroup] using moveHead_mem_braidImage X b
end PropertyF
