module
public import PropertyF.Ground.Cabling.PrefixPower
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

set_option backward.isDefEq.respectTransparency false in
/-- The left-prefix comparison is the standard comparison followed by
transport of the total strand count. -/
theorem prefixPowerIso_hom (X : C) (m k : ℕ) :
    (prefixPowerIso X m k).hom = (tensorPowerTensorIso X k m).hom ≫
      eqToHom (congrArg (tensorPower X) (Nat.add_comm k m)) := by
  induction k with
  | zero =>
    change (λ_ (tensorPower X m)).hom = (tensorPowerTensorIso X 0 m).hom ≫
      eqToHom (congrArg (tensorPower X) (Nat.zero_add m))
    exact (powerTensor_zero_left X m).symm
  | succ k ih =>
    let h₁ : tensorPower X ((k+1)+m) = X ⊗ tensorPower X (k+m) := by
      change tensorPower X ((k+1)+m) = tensorPower X ((k+m)+1)
      congr 1; omega
    let h₂ : tensorPower X (k+m) = tensorPower X (m+k) :=
      congrArg (tensorPower X) (Nat.add_comm k m)
    have h := powerTensor_succ_general X k m
    change (tensorPowerTensorIso X (k+1) m).hom ≫ eqToHom h₁ =
      (α_ X (tensorPower X k) (tensorPower X m)).hom ≫
        (𝟙 X ⊗ₘ (tensorPowerTensorIso X k m).hom) at h
    have hmapGen {A B : C} (h : A = B) : (𝟙 X ⊗ₘ eqToHom h) =
        eqToHom (congrArg (fun Z : C => X ⊗ Z) h) := by cases h; simp
    have htrans : eqToHom h₁ ≫ (𝟙 X ⊗ₘ eqToHom h₂) =
        eqToHom (congrArg (tensorPower X) (Nat.add_comm (k+1) m)) := by
      rw [hmapGen, eqToHom_trans]
    calc
      (prefixPowerIso X m (k+1)).hom =
          (α_ X (tensorPower X k) (tensorPower X m)).hom ≫
            (𝟙 X ⊗ₘ (prefixPowerIso X m k).hom) := by rfl
      _ = (α_ X (tensorPower X k) (tensorPower X m)).hom ≫
          (𝟙 X ⊗ₘ ((tensorPowerTensorIso X k m).hom ≫ eqToHom h₂)) := by rw [ih]
      _ = ((tensorPowerTensorIso X (k+1) m).hom ≫ eqToHom h₁) ≫
          (𝟙 X ⊗ₘ eqToHom h₂) := by
        rw [h]
        simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]
      _ = _ := by rw [Category.assoc, htrans]
/-- Cabled maps remain cabled after adding any tensor-power block on the left. -/
theorem cableHom_prepend_left (X : C) {m n : ℕ}
    (f : tensorPower X m ⟶ tensorPower X n) (hf : cableHom X m n f) (k : ℕ) :
    cableHom X (k+m) (k+n)
      ((tensorPowerTensorIso X k m).inv ≫ (tensorPower X k ◁ f) ≫
        (tensorPowerTensorIso X k n).hom) := by
  obtain ⟨h, a, hf⟩ := hf
  subst n
  simp only [eqToHom_refl, Category.comp_id] at hf
  subst f
  let q := eqToIso (congrArg (tensorPower X) (Nat.add_comm k m))
  let b := addLeftAutAllIter X m k a.val
  have hb : b ∈ braidImageAllSubgroup X (m+k) := addLeftAutAllIter_mem X m a.val a.property k
  have hc : q.symm.conjAut b ∈ braidImageAllSubgroup X (k+m) := by
    have hh := (braidImageAllSubgroup_transport X (Nat.add_comm m k) b).mp hb
    have hsymm {A B : C} (h : A = B) : (eqToIso h).symm = eqToIso h.symm := by cases h; rfl
    change (eqToIso (congrArg (tensorPower X) (Nat.add_comm k m))).symm.conjAut b ∈ _
    rw [hsymm]
    exact hh
  let c : braidImageAllSubgroup X (k+m) := ⟨q.symm.conjAut b, hc⟩
  refine ⟨rfl, c, ?_⟩
  simp only [eqToHom_refl, Category.comp_id]
  change (tensorPowerTensorIso X k m).inv ≫ (tensorPower X k ◁ a.val.asIso.hom) ≫
    (tensorPowerTensorIso X k m).hom = (q.symm.conjAut b).asIso.hom
  have hp : prefixPowerIso X m k = (tensorPowerTensorIso X k m) ≪≫ q := by
    apply Iso.ext
    exact prefixPowerIso_hom X m k
  have hh := addLeftAutAllIter_hom X m k a.val
  change b.asIso.hom = _ at hh
  simp only [Iso.conjAut_apply, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv]
  rw [hh, hp]
  simp [Iso.trans_inv, Iso.trans_hom, Category.assoc]
end PropertyF
