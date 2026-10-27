module
public import PropertyF.Ground.Cabling.PowerExpr
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

set_option backward.isDefEq.respectTransparency false in
/-- Normalization carries the actual associator to strand-count transport. -/
theorem PowerExpr.normalize_assoc (X : C) (a b c : PowerExpr) :
    ((.tensor (.tensor a b) c : PowerExpr).normalize X).hom ≫
      eqToHom (congrArg (tensorPower X) (Nat.add_assoc a.length b.length c.length)) =
    (α_ (a.eval X) (b.eval X) (c.eval X)).hom ≫
      ((.tensor a (.tensor b c) : PowerExpr).normalize X).hom := by
  let A := a.normalize X
  let B := b.normalize X
  let D := c.normalize X
  let E := tensorPowerTensorIso X a.length b.length
  let F := tensorPowerTensorIso X (a.length+b.length) c.length
  let G := tensorPowerTensorIso X b.length c.length
  let H := tensorPowerTensorIso X a.length (b.length+c.length)
  have ha := powerTensor_assoc X a.length b.length c.length
  change ((E ⊗ᵢ Iso.refl (tensorPower X c.length)) ≪≫ F).hom ≫
      eqToHom (congrArg (tensorPower X) (Nat.add_assoc a.length b.length c.length)) =
    ((α_ (tensorPower X a.length) (tensorPower X b.length) (tensorPower X c.length)) ≪≫
      (Iso.refl _ ⊗ᵢ G) ≪≫ H).hom at ha
  change ((((A ⊗ᵢ B) ≪≫ E) ⊗ᵢ D) ≪≫ F).hom ≫
      eqToHom (congrArg (tensorPower X) (Nat.add_assoc a.length b.length c.length)) =
    (α_ (a.eval X) (b.eval X) (c.eval X)).hom ≫
      ((A ⊗ᵢ ((B ⊗ᵢ D) ≪≫ G)) ≪≫ H).hom
  calc
    _ = (((A.hom ⊗ₘ B.hom) ⊗ₘ D.hom) ≫
          (((E ⊗ᵢ Iso.refl (tensorPower X c.length)) ≪≫ F).hom ≫
            eqToHom (congrArg (tensorPower X) (Nat.add_assoc a.length b.length c.length)))) := by
      dsimp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
      monoidal
    _ = (((A.hom ⊗ₘ B.hom) ⊗ₘ D.hom) ≫
          ((α_ (tensorPower X a.length) (tensorPower X b.length) (tensorPower X c.length)) ≪≫
            (Iso.refl _ ⊗ᵢ G) ≪≫ H).hom) := by rw [ha]
    _ = _ := by
      dsimp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
      monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Associators are cabled maps. -/
theorem PowerExpr.isCable_assoc (X : C) (a b c : PowerExpr) :
    IsCable X (.tensor (.tensor a b) c) (.tensor a (.tensor b c))
      (α_ (a.eval X) (b.eval X) (c.eval X)).hom := by
  let h : (.tensor (.tensor a b) c : PowerExpr).length =
      (.tensor a (.tensor b c) : PowerExpr).length := Nat.add_assoc _ _ _
  have hn := normalize_assoc X a b c
  have hz : ((.tensor (.tensor a b) c : PowerExpr).normalize X).inv ≫
      (α_ (a.eval X) (b.eval X) (c.eval X)).hom ≫
        ((.tensor a (.tensor b c) : PowerExpr).normalize X).hom =
      eqToHom (congrArg (tensorPower X) h) := by
    rw [← hn]
    simp
  change cableHom X _ _ _
  rw [hz]
  exact cableHom_eqToHom X h
set_option backward.isDefEq.respectTransparency false in
/-- Normalization carries the left unitor to strand-count transport. -/
theorem PowerExpr.normalize_leftUnit (X : C) (a : PowerExpr) :
    ((.tensor .unit a : PowerExpr).normalize X).hom ≫
      eqToHom (congrArg (tensorPower X) (Nat.zero_add a.length)) =
    (λ_ (a.eval X)).hom ≫ (a.normalize X).hom := by
  change ((Iso.refl (𝟙_ C) ⊗ᵢ a.normalize X) ≪≫
    tensorPowerTensorIso X 0 a.length).hom ≫ _ = _
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom, Category.assoc]
  rw [powerTensor_zero_left]
  exact leftUnitor_naturality (a.normalize X).hom

set_option backward.isDefEq.respectTransparency false in
/-- Normalization carries the right unitor to the identity. -/
theorem PowerExpr.normalize_rightUnit (X : C) (a : PowerExpr) :
    ((.tensor a .unit : PowerExpr).normalize X).hom =
    (ρ_ (a.eval X)).hom ≫ (a.normalize X).hom := by
  change ((a.normalize X ⊗ᵢ Iso.refl (𝟙_ C)) ≪≫
    tensorPowerTensorIso X a.length 0).hom = _
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id, Category.assoc]
  rw [powerTensor_zero_right]
  exact rightUnitor_naturality (a.normalize X).hom

set_option backward.isDefEq.respectTransparency false in
/-- Both unitors are cabled maps. -/
theorem PowerExpr.isCable_leftUnit (X : C) (a : PowerExpr) :
    IsCable X (.tensor .unit a) a (λ_ (a.eval X)).hom := by
  let h : (.tensor .unit a : PowerExpr).length = a.length := Nat.zero_add _
  have hn := normalize_leftUnit X a
  have hz : ((.tensor .unit a : PowerExpr).normalize X).inv ≫
      (λ_ (a.eval X)).hom ≫ (a.normalize X).hom = eqToHom (congrArg (tensorPower X) h) := by
    rw [← hn]
    simp
  change cableHom X _ _ _
  rw [hz]
  exact cableHom_eqToHom X h

set_option backward.isDefEq.respectTransparency false in
theorem PowerExpr.isCable_rightUnit (X : C) (a : PowerExpr) :
    IsCable X (.tensor a .unit) a (ρ_ (a.eval X)).hom := by
  have hn := normalize_rightUnit X a
  have hz : ((.tensor a .unit : PowerExpr).normalize X).inv ≫
      (ρ_ (a.eval X)).hom ≫ (a.normalize X).hom = 𝟙 _ := by
    rw [← hn]
    simp
  change cableHom X _ _ _
  rw [hz]
  exact cableHom_id X _
set_option backward.isDefEq.respectTransparency false in
/-- The normal form of two generator atoms is the obvious right-unitor
comparison. -/
theorem PowerExpr.normalize_atom_pair (X : C) :
    ((.tensor .atom .atom : PowerExpr).normalize X) = Iso.refl X ⊗ᵢ (ρ_ X).symm := by
  have hn := powerTensor_one_left X 1
  simp only [eqToHom_refl, Category.comp_id] at hn
  apply Iso.ext
  change ((ρ_ X).inv ⊗ₘ (ρ_ X).inv) ≫ (tensorPowerTensorIso X 1 1).hom =
    𝟙 X ⊗ₘ (ρ_ X).inv
  rw [hn]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The self-braiding of the generator is its two-strand braid generator. -/
theorem PowerExpr.isCable_atom_braid (X : C) :
    IsCable X (.tensor .atom .atom) (.tensor .atom .atom) (β_ X X).hom := by
  let e := ((.tensor .atom .atom : PowerExpr).normalize X)
  have he : e = Iso.refl X ⊗ᵢ (ρ_ X).symm := normalize_atom_pair X
  have hb : e.inv ≫ (β_ X X).hom ≫ e.hom = (braidGenerator X 0 0).asIso.hom := by
    rw [he]
    dsimp only [braidGenerator, tensorIso_inv, tensorIso_hom, Iso.trans_hom, Iso.symm_hom,
      Iso.symm_inv, Iso.refl_hom, Iso.refl_inv, tensorPower]
    monoidal
  change cableHom X 2 2 _
  rw [hb]
  exact ⟨rfl, ⟨braidGenerator X 0 0, Subgroup.subset_closure (Set.mem_range_self _)⟩, by simp⟩
end PropertyF
