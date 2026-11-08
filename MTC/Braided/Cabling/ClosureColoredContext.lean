module
public import MTC.Braided.Cabling.ClosureColoredWords

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Flatten three consecutive blocks by joining the last two first. -/
def rightTripleFlatten (X : C) (a b t : ℕ) :
    tensorPower X a ⊗ (tensorPower X b ⊗ tensorPower X t) ≅
      tensorPower X (strandSum a (strandSum b t)) :=
  (Iso.refl (tensorPower X a) ⊗ᵢ joinPowerIso X b t) ≪≫
    joinPowerIso X a (strandSum b t)

/-- Flatten three consecutive blocks by joining the first two first. -/
def leftTripleFlatten (X : C) (a b t : ℕ) :
    (tensorPower X a ⊗ tensorPower X b) ⊗ tensorPower X t ≅
      tensorPower X (strandSum (strandSum a b) t) :=
  (joinPowerIso X a b ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
    joinPowerIso X (strandSum a b) t

/-- Either grouping gives the same flattening, with the canonical associator. -/
theorem leftTripleFlatten_heq (X : C) (a b t : ℕ) :
    leftTripleFlatten X a b t ≍
      (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)) ≪≫
        rightTripleFlatten X a b t := by
  have ht := iso_trans_eqToIso_heq (leftTripleFlatten X a b t)
    (congrArg (tensorPower X) (strandSum_assoc a b t))
  have ha := joinPowerIso_assoc X a b t
  rw [← Iso.trans_assoc] at ha
  change leftTripleFlatten X a b t ≪≫ _ =
    (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)) ≪≫
      rightTripleFlatten X a b t at ha
  exact ht.symm.trans (heq_of_eq ha)

set_option backward.isDefEq.respectTransparency false in
/-- A crossing of the first two blocks can be evaluated after grouping them,
with the third block carried along unchanged. -/
theorem rightTripleCross_heq (X : C) (a b t : ℕ) [BraidedCategory C] :
    ((rightTripleFlatten X a b t).symm ≪≫
      (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      (α_ (tensorPower X b) (tensorPower X a) (tensorPower X t)) ≪≫
      rightTripleFlatten X b a t) ≍
    ((leftTripleFlatten X a b t).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      leftTripleFlatten X b a t) := by
  have ha := leftTripleFlatten_heq X a b t
  have hb := leftTripleFlatten_heq X b a t
  have hc : ((rightTripleFlatten X a b t).symm ≪≫
      (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      (α_ (tensorPower X b) (tensorPower X a) (tensorPower X t)) ≪≫
      rightTripleFlatten X b a t) =
    (((α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)) ≪≫
        rightTripleFlatten X a b t).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      ((α_ (tensorPower X b) (tensorPower X a) (tensorPower X t)) ≪≫
        rightTripleFlatten X b a t)) := by
    apply Iso.ext
    simp [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  apply HEq.trans (heq_of_eq hc)
  congr 2
  all_goals try exact ha.symm
  all_goals try exact hb.symm
  all_goals simp [strandSum_eq_add, Nat.add_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Grouped crossing is a flattened two-block crossing with an identity suffix. -/
theorem leftTripleCross_eq (X : C) (a b t : ℕ) [BraidedCategory C] :
    ((leftTripleFlatten X a b t).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      leftTripleFlatten X b a t) =
    ((joinPowerIso X (strandSum a b) t).symm ≪≫
      (((joinPowerIso X a b).symm ≪≫ β_ (tensorPower X a) (tensorPower X b) ≪≫
        joinPowerIso X b a) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      joinPowerIso X (strandSum b a) t) := by
  apply Iso.ext
  simp only [leftTripleFlatten, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, tensorHom_id,
    Category.assoc]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Flatten a tuple by first flattening its suffix and then its three blocks. -/
theorem heterogeneousPowerFlatten_head_two (X : C) (n : ℕ) (k : Fin (n+2) → ℕ) :
    heterogeneousPowerFlatten X (n+2) k =
      (Iso.refl (tensorPower X (k 0)) ⊗ᵢ
        (Iso.refl (tensorPower X (k 1)) ⊗ᵢ
          heterogeneousPowerFlatten X n (fun i => k i.succ.succ))) ≪≫
        rightTripleFlatten X (k 0) (k 1)
          (heterogeneousStrandCount n (fun i => k i.succ.succ)) := by
  apply Iso.ext
  simp only [heterogeneousPowerFlatten, heterogeneousStrandCount, rightTripleFlatten,
    Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom, whiskerLeft_comp, Category.assoc]
  congr 1

/-- The zeroth colored generator braids the first two colors and fixes the tail. -/
theorem coloredGenerator_zero (n : ℕ) [BraidedCategory C] (F : Fin (n+2) → C) :
    Cabling.coloredGenerator n 0 F ≍
      (α_ (F 0) (F 1) (Cabling.coloredTensor n (fun i => F i.succ.succ))).symm ≪≫
      ((β_ (F 0) (F 1)) ⊗ᵢ Iso.refl _) ≪≫
      (α_ (F 1) (F 0) (Cabling.coloredTensor n (fun i => F i.succ.succ))) := by
  cases n <;> rfl

/-- The zeroth swap fixes every color in its suffix. -/
theorem coloredSwap_zero_tail (n : ℕ) (i : Fin n) :
    Cabling.coloredSwap n 0 i.succ.succ = i.succ.succ := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => rfl

set_option backward.isDefEq.respectTransparency false in
/-- Flattening a spectator suffix commutes with crossing the first two factors. -/
theorem firstCross_suffix_cancel [BraidedCategory C] (A B U T P Q : C)
    (f : U ≅ T) (j : A ⊗ (B ⊗ T) ≅ P) (k : B ⊗ (A ⊗ T) ≅ Q) :
    (((Iso.refl A ⊗ᵢ (Iso.refl B ⊗ᵢ f)) ≪≫ j).symm ≪≫
      (α_ A B U).symm ≪≫ ((β_ A B) ⊗ᵢ Iso.refl U) ≪≫ (α_ B A U) ≪≫
      ((Iso.refl B ⊗ᵢ (Iso.refl A ⊗ᵢ f)) ≪≫ k)) =
    (j.symm ≪≫ (α_ A B T).symm ≪≫ ((β_ A B) ⊗ᵢ Iso.refl T) ≪≫
      (α_ B A T) ≪≫ k) := by
  have hn : ((α_ A B U).symm ≪≫ ((β_ A B) ⊗ᵢ Iso.refl U) ≪≫ (α_ B A U)) ≪≫
      (Iso.refl B ⊗ᵢ (Iso.refl A ⊗ᵢ f)) =
      (Iso.refl A ⊗ᵢ (Iso.refl B ⊗ᵢ f)) ≪≫
        ((α_ A B T).symm ≪≫ ((β_ A B) ⊗ᵢ Iso.refl T) ≪≫ (α_ B A T)) := by
    apply Iso.ext
    have h := Cabling.colored_first_map (𝟙 A) (𝟙 B) f.hom
    simpa only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom] using h
  calc
    _ = j.symm ≪≫ (Iso.refl A ⊗ᵢ (Iso.refl B ⊗ᵢ f)).symm ≪≫
        (((α_ A B U).symm ≪≫ ((β_ A B) ⊗ᵢ Iso.refl U) ≪≫ (α_ B A U)) ≪≫
          (Iso.refl B ⊗ᵢ (Iso.refl A ⊗ᵢ f))) ≪≫ k := by
      simp [Iso.trans_symm, Iso.trans_assoc]
    _ = j.symm ≪≫ (Iso.refl A ⊗ᵢ (Iso.refl B ⊗ᵢ f)).symm ≪≫
        ((Iso.refl A ⊗ᵢ (Iso.refl B ⊗ᵢ f)) ≪≫
          ((α_ A B T).symm ≪≫ ((β_ A B) ⊗ᵢ Iso.refl T) ≪≫ (α_ B A T))) ≪≫ k := by rw [hn]
    _ = _ := by simp [Iso.trans_assoc]


/-- The zeroth swap exchanges the first two colors. -/
theorem coloredSwap_zero_head (n : ℕ) :
    Cabling.coloredSwap n 0 0 = 1 ∧ Cabling.coloredSwap n 0 1 = 0 := by
  cases n <;> exact ⟨rfl, rfl⟩

/-- The colored flattening differs from recursive tuple flattening only by
source and target index transports. -/
theorem coloredTensorPowersFlatten_heq (X : C) [BraidedCategory C] [Abelian C]
    (n : ℕ) (k : Fin n → ℕ) :
    coloredTensorPowersFlatten X n k ≍ heterogeneousPowerFlatten X n k := by
  unfold coloredTensorPowersFlatten heterogeneousPowerFlattenSum
  simp only [powerIndexIso]
  exact (eqToIso_trans_heq _ _).trans (iso_trans_eqToIso_heq _ _)

