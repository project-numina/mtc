module
public import MTC.Braided.Cabling.ClosureColoredFlatten
public import MTC.Braided.Cabling.PureSumColored

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- The heterogeneous tuple is the actual colored tensor of these powers. -/
theorem coloredTensor_powers_eq (X : C) : ∀ (n : ℕ) (k : Fin n → ℕ),
    Cabling.coloredTensor n (fun i => tensorPower X (k i)) = heterogeneousPowerTensor X n k
  | 0, _ => rfl
  | n+1, k => by
    simp only [Cabling.coloredTensor, heterogeneousPowerTensor]
    rw [coloredTensor_powers_eq X n (fun i => k i.succ)]

/-- Canonical flattening for the actual colored tensor of heterogeneous powers. -/
def coloredTensorPowersFlatten (X : C) (n : ℕ) (k : Fin n → ℕ) :
    Cabling.coloredTensor n (fun i => tensorPower X (k i)) ≅
      tensorPower X (∑ i, k i) :=
  eqToIso (coloredTensor_powers_eq X n k) ≪≫ heterogeneousPowerFlattenSum X n k

set_option backward.isDefEq.respectTransparency false in
/-- Flattening one colored block is its right unitor. -/
theorem heterogeneousPowerFlatten_one_heq (X : C) (k : Fin 1 → ℕ) :
    heterogeneousPowerFlatten X 1 k ≍ ρ_ (tensorPower X (k 0)) := by
  have hj := joinPowerIso_heq X (k 0) 0
  rw [tensorPowerTensorIso_zero] at hj
  have hid : (Iso.refl (tensorPower X (k 0)) ⊗ᵢ Iso.refl (𝟙_ C)) = Iso.refl _ := by
    apply Iso.ext
    simp
  simp only [heterogeneousPowerFlatten, heterogeneousStrandCount, heterogeneousPowerTensor]
  rw [hid, Iso.refl_trans]
  exact hj

set_option backward.isDefEq.respectTransparency false in
/-- Flattening two colored blocks removes the trailing unit and joins the blocks. -/
theorem heterogeneousPowerFlatten_two_heq (X : C) (k : Fin 2 → ℕ) :
    heterogeneousPowerFlatten X 2 k ≍
      (Iso.refl (tensorPower X (k 0)) ⊗ᵢ ρ_ (tensorPower X (k 1))) ≪≫
        joinPowerIso X (k 0) (k 1) := by
  have h := heterogeneousPowerFlatten_one_heq X (fun i : Fin 1 => k i.succ)
  simp only [heterogeneousPowerFlatten, heterogeneousStrandCount]
  congr 2
  all_goals try simp [strandSum_eq_add]

set_option backward.isDefEq.respectTransparency false in
/-- A two-color crossing, under tuple flattening, is the crossing of its two
underlying blocks under canonical joins. -/
theorem coloredGenerator_two_flatten_heq (X : C) (k : Fin 2 → ℕ) :
    ((heterogeneousPowerFlatten X 2 k).symm ≪≫
      Cabling.coloredGenerator 0 0 (fun i => tensorPower X (k i)) ≪≫
      heterogeneousPowerFlatten X 2 (fun i => k (Cabling.coloredSwap 0 0 i))) ≍
    ((joinPowerIso X (k 0) (k 1)).symm ≪≫
      β_ (tensorPower X (k 0)) (tensorPower X (k 1)) ≪≫
      joinPowerIso X (k 1) (k 0)) := by
  have hs := heterogeneousPowerFlatten_two_heq X k
  have ht := heterogeneousPowerFlatten_two_heq X (fun i => k (Cabling.coloredSwap 0 0 i))
  simp only [Cabling.coloredSwap, Fin.cases_zero, Fin.cases_succ] at ht
  have hg : Cabling.coloredGenerator 0 0 (fun i => tensorPower X (k i)) =
      (α_ (tensorPower X (k 0)) (tensorPower X (k 1)) (𝟙_ C)).symm ≪≫
        ((β_ (tensorPower X (k 0)) (tensorPower X (k 1))) ⊗ᵢ Iso.refl _) ≪≫
          α_ (tensorPower X (k 1)) (tensorPower X (k 0)) (𝟙_ C) := rfl
  rw [hg]
  have hm : ((heterogeneousPowerFlatten X 2 k).symm ≪≫
      ((α_ (tensorPower X (k 0)) (tensorPower X (k 1)) (𝟙_ C)).symm ≪≫
        ((β_ (tensorPower X (k 0)) (tensorPower X (k 1))) ⊗ᵢ Iso.refl _) ≪≫
          α_ (tensorPower X (k 1)) (tensorPower X (k 0)) (𝟙_ C)) ≪≫
      heterogeneousPowerFlatten X 2 (fun i => k (Cabling.coloredSwap 0 0 i))) ≍
    (((Iso.refl (tensorPower X (k 0)) ⊗ᵢ ρ_ (tensorPower X (k 1))) ≪≫
        joinPowerIso X (k 0) (k 1)).symm ≪≫
      ((α_ (tensorPower X (k 0)) (tensorPower X (k 1)) (𝟙_ C)).symm ≪≫
        ((β_ (tensorPower X (k 0)) (tensorPower X (k 1))) ⊗ᵢ Iso.refl _) ≪≫
          α_ (tensorPower X (k 1)) (tensorPower X (k 0)) (𝟙_ C)) ≪≫
      ((Iso.refl (tensorPower X (k 1)) ⊗ᵢ ρ_ (tensorPower X (k 0))) ≪≫
        joinPowerIso X (k 1) (k 0))) := by
    congr 2
    all_goals try exact hs
    all_goals try exact ht
    all_goals simp [heterogeneousStrandCount_eq_sum, Fin.sum_univ_succ, Cabling.coloredSwap, strandSum_eq_add]
  apply hm.trans
  apply heq_of_eq
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv,
    Iso.refl_hom, Iso.refl_inv, id_tensorHom, Category.assoc]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The crossing between two positive-width canonical joins is the explicit
rectangular braid word, up to index transport. -/
theorem joinCross_word_heq (X : C) [BraidedCategory C] [Abelian C] (r s : ℕ) :
    ((joinPowerIso X (r+1) (s+1)).symm ≪≫
      β_ (tensorPower X (r+1)) (tensorPower X (s+1)) ≪≫
      joinPowerIso X (s+1) (r+1)) ≍
      ((braidWordAction X (s+r) (blockSweepWord s r)).val).asIso := by
  have h1 : joinPowerNormalized X s r ≍ joinPowerIso X (r+1) (s+1) :=
    iso_trans_eqToIso_heq _ _
  have h2 : joinPowerNormalized X r s ≍ joinPowerIso X (s+1) (r+1) :=
    iso_trans_eqToIso_heq _ _
  have hw := congrArg Aut.asIso (heterogeneousBlockCross_word X s r)
  apply HEq.trans _ (heq_of_eq hw)
  dsimp only [Aut.of]
  rw [← Iso.trans_assoc, ← Iso.trans_assoc, ← Iso.trans_assoc]
  simp only [powerIndexIso]
  apply HEq.trans _ (iso_trans_eqToIso_heq _ _).symm
  congr 2
  all_goals try exact h2.symm
  all_goals try simp [strandSum_eq_add]
  all_goals try omega
  all_goals try (congr 1; try exact h1.symm; try (apply congrArg (tensorPower X); omega))
  all_goals try exact h1.symm
  all_goals try (apply congrArg (tensorPower X); simp only [strandSum_eq_add]; omega)
  all_goals omega

set_option backward.isDefEq.respectTransparency false in
/-- Two positive colored blocks act by the explicit rectangular braid word. -/
theorem coloredGenerator_two_word_heq (X : C) (k : Fin 2 → ℕ) (r s : ℕ)
    (h0 : k 0 = r+1) (h1 : k 1 = s+1) :
    ((heterogeneousPowerFlatten X 2 k).symm ≪≫
      Cabling.coloredGenerator 0 0 (fun i => tensorPower X (k i)) ≪≫
      heterogeneousPowerFlatten X 2 (fun i => k (Cabling.coloredSwap 0 0 i))) ≍
      ((braidWordAction X (s+r) (blockSweepWord s r)).val).asIso := by
  have hc := coloredGenerator_two_flatten_heq X k
  rw [h0, h1] at hc
  exact hc.trans (joinCross_word_heq X r s)


/-- If the first colored block is empty, the flattened crossing is identity. -/
theorem coloredGenerator_two_zero_left_heq (X : C) (k : Fin 2 → ℕ) (h0 : k 0 = 0) :
    ((heterogeneousPowerFlatten X 2 k).symm ≪≫
      Cabling.coloredGenerator 0 0 (fun i => tensorPower X (k i)) ≪≫
      heterogeneousPowerFlatten X 2 (fun i => k (Cabling.coloredSwap 0 0 i))) ≍
      Iso.refl (tensorPower X (k 1)) := by
  have h := coloredGenerator_two_flatten_heq X k
  rw [h0] at h
  exact h.trans (heterogeneousBlockCross_zero_left X (k 1))

/-- If the second colored block is empty, the flattened crossing is identity. -/
theorem coloredGenerator_two_zero_right_heq (X : C) (k : Fin 2 → ℕ) (h1 : k 1 = 0) :
    ((heterogeneousPowerFlatten X 2 k).symm ≪≫
      Cabling.coloredGenerator 0 0 (fun i => tensorPower X (k i)) ≪≫
      heterogeneousPowerFlatten X 2 (fun i => k (Cabling.coloredSwap 0 0 i))) ≍
      Iso.refl (tensorPower X (k 0)) := by
  have h := coloredGenerator_two_flatten_heq X k
  rw [h1] at h
  exact h.trans (heterogeneousBlockCross_zero_right X (k 0))
