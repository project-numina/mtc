module
public import MTC.Braided.Cabling.Naturality

/-! Actual categorical braidings of independently colored tensor strands. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- A right-associated tensor product of independently chosen strands. -/
def coloredTensor : ∀ n : ℕ, (Fin n → C) → C
  | 0, _ => 𝟙_ C
  | n + 1, X => X 0 ⊗ coloredTensor n (fun i => X i.succ)

/-- Swap adjacent positions, recursively respecting the tensor association. -/
def coloredSwap : (n : ℕ) → Fin (n + 1) → Fin (n + 2) → Fin (n + 2)
  | 0, _ => Fin.cases 1 (Fin.cases 0 (fun i => nomatch i))
  | n + 1, i => Fin.cases
      (Fin.cases 1 (Fin.cases 0 (fun j => j.succ.succ)))
      (fun j => Fin.cases 0 (fun k => (coloredSwap n j k).succ)) i

/-- The recursive swap is exactly the adjacent permutation used by braid words. -/
theorem coloredSwap_eq_swap : ∀ (n : ℕ) (i : Fin (n + 1)),
    coloredSwap n i = Equiv.swap i.castSucc i.succ := by
  intro n
  induction n with
  | zero =>
    intro i
    fin_cases i
    funext j
    fin_cases j <;> decide
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · funext j
      refine Fin.cases ?_ (fun l => ?_) j
      · simp [coloredSwap, Equiv.swap_apply_def]
      · refine Fin.cases ?_ (fun t => ?_) l
        · change (0 : Fin (n + 3)) = 0
          rfl
        · simp [coloredSwap, Equiv.swap_apply_def]
          intro h
          have hh := congrArg Fin.val h
          simp at hh
    · funext j
      refine Fin.cases ?_ (fun l => ?_) j
      · simp only [coloredSwap, Equiv.swap_apply_def, Fin.cases_zero]
        split_ifs with h h <;> simp_all
      · simp [coloredSwap, ih, Equiv.swap_apply_def] <;> split_ifs <;> simp_all

/-- The actual adjacent braiding between differently colored strands. -/
def coloredGenerator : ∀ (n : ℕ) (i : Fin (n + 1)) (X : Fin (n + 2) → C),
    coloredTensor (n + 2) X ≅ coloredTensor (n + 2) (fun j => X (coloredSwap n i j))
  | 0, _, X =>
      (α_ (X 0) (X 1) (𝟙_ C)).symm ≪≫
        ((β_ (X 0) (X 1)) ⊗ᵢ Iso.refl (𝟙_ C)) ≪≫
        (α_ (X 1) (X 0) (𝟙_ C))
  | n + 1, i, X => Fin.cases
      ((α_ (X 0) (X 1) (coloredTensor (n + 1) (fun k => X k.succ.succ))).symm ≪≫
        ((β_ (X 0) (X 1)) ⊗ᵢ Iso.refl _) ≪≫
        (α_ (X 1) (X 0) (coloredTensor (n + 1) (fun k => X k.succ.succ))))
      (fun j => Iso.refl (X 0) ⊗ᵢ coloredGenerator n j (fun k => X k.succ)) i

/-- Tensor independent maps on each colored strand. -/
def coloredTensorMap : ∀ (n : ℕ) {X Y : Fin n → C},
    (∀ i, X i ⟶ Y i) → (coloredTensor n X ⟶ coloredTensor n Y)
  | 0, _, _, _ => 𝟙 _
  | n + 1, _, _, f => f 0 ⊗ₘ coloredTensorMap n (fun i => f i.succ)

/-- Naturality of a crossing of two different strands with a spectator tail. -/
theorem colored_first_map {X Y X' Y' A B : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : A ⟶ B) :
    ((α_ X Y A).symm ≪≫ ((β_ X Y) ⊗ᵢ Iso.refl A) ≪≫ α_ Y X A).hom ≫
        (g ⊗ₘ (f ⊗ₘ h)) =
      (f ⊗ₘ (g ⊗ₘ h)) ≫
        ((α_ X' Y' B).symm ≪≫ ((β_ X' Y') ⊗ᵢ Iso.refl B) ≪≫ α_ Y' X' B).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
  rw [← associator_naturality, associator_inv_naturality_assoc]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    braiding_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- A colored adjacent crossing is natural in the independent strand maps. -/
theorem coloredGenerator_natural : ∀ (n : ℕ) (i : Fin (n + 1))
    {X Y : Fin (n + 2) → C} (f : ∀ j, X j ⟶ Y j),
    (coloredGenerator n i X).hom ≫
      coloredTensorMap (n + 2) (fun j => f (coloredSwap n i j)) =
    coloredTensorMap (n + 2) f ≫ (coloredGenerator n i Y).hom := by
  intro n
  induction n with
  | zero =>
    intro i X Y f
    fin_cases i
    change ((α_ (X 0) (X 1) (𝟙_ C)).symm ≪≫ ((β_ (X 0) (X 1)) ⊗ᵢ Iso.refl _) ≪≫ α_ (X 1) (X 0) _).hom ≫
      (f 1 ⊗ₘ (f 0 ⊗ₘ 𝟙 _)) = (f 0 ⊗ₘ (f 1 ⊗ₘ 𝟙 _)) ≫
      ((α_ (Y 0) (Y 1) (𝟙_ C)).symm ≪≫ ((β_ (Y 0) (Y 1)) ⊗ᵢ Iso.refl _) ≪≫ α_ (Y 1) (Y 0) _).hom
    exact colored_first_map (f 0) (f 1) (𝟙 _)
  | succ n ih =>
    intro i X Y f
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((α_ (X 0) (X 1) _).symm ≪≫ ((β_ (X 0) (X 1)) ⊗ᵢ Iso.refl _) ≪≫ α_ (X 1) (X 0) _).hom ≫
        (f 1 ⊗ₘ (f 0 ⊗ₘ coloredTensorMap (n + 1) (fun k => f k.succ.succ))) =
        (f 0 ⊗ₘ (f 1 ⊗ₘ coloredTensorMap (n + 1) (fun k => f k.succ.succ))) ≫
        ((α_ (Y 0) (Y 1) _).symm ≪≫ ((β_ (Y 0) (Y 1)) ⊗ᵢ Iso.refl _) ≪≫ α_ (Y 1) (Y 0) _).hom
      exact colored_first_map (f 0) (f 1) _
    · change (𝟙 (X 0) ⊗ₘ (coloredGenerator n j (fun k => X k.succ)).hom) ≫
        (f 0 ⊗ₘ coloredTensorMap (n + 2) (fun k => f (coloredSwap n j k).succ)) =
        (f 0 ⊗ₘ coloredTensorMap (n + 2) (fun k => f k.succ)) ≫
        (𝟙 (Y 0) ⊗ₘ (coloredGenerator n j (fun k => Y k.succ)).hom)
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      rw [ih j (fun k => f k.succ)]

/-- The negative adjacent crossing of differently colored strands. -/
def coloredGeneratorInverse : ∀ (n : ℕ) (i : Fin (n + 1)) (X : Fin (n + 2) → C),
    coloredTensor (n + 2) X ≅ coloredTensor (n + 2) (fun j => X (coloredSwap n i j))
  | 0, _, X =>
      (α_ (X 0) (X 1) (𝟙_ C)).symm ≪≫
        ((β_ (X 1) (X 0)).symm ⊗ᵢ Iso.refl (𝟙_ C)) ≪≫
        (α_ (X 1) (X 0) (𝟙_ C))
  | n + 1, i, X => Fin.cases
      ((α_ (X 0) (X 1) (coloredTensor (n + 1) (fun k => X k.succ.succ))).symm ≪≫
        ((β_ (X 1) (X 0)).symm ⊗ᵢ Iso.refl _) ≪≫
        (α_ (X 1) (X 0) (coloredTensor (n + 1) (fun k => X k.succ.succ))))
      (fun j => Iso.refl (X 0) ⊗ᵢ coloredGeneratorInverse n j (fun k => X k.succ)) i

/-- Positive and negative actual colored crossings. -/
def coloredLetter (n : ℕ) (i : Fin (n + 1)) (positive : Bool) (X : Fin (n + 2) → C) :
    coloredTensor (n + 2) X ≅ coloredTensor (n + 2) (fun j => X (coloredSwap n i j)) :=
  if positive then coloredGenerator n i X else coloredGeneratorInverse n i X

/-- Naturality of a crossing of two different strands with a spectator tail. -/
theorem colored_first_inverse_map {X Y X' Y' A B : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : A ⟶ B) :
    ((α_ X Y A).symm ≪≫ ((β_ Y X).symm ⊗ᵢ Iso.refl A) ≪≫ α_ Y X A).hom ≫
        (g ⊗ₘ (f ⊗ₘ h)) =
      (f ⊗ₘ (g ⊗ₘ h)) ≫
        ((α_ X' Y' B).symm ≪≫ ((β_ Y' X').symm ⊗ᵢ Iso.refl B) ≪≫ α_ Y' X' B).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
  rw [← associator_naturality, associator_inv_naturality_assoc]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    braiding_inv_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- A colored adjacent crossing is natural in the independent strand maps. -/
theorem coloredGeneratorInverse_natural : ∀ (n : ℕ) (i : Fin (n + 1))
    {X Y : Fin (n + 2) → C} (f : ∀ j, X j ⟶ Y j),
    (coloredGeneratorInverse n i X).hom ≫
      coloredTensorMap (n + 2) (fun j => f (coloredSwap n i j)) =
    coloredTensorMap (n + 2) f ≫ (coloredGeneratorInverse n i Y).hom := by
  intro n
  induction n with
  | zero =>
    intro i X Y f
    fin_cases i
    change ((α_ (X 0) (X 1) (𝟙_ C)).symm ≪≫ ((β_ (X 1) (X 0)).symm ⊗ᵢ Iso.refl _) ≪≫ α_ (X 1) (X 0) _).hom ≫
      (f 1 ⊗ₘ (f 0 ⊗ₘ 𝟙 _)) = (f 0 ⊗ₘ (f 1 ⊗ₘ 𝟙 _)) ≫
      ((α_ (Y 0) (Y 1) (𝟙_ C)).symm ≪≫ ((β_ (Y 1) (Y 0)).symm ⊗ᵢ Iso.refl _) ≪≫ α_ (Y 1) (Y 0) _).hom
    exact colored_first_inverse_map (f 0) (f 1) (𝟙 _)
  | succ n ih =>
    intro i X Y f
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((α_ (X 0) (X 1) _).symm ≪≫ ((β_ (X 1) (X 0)).symm ⊗ᵢ Iso.refl _) ≪≫ α_ (X 1) (X 0) _).hom ≫
        (f 1 ⊗ₘ (f 0 ⊗ₘ coloredTensorMap (n + 1) (fun k => f k.succ.succ))) =
        (f 0 ⊗ₘ (f 1 ⊗ₘ coloredTensorMap (n + 1) (fun k => f k.succ.succ))) ≫
        ((α_ (Y 0) (Y 1) _).symm ≪≫ ((β_ (Y 1) (Y 0)).symm ⊗ᵢ Iso.refl _) ≪≫ α_ (Y 1) (Y 0) _).hom
      exact colored_first_inverse_map (f 0) (f 1) _
    · change (𝟙 (X 0) ⊗ₘ (coloredGeneratorInverse n j (fun k => X k.succ)).hom) ≫
        (f 0 ⊗ₘ coloredTensorMap (n + 2) (fun k => f (coloredSwap n j k).succ)) =
        (f 0 ⊗ₘ coloredTensorMap (n + 2) (fun k => f k.succ)) ≫
        (𝟙 (Y 0) ⊗ₘ (coloredGeneratorInverse n j (fun k => Y k.succ)).hom)
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      rw [ih j (fun k => f k.succ)]

/-- The target-strand permutation of a concrete signed adjacent word. -/
def coloredWordSwap (n : ℕ) : List (Fin (n + 1) × Bool) → Fin (n + 2) → Fin (n + 2)
  | [] => id
  | a :: w => fun j => coloredSwap n a.1 (coloredWordSwap n w j)

/-- Evaluate a concrete signed word as actual heterogeneous categorical crossings. -/
def coloredWordIso (n : ℕ) : ∀ (w : List (Fin (n + 1) × Bool)) (X : Fin (n + 2) → C),
    coloredTensor (n + 2) X ≅ coloredTensor (n + 2) (fun j => X (coloredWordSwap n w j))
  | [], X => Iso.refl _
  | a :: w, X => coloredLetter n a.1 a.2 X ≪≫
      coloredWordIso n w (fun j => X (coloredSwap n a.1 j))

/-- The colored-word endpoint is the actual strand permutation of the word. -/
theorem coloredWordSwap_eq_strandPermutation (n : ℕ)
    (w : List (Fin (n + 1) × Bool)) :
    coloredWordSwap n w = strandPermutation n (FreeGroup.mk w) := by
  induction w with
  | nil => funext j; simp [coloredWordSwap, strandPermutation]
  | cons a w ih =>
    funext j
    cases a with
    | mk i b =>
      cases b <;> simp [coloredWordSwap, coloredSwap_eq_swap, strandPermutation,
        FreeGroup.lift_mk, ih, Equiv.Perm.mul_apply]

/-- The colored tensor map preserves identities. -/
theorem coloredTensorMap_id : ∀ (n : ℕ) (X : Fin n → C),
    coloredTensorMap n (fun i => 𝟙 (X i)) = 𝟙 (coloredTensor n X)
  | 0, _ => rfl
  | n + 1, X => by
    change (𝟙 (X 0) ⊗ₘ coloredTensorMap n (fun i => 𝟙 (X i.succ))) = _
    rw [coloredTensorMap_id]
    simp [coloredTensor]

/-- The colored tensor map preserves independent componentwise composition. -/
theorem coloredTensorMap_comp : ∀ (n : ℕ) {X Y Z : Fin n → C}
    (f : ∀ i, X i ⟶ Y i) (g : ∀ i, Y i ⟶ Z i),
    coloredTensorMap n (fun i => f i ≫ g i) = coloredTensorMap n f ≫ coloredTensorMap n g
  | 0, _, _, _, _, _ => by simp [coloredTensorMap, coloredTensor]
  | n + 1, _, _, _, f, g => by
    change ((f 0 ≫ g 0) ⊗ₘ coloredTensorMap n (fun i => f i.succ ≫ g i.succ)) =
      (f 0 ⊗ₘ coloredTensorMap n (fun i => f i.succ)) ≫
        (g 0 ⊗ₘ coloredTensorMap n (fun i => g i.succ))
    rw [coloredTensorMap_comp, tensorHom_comp_tensorHom]

/-- Both signs of a colored crossing are natural in independent strand maps. -/
theorem coloredLetter_natural (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    {X Y : Fin (n + 2) → C} (f : ∀ j, X j ⟶ Y j) :
    (coloredLetter n i b X).hom ≫ coloredTensorMap (n + 2) (fun j => f (coloredSwap n i j)) =
      coloredTensorMap (n + 2) f ≫ (coloredLetter n i b Y).hom := by
  cases b
  · exact coloredGeneratorInverse_natural n i f
  · exact coloredGenerator_natural n i f

/-- A signed colored word is natural in independent maps on its strands. -/
theorem coloredWordIso_natural (n : ℕ) : ∀ (w : List (Fin (n + 1) × Bool))
    {X Y : Fin (n + 2) → C} (f : ∀ j, X j ⟶ Y j),
    (coloredWordIso n w X).hom ≫ coloredTensorMap (n + 2) (fun j => f (coloredWordSwap n w j)) =
      coloredTensorMap (n + 2) f ≫ (coloredWordIso n w Y).hom
  | [], _, _, f => by simp [coloredWordIso, coloredWordSwap]
  | a :: w, _, _, f => by
    simp only [coloredWordIso, coloredWordSwap, Iso.trans_hom, Category.assoc]
    rw [coloredWordIso_natural n w (fun j => f (coloredSwap n a.1 j))]
    rw [← Category.assoc, coloredLetter_natural]
    simp only [Category.assoc]

/-- The homogeneous colored tensor is canonically the existing tensor power. -/
def coloredConstantIso (X : C) : ∀ n : ℕ,
    coloredTensor n (fun _ => X) ≅ tensorPower X n
  | 0 => Iso.refl _
  | n + 1 => Iso.refl X ⊗ᵢ coloredConstantIso X n

set_option backward.isDefEq.respectTransparency false in
/-- On a homogeneous tuple the actual colored generator is the existing
categorical braid generator, transported along the constant-tuple isomorphism. -/
theorem coloredGenerator_constant : ∀ (n : ℕ) (i : Fin (n + 1)) (X : C),
    (coloredGenerator n i (fun _ => X)).hom ≫ (coloredConstantIso X (n + 2)).hom =
      (coloredConstantIso X (n + 2)).hom ≫ (braidGenerator X n i).asIso.hom := by
  intro n
  induction n with
  | zero =>
    intro i X
    fin_cases i
    change ((α_ X X (𝟙_ C)).symm ≪≫ ((β_ X X) ⊗ᵢ Iso.refl _) ≪≫ α_ X X _).hom ≫
      (𝟙 X ⊗ₘ (𝟙 X ⊗ₘ 𝟙 _)) = (𝟙 X ⊗ₘ (𝟙 X ⊗ₘ 𝟙 _)) ≫
      ((α_ X X (𝟙_ C)).symm ≪≫ ((β_ X X) ⊗ᵢ Iso.refl _) ≪≫ α_ X X _).hom
    exact braid_first_map (𝟙 X) (𝟙 _)
  | succ n ih =>
    intro i X
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((α_ X X _).symm ≪≫ ((β_ X X) ⊗ᵢ Iso.refl _) ≪≫ α_ X X _).hom ≫
        (𝟙 X ⊗ₘ (𝟙 X ⊗ₘ (coloredConstantIso X (n + 1)).hom)) =
        (𝟙 X ⊗ₘ (𝟙 X ⊗ₘ (coloredConstantIso X (n + 1)).hom)) ≫
        ((α_ X X _).symm ≪≫ ((β_ X X) ⊗ᵢ Iso.refl _) ≪≫ α_ X X _).hom
      exact braid_first_map (𝟙 X) _
    · change (𝟙 X ⊗ₘ (coloredGenerator n j (fun _ => X)).hom) ≫
        (𝟙 X ⊗ₘ (coloredConstantIso X (n + 2)).hom) =
        (𝟙 X ⊗ₘ (coloredConstantIso X (n + 2)).hom) ≫
        (𝟙 X ⊗ₘ (braidGenerator X n j).asIso.hom)
      simp only [tensorHom_comp_tensorHom, Category.id_comp, ih]

/-- The inverse homogeneous adjacent generator is the negative crossing. -/
theorem braidGenerator_first_inv (X : C) (n : ℕ) :
    (braidGenerator X n 0).asIso.inv =
      ((α_ X X (tensorPower X n)).symm ≪≫
        ((β_ X X).symm ⊗ᵢ Iso.refl (tensorPower X n)) ≪≫
        α_ X X (tensorPower X n)).hom := by
  cases n with
  | zero =>
    change ((α_ X X (tensorPower X 0)).symm ≪≫
      ((β_ X X) ⊗ᵢ Iso.refl _) ≪≫ α_ X X _).inv = _
    simp
  | succ n =>
    change ((α_ X X (tensorPower X (n + 1))).symm ≪≫
      ((β_ X X) ⊗ᵢ Iso.refl _) ≪≫ α_ X X _).inv = _
    simp

set_option backward.isDefEq.respectTransparency false in
/-- On a homogeneous tuple the actual colored generator is the existing
categorical braid generator, transported along the constant-tuple isomorphism. -/
theorem coloredGeneratorInverse_constant : ∀ (n : ℕ) (i : Fin (n + 1)) (X : C),
    (coloredGeneratorInverse n i (fun _ => X)).hom ≫ (coloredConstantIso X (n + 2)).hom =
      (coloredConstantIso X (n + 2)).hom ≫ (braidGenerator X n i).asIso.inv := by
  intro n
  induction n with
  | zero =>
    intro i X
    have : i = 0 := Fin.eq_zero i
    subst i
    rw [braidGenerator_first_inv]
    change ((α_ X X (𝟙_ C)).symm ≪≫ ((β_ X X).symm ⊗ᵢ Iso.refl _) ≪≫ α_ X X _).hom ≫
      (𝟙 X ⊗ₘ (𝟙 X ⊗ₘ 𝟙 _)) = (𝟙 X ⊗ₘ (𝟙 X ⊗ₘ 𝟙 _)) ≫
      ((α_ X X (𝟙_ C)).symm ≪≫ ((β_ X X).symm ⊗ᵢ Iso.refl _) ≪≫ α_ X X _).hom
    exact colored_first_inverse_map (𝟙 X) (𝟙 X) (𝟙 _)
  | succ n ih =>
    intro i X
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [braidGenerator_first_inv]
      change ((α_ X X _).symm ≪≫ ((β_ X X).symm ⊗ᵢ Iso.refl _) ≪≫ α_ X X _).hom ≫
        (𝟙 X ⊗ₘ (𝟙 X ⊗ₘ (coloredConstantIso X (n + 1)).hom)) =
        (𝟙 X ⊗ₘ (𝟙 X ⊗ₘ (coloredConstantIso X (n + 1)).hom)) ≫
        ((α_ X X _).symm ≪≫ ((β_ X X).symm ⊗ᵢ Iso.refl _) ≪≫ α_ X X _).hom
      exact colored_first_inverse_map (𝟙 X) (𝟙 X) _
    · change (𝟙 X ⊗ₘ (coloredGeneratorInverse n j (fun _ => X)).hom) ≫
        (𝟙 X ⊗ₘ (coloredConstantIso X (n + 2)).hom) =
        (𝟙 X ⊗ₘ (coloredConstantIso X (n + 2)).hom) ≫
        (𝟙 X ⊗ₘ (braidGenerator X n j).asIso.inv)
      simp only [tensorHom_comp_tensorHom, Category.id_comp, ih]

/-- Both signs of a homogeneous colored crossing are the corresponding
actual signed categorical braid generator. -/
theorem coloredLetter_constant (n : ℕ) (i : Fin (n + 1)) (b : Bool) (X : C) :
    (coloredLetter n i b (fun _ => X)).hom ≫ (coloredConstantIso X (n + 2)).hom =
      (coloredConstantIso X (n + 2)).hom ≫
        (if b then (braidGenerator X n i).asIso.hom else (braidGenerator X n i).asIso.inv) := by
  cases b
  · exact coloredGeneratorInverse_constant n i X
  · exact coloredGenerator_constant n i X

/-- On a homogeneous tuple, evaluating a signed colored word is the actual
categorical braid word action. -/
theorem coloredWordIso_constant (n : ℕ) (w : List (Fin (n + 1) × Bool)) (X : C) :
    (coloredWordIso n w (fun _ => X)).hom ≫ (coloredConstantIso X (n + 2)).hom =
      (coloredConstantIso X (n + 2)).hom ≫
        ((braidWordAction X n (FreeGroup.mk w.reverse)).val).asIso.hom := by
  induction w with
  | nil => simp [coloredWordIso, braidWordAction]
  | cons a w ih =>
    cases a with
    | mk i b =>
      simp only [coloredWordIso, Iso.trans_hom, Category.assoc]
      rw [ih, ← Category.assoc, coloredLetter_constant]
      cases b <;> simp [braidWordAction, FreeGroup.lift_mk, List.map_reverse, List.prod_reverse, Aut.mul_asIso, Aut.inv_asIso,
        Iso.trans_hom, Category.assoc]

end MTC.Braided.Cabling
end
