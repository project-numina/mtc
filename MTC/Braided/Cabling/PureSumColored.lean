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

/-- The first adjacent swap exchanges zero and one. -/
theorem coloredSwap_first_eq (n : ℕ) :
    coloredSwap n 0 = Equiv.swap (0 : Fin (n + 2)) 1 := by
  funext j
  cases n with
  | zero =>
    fin_cases j <;> decide
  | succ n =>
    refine Fin.cases ?_ (fun l => ?_) j
    · simp [coloredSwap]
    · refine Fin.cases ?_ (fun t => ?_) l
      · rfl
      · simp [coloredSwap, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (Fin.succ_succ_ne_one _)]

/-- The recursive swap is exactly the adjacent permutation used by braid words. -/
theorem coloredSwap_eq_swap : ∀ (n : ℕ) (i : Fin (n + 1)),
    coloredSwap n i = Equiv.swap i.castSucc i.succ := by
  intro n
  induction n with
  | zero =>
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact coloredSwap_first_eq 0
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact coloredSwap_first_eq (n + 1)
    · funext j
      refine Fin.cases ?_ (fun l => ?_) j
      · simp only [coloredSwap, Fin.cases_succ, Fin.cases_zero, Fin.castSucc_succ,
          Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm]
      · simpa only [coloredSwap, Fin.cases_succ, ih, Fin.castSucc_succ] using
          ((Fin.succ_injective (n + 2)).map_swap k.castSucc k.succ l)

/-- Every adjacent colored swap is an involution. -/
theorem coloredSwap_involutive (n : ℕ) (i : Fin (n + 1)) :
    Function.Involutive (coloredSwap n i) := by
  rw [coloredSwap_eq_swap]
  intro j
  exact Equiv.swap_apply_self _ _ j

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
/-- Both signs of a colored crossing are natural in independent strand maps. -/
theorem coloredLetter_natural : ∀ (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    {X Y : Fin (n + 2) → C} (f : ∀ j, X j ⟶ Y j),
    (coloredLetter n i b X).hom ≫ coloredTensorMap (n + 2) (fun j => f (coloredSwap n i j)) =
      coloredTensorMap (n + 2) f ≫ (coloredLetter n i b Y).hom := by
  intro n
  induction n with
  | zero =>
    intro i b X Y f
    fin_cases i
    cases b
    · exact colored_first_inverse_map (f 0) (f 1) (𝟙 _)
    · exact colored_first_map (f 0) (f 1) (𝟙 _)
  | succ n ih =>
    intro i b X Y f
    refine Fin.cases ?_ (fun j => ?_) i
    · cases b
      · exact colored_first_inverse_map (f 0) (f 1) _
      · exact colored_first_map (f 0) (f 1) _
    · have hm : (𝟙 (X 0) ⊗ₘ (coloredLetter n j b (fun k => X k.succ)).hom) ≫
          (f 0 ⊗ₘ coloredTensorMap (n + 2) (fun k => f (coloredSwap n j k).succ)) =
          (f 0 ⊗ₘ coloredTensorMap (n + 2) (fun k => f k.succ)) ≫
          (𝟙 (Y 0) ⊗ₘ (coloredLetter n j b (fun k => Y k.succ)).hom) := by
        simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
        rw [ih j b (fun k => f k.succ)]
      cases b
      · exact hm
      · exact hm

set_option backward.isDefEq.respectTransparency false in
/-- A colored adjacent crossing is natural in the independent strand maps. -/
theorem coloredGenerator_natural : ∀ (n : ℕ) (i : Fin (n + 1))
    {X Y : Fin (n + 2) → C} (f : ∀ j, X j ⟶ Y j),
    (coloredGenerator n i X).hom ≫
      coloredTensorMap (n + 2) (fun j => f (coloredSwap n i j)) =
    coloredTensorMap (n + 2) f ≫ (coloredGenerator n i Y).hom :=
  fun n i {_X _Y} f => coloredLetter_natural n i true f

set_option backward.isDefEq.respectTransparency false in
/-- A colored adjacent crossing is natural in the independent strand maps. -/
theorem coloredGeneratorInverse_natural : ∀ (n : ℕ) (i : Fin (n + 1))
    {X Y : Fin (n + 2) → C} (f : ∀ j, X j ⟶ Y j),
    (coloredGeneratorInverse n i X).hom ≫
      coloredTensorMap (n + 2) (fun j => f (coloredSwap n i j)) =
    coloredTensorMap (n + 2) f ≫ (coloredGeneratorInverse n i Y).hom :=
  fun n i {_X _Y} f => coloredLetter_natural n i false f

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
    simp [coloredTensorMap, coloredTensor, coloredTensorMap_id n]

/-- The colored tensor map preserves independent componentwise composition. -/
theorem coloredTensorMap_comp : ∀ (n : ℕ) {X Y Z : Fin n → C}
    (f : ∀ i, X i ⟶ Y i) (g : ∀ i, Y i ⟶ Z i),
    coloredTensorMap n (fun i => f i ≫ g i) = coloredTensorMap n f ≫ coloredTensorMap n g
  | 0, _, _, _, _, _ => by simp [coloredTensorMap, coloredTensor]
  | n + 1, _, _, _, f, g => by
    simp only [coloredTensorMap, coloredTensorMap_comp]
    exact (tensorHom_comp_tensorHom _ _ _ _).symm

/-- A signed colored word is natural in independent maps on its strands. -/
theorem coloredWordIso_natural {n : ℕ} : ∀ (w : List (Fin (n + 1) × Bool))
    {X Y : Fin (n + 2) → C} (f : ∀ j, X j ⟶ Y j),
    (coloredWordIso n w X).hom ≫ coloredTensorMap (n + 2) (fun j => f (coloredWordSwap n w j)) =
      coloredTensorMap (n + 2) f ≫ (coloredWordIso n w Y).hom
  | [], _, _, f => by simp [coloredWordIso, coloredWordSwap]
  | a :: w, _, _, f => by
    simp only [coloredWordIso, coloredWordSwap, Iso.trans_hom, Category.assoc]
    rw [coloredWordIso_natural w (fun j => f (coloredSwap n a.1 j))]
    rw [← Category.assoc, coloredLetter_natural]
    simp only [Category.assoc]

/-- The homogeneous colored tensor is canonically the existing tensor power. -/
def coloredConstantIso (X : C) : ∀ n : ℕ,
    coloredTensor n (fun _ => X) ≅ tensorPower X n
  | 0 => Iso.refl _
  | n + 1 => Iso.refl X ⊗ᵢ coloredConstantIso X n

set_option backward.isDefEq.respectTransparency false in
/-- The inverse homogeneous adjacent generator is the negative crossing. -/
theorem braidGenerator_first_inv (X : C) (n : ℕ) :
    (braidGenerator X n 0).asIso.inv =
      ((α_ X X (tensorPower X n)).symm ≪≫
        ((β_ X X).symm ⊗ᵢ Iso.refl (tensorPower X n)) ≪≫
        α_ X X (tensorPower X n)).hom := by
  rw [braidGenerator_first]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Both signs of a homogeneous colored crossing are the corresponding
actual signed categorical braid generator. -/
theorem coloredLetter_constant : ∀ (n : ℕ) (i : Fin (n + 1)) (b : Bool) (X : C),
    (coloredLetter n i b (fun _ => X)).hom ≫ (coloredConstantIso X (n + 2)).hom =
      (coloredConstantIso X (n + 2)).hom ≫
        (if b then (braidGenerator X n i).asIso.hom else (braidGenerator X n i).asIso.inv) := by
  intro n
  induction n with
  | zero =>
    intro i b X
    have hi : i = 0 := Fin.eq_zero i
    subst i
    cases b
    · simp only [coloredLetter, Bool.false_eq_true, ↓reduceIte]
      rw [braidGenerator_first_inv]
      exact colored_first_inverse_map (𝟙 X) (𝟙 X) (𝟙 _)
    · exact braid_first_map (𝟙 X) (𝟙 _)
  | succ n ih =>
    intro i b X
    refine Fin.cases ?_ (fun j => ?_) i
    · cases b
      · simp only [coloredLetter, Bool.false_eq_true, ↓reduceIte]
        rw [braidGenerator_first_inv]
        exact colored_first_inverse_map (𝟙 X) (𝟙 X) _
      · exact braid_first_map (𝟙 X) _
    · have hm : (𝟙 X ⊗ₘ (coloredLetter n j b (fun _ => X)).hom) ≫
          (𝟙 X ⊗ₘ (coloredConstantIso X (n + 2)).hom) =
          (𝟙 X ⊗ₘ (coloredConstantIso X (n + 2)).hom) ≫
          (𝟙 X ⊗ₘ (if b then (braidGenerator X n j).asIso.hom else
            (braidGenerator X n j).asIso.inv)) := by
        simp only [tensorHom_comp_tensorHom, Category.id_comp]
        rw [ih j b X]
      cases b
      · exact hm
      · exact hm

set_option backward.isDefEq.respectTransparency false in
/-- On a homogeneous tuple the actual colored generator is the existing
categorical braid generator, transported along the constant-tuple isomorphism. -/
theorem coloredGenerator_constant : ∀ (n : ℕ) (i : Fin (n + 1)) (X : C),
    (coloredGenerator n i (fun _ => X)).hom ≫ (coloredConstantIso X (n + 2)).hom =
      (coloredConstantIso X (n + 2)).hom ≫ (braidGenerator X n i).asIso.hom :=
  fun n i X => coloredLetter_constant n i true X

set_option backward.isDefEq.respectTransparency false in
/-- On a homogeneous tuple the actual colored generator is the existing
categorical braid generator, transported along the constant-tuple isomorphism. -/
theorem coloredGeneratorInverse_constant : ∀ (n : ℕ) (i : Fin (n + 1)) (X : C),
    (coloredGeneratorInverse n i (fun _ => X)).hom ≫ (coloredConstantIso X (n + 2)).hom =
      (coloredConstantIso X (n + 2)).hom ≫ (braidGenerator X n i).asIso.inv :=
  fun n i X => coloredLetter_constant n i false X

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
      rw [ih, ← Category.assoc, coloredLetter_constant, braidWordAction_cons_reverse]
      simp only [Category.assoc]

/-- Reversing a signed word inverts its strand permutation. -/
theorem strandPermutation_reverse (n : ℕ) (w : List (Fin (n + 1) × Bool)) :
    strandPermutation n (FreeGroup.mk w.reverse) =
      (strandPermutation n (FreeGroup.mk w))⁻¹ := by
  rw [← map_inv, FreeGroup.inv_mk]
  simp [strandPermutation, FreeGroup.lift_mk, FreeGroup.invRev, List.map_reverse,
    List.map_map, Function.comp_def]

/-- Each actual braid word carries an arbitrary colored tensor block to the
block with the corresponding permuted strand colors. -/
theorem coloredWordIso_intertwines_uniform {n : ℕ}
    (w : List (Fin (n + 1) × Bool)) {X : Fin (n + 2) → C} {Y : C}
    (f : ∀ j, X j ⟶ Y) :
    (coloredWordIso n w X).hom ≫
      coloredTensorMap (n + 2) (fun j => f (coloredWordSwap n w j)) ≫
        (coloredConstantIso Y (n + 2)).hom =
    coloredTensorMap (n + 2) f ≫ (coloredConstantIso Y (n + 2)).hom ≫
      ((braidWordAction Y n (FreeGroup.mk w.reverse)).val).asIso.hom := by
  rw [← Category.assoc, coloredWordIso_natural]
  simp only [Category.assoc]
  rw [coloredWordIso_constant]

/-- Inclusion of a colored tensor block into the tensor power of a common object. -/
def coloredBlockInclusion (n : ℕ) (X : Fin n → C) (Y : C) (f : ∀ j, X j ⟶ Y) :
    coloredTensor n X ⟶ tensorPower Y n :=
  coloredTensorMap n f ≫ (coloredConstantIso Y n).hom

/-- Projection onto a colored tensor block. -/
def coloredBlockProjection (n : ℕ) (X : Fin n → C) (Y : C) (g : ∀ j, Y ⟶ X j) :
    tensorPower Y n ⟶ coloredTensor n X :=
  (coloredConstantIso Y n).inv ≫ coloredTensorMap n g

/-- Componentwise retracts induce a retract of tensor blocks. -/
theorem coloredBlockInclusion_projection {n : ℕ} {X : Fin n → C} {Y : C}
    (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j) (h : ∀ j, f j ≫ g j = 𝟙 (X j)) :
    coloredBlockInclusion n X Y f ≫ coloredBlockProjection n X Y g = 𝟙 _ := by
  simp only [coloredBlockInclusion, coloredBlockProjection, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← coloredTensorMap_comp]
  simpa only [h] using coloredTensorMap_id n X

/-- Transport along an identity strand permutation commutes with the
componentwise colored tensor map. -/
theorem coloredTensorMap_identityPermutation (n : ℕ) (σ : Fin n → Fin n)
    (hσ : σ = id) {X : Fin n → C} {Y : C} (f : ∀ j, X j ⟶ Y) :
    coloredTensorMap n (fun j => f (σ j)) =
      eqToHom (congrArg (coloredTensor n) (congrArg (fun t => fun j => X (t j)) hσ)) ≫
        coloredTensorMap n f := by
  cases hσ
  simp

/-- A pure word, read in the categorical composition order, fixes all positions. -/
theorem coloredWordSwap_reverse_pure (n : ℕ) (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1) : coloredWordSwap n w.reverse = id := by
  rw [coloredWordSwap_eq_strandPermutation, strandPermutation_reverse, hw]
  rfl

/-- The actual endomorphism of a colored block induced by a pure word. -/
def coloredPureWordHom (n : ℕ) (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1) (X : Fin (n + 2) → C) :
    coloredTensor (n + 2) X ⟶ coloredTensor (n + 2) X :=
  (coloredWordIso n w.reverse X).hom ≫
    eqToHom (congrArg (coloredTensor (n + 2))
      (congrArg (fun t => fun j => X (t j)) (coloredWordSwap_reverse_pure n w hw)))

/-- The colored pure-word endomorphism is an actual automorphism. -/
def coloredPureWordAut (n : ℕ) (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1) (X : Fin (n + 2) → C) :
    Aut (coloredTensor (n + 2) X) :=
  Aut.of (coloredWordIso n w.reverse X ≪≫
    eqToIso (congrArg (coloredTensor (n + 2))
      (congrArg (fun t => fun j => X (t j)) (coloredWordSwap_reverse_pure n w hw))))

@[simp] theorem coloredPureWordAut_hom (n : ℕ) (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1) (X : Fin (n + 2) → C) :
    (coloredPureWordAut n w hw X).asIso.hom = coloredPureWordHom n w hw X := rfl

/-- The pure colored endomorphism intertwines with its ambient braid action. -/
theorem coloredPureWordHom_intertwines {n : ℕ}
    (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1)
    {X : Fin (n + 2) → C} {Y : C} (f : ∀ j, X j ⟶ Y) :
    coloredPureWordHom n w hw X ≫ coloredBlockInclusion (n + 2) X Y f =
      coloredBlockInclusion (n + 2) X Y f ≫
        ((braidWordAction Y n (FreeGroup.mk w)).val).asIso.hom := by
  have hn := coloredWordIso_intertwines_uniform w.reverse f
  simp only [List.reverse_reverse] at hn
  rw [coloredTensorMap_identityPermutation (n + 2) _ (coloredWordSwap_reverse_pure n w hw) f] at hn
  simpa only [coloredPureWordHom, coloredBlockInclusion, Category.assoc] using hn

/-- The diagonal of the actual pure braid action is the colored pure-word
endomorphism, without any finiteness hypothesis. -/
theorem pureWord_coloredBlock_diagonal (n : ℕ)
    (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1)
    {X : Fin (n + 2) → C} {Y : C} (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (h : ∀ j, f j ≫ g j = 𝟙 (X j)) :
    coloredBlockInclusion (n + 2) X Y f ≫
      ((braidWordAction Y n (FreeGroup.mk w)).val).asIso.hom ≫
        coloredBlockProjection (n + 2) X Y g = coloredPureWordHom n w hw X := by
  simp only [← Category.assoc, ← coloredPureWordHom_intertwines w hw f]
  simp only [Category.assoc, coloredBlockInclusion_projection f g h,
    Category.comp_id]

/-- A pure word preserves every colored retract block of a tensor power. -/
theorem pureWord_preserves_coloredBlock (n : ℕ)
    (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1)
    {X : Fin (n + 2) → C} {Y : C} (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (h : ∀ j, f j ≫ g j = 𝟙 (X j)) :
    let ι := coloredBlockInclusion (n + 2) X Y f
    let π := coloredBlockProjection (n + 2) X Y g
    let b := ((braidWordAction Y n (FreeGroup.mk w)).val).asIso.hom
    ι ≫ b = (ι ≫ b ≫ π) ≫ ι := by
  dsimp only
  rw [pureWord_coloredBlock_diagonal n w hw f g h]
  exact (coloredPureWordHom_intertwines w hw f).symm

end MTC.Braided.Cabling
end
