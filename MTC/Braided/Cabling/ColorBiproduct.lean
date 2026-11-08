module
public import MTC.Braided.Cabling.PureSumColored
public import MTC.Braided.Cabling.Generated

/-! # Colored tensor components of tensor powers of finite biproducts -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Braided.Cabling
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [BraidedCategory C]
variable {I : Type} [Fintype I] [DecidableEq I] (V : I → C)

/-- The actual inclusion of a colored tensor component. -/
def colorInclusion : ∀ n : ℕ, (f : Fin n → I) →
    coloredTensor n (fun j => V (f j)) ⟶ tensorPower (⨁ V) n
  | 0, _ => 𝟙 _
  | n + 1, f => biproduct.ι V (f 0) ⊗ₘ colorInclusion n (fun j => f j.succ)

/-- The actual projection onto a colored tensor component. -/
def colorProjection : ∀ n : ℕ, (f : Fin n → I) →
    tensorPower (⨁ V) n ⟶ coloredTensor n (fun j => V (f j))
  | 0, _ => 𝟙 _
  | n + 1, f => biproduct.π V (f 0) ⊗ₘ colorProjection n (fun j => f j.succ)

/-- Each colored inclusion and its matching projection compose to identity. -/
@[simp] theorem colorInclusion_projection_self : ∀ n (f : Fin n → I),
    colorInclusion V n f ≫ colorProjection V n f = 𝟙 _
  | 0, _ => by simp [colorInclusion, colorProjection, coloredTensor, tensorPower]
  | n + 1, f => by
    rw [colorInclusion, colorProjection, tensorHom_comp_tensorHom, biproduct.ι_π_self,
      colorInclusion_projection_self n (fun j => f j.succ)]
    simp [coloredTensor]

/-- Distinct colorings give orthogonal inclusion/projection components. -/
theorem colorInclusion_projection_ne : ∀ n (f g : Fin n → I), f ≠ g →
    colorInclusion V n f ≫ colorProjection V n g = 0
  | 0, f, g, h => by
    exfalso
    apply h
    funext i
    exact Fin.elim0 i
  | n + 1, f, g, h => by
    rw [colorInclusion, colorProjection, tensorHom_comp_tensorHom]
    by_cases hhead : f 0 = g 0
    · have htail : (fun j : Fin n => f j.succ) ≠ (fun j : Fin n => g j.succ) := by
        intro ht
        apply h
        funext j
        exact Fin.cases hhead (fun k => congrFun ht k) j
      rw [colorInclusion_projection_ne n _ _ htail]
      simp
    · rw [biproduct.ι_π_ne V hhead]
      simp

/-- The colored components resolve the identity on every tensor power. -/
theorem colorProjection_inclusion_total : ∀ n,
    (∑ f : Fin n → I, colorProjection V n f ≫ colorInclusion V n f) =
      𝟙 (tensorPower (⨁ V) n)
  | 0 => by
    classical
    simp [colorProjection, colorInclusion, tensorPower]
  | n + 1 => by
    classical
    change (∑ f : Fin (n + 1) → I, colorProjection V (n + 1) f ≫ colorInclusion V (n + 1) f) =
      𝟙 ((⨁ V) ⊗ tensorPower (⨁ V) n)
    let e : I × (Fin n → I) ≃ (Fin (n + 1) → I) := Fin.consEquiv (fun _ => I)
    have hs : (∑ f : Fin (n + 1) → I, colorProjection V (n + 1) f ≫ colorInclusion V (n + 1) f) =
        ∑ a : I, ∑ f : Fin n → I,
          (biproduct.π V a ≫ biproduct.ι V a) ⊗ₘ
            (colorProjection V n f ≫ colorInclusion V n f) := by
      rw [← e.sum_comp, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro f hf
      simp only [e, Fin.consEquiv_apply, colorProjection, colorInclusion, tensorHom_comp_tensorHom]
      change (biproduct.π V (Fin.cons (α := fun _ : Fin (n + 1) => I) a f 0) ≫ biproduct.ι V (Fin.cons (α := fun _ : Fin (n + 1) => I) a f 0)) ⊗ₘ
        (colorProjection V n (fun j : Fin n => Fin.cons (α := fun _ : Fin (n + 1) => I) a f j.succ) ≫
          colorInclusion V n (fun j : Fin n => Fin.cons (α := fun _ : Fin (n + 1) => I) a f j.succ)) = _
      have ht : (fun j : Fin n => Fin.cons (α := fun _ : Fin (n + 1) => I) a f j.succ) = f := by
        funext j
        exact Fin.cons_succ (α := fun _ : Fin (n + 1) => I) a f j
      have htcomp := congrArg (fun g : Fin n → I =>
        colorProjection V n g ≫ colorInclusion V n g) ht
      rw [Fin.cons_zero, htcomp]
    rw [hs]
    simp_rw [← tensor_sum, colorProjection_inclusion_total n]
    rw [← sum_tensor, biproduct.total]
    simp

/-- Tensor powers of a finite biproduct decompose into the actual colored
tensor products of its summands. -/
def coloredBiproductIso (n : ℕ) : tensorPower (⨁ V) n ≅
    ⨁ (fun f : Fin n → I => coloredTensor n (fun j => V (f j))) where
  hom := biproduct.lift (colorProjection V n)
  inv := biproduct.desc (colorInclusion V n)
  hom_inv_id := by rw [biproduct.lift_desc, colorProjection_inclusion_total]
  inv_hom_id := by
    classical
    apply biproduct.hom_ext'
    intro f
    apply biproduct.hom_ext
    intro g
    simp only [Category.assoc, biproduct.ι_desc_assoc, biproduct.lift_π,
      Category.comp_id]
    by_cases h : f = g
    · subst g
      simp
    · rw [colorInclusion_projection_ne V n f g h]
      simp [biproduct.ι_π_ne _ h]

/-- The decomposition's component projections are the recursive maps. -/
@[simp] theorem coloredBiproductIso_hom_π (n : ℕ) (f : Fin n → I) :
    (coloredBiproductIso V n).hom ≫
      biproduct.π (fun f : Fin n → I => coloredTensor n (fun j => V (f j))) f =
        colorProjection V n f := by
  simp [coloredBiproductIso]

/-- The decomposition's component inclusions are the recursive maps. -/
@[simp] theorem coloredBiproductIso_ι_inv (n : ℕ) (f : Fin n → I) :
    biproduct.ι (fun f : Fin n → I => coloredTensor n (fun j => V (f j))) f ≫
      (coloredBiproductIso V n).inv = colorInclusion V n f := by
  simp [coloredBiproductIso]

/-- Each recursive inclusion is the independent-strand tensor map followed
by the canonical homogeneous tensor-power comparison. -/
theorem colorInclusion_eq_coloredTensorMap : ∀ n (f : Fin n → I),
    colorInclusion V n f = coloredTensorMap n (fun j => biproduct.ι V (f j)) ≫
      (coloredConstantIso (⨁ V) n).hom
  | 0, _ => by simp [colorInclusion, coloredTensorMap, coloredConstantIso]
  | n + 1, f => by
    rw [colorInclusion, coloredTensorMap, coloredConstantIso]
    simp only [tensorIso_hom, Iso.refl_hom, tensorHom_comp_tensorHom, Category.comp_id]
    rw [← colorInclusion_eq_coloredTensorMap n (fun j => f j.succ)]

/-- Each recursive projection is the homogeneous comparison followed by the
independent-strand tensor map of biproduct projections. -/
theorem colorProjection_eq_coloredTensorMap : ∀ n (f : Fin n → I),
    colorProjection V n f = (coloredConstantIso (⨁ V) n).inv ≫
      coloredTensorMap n (fun j => biproduct.π V (f j))
  | 0, _ => by simp [colorProjection, coloredTensorMap, coloredConstantIso, coloredTensor, tensorPower]
  | n + 1, f => by
    rw [colorProjection, coloredTensorMap, coloredConstantIso]
    simp only [tensorIso_inv, Iso.refl_inv, tensorHom_comp_tensorHom, Category.id_comp]
    rw [← colorProjection_eq_coloredTensorMap n (fun j => f j.succ)]

/-- Every actual colored signed word intertwines the corresponding
component inclusion with the actual braid action on the finite sum. -/
theorem coloredWordIso_intertwines_colorInclusion (n : ℕ)
    (w : List (Fin (n + 1) × Bool)) (f : Fin (n + 2) → I) :
    (coloredWordIso n w (fun j => V (f j))).hom ≫
      colorInclusion V (n + 2) (fun j => f (coloredWordSwap n w j)) =
    colorInclusion V (n + 2) f ≫
      ((braidWordAction (⨁ V) n (FreeGroup.mk w.reverse)).val).asIso.hom := by
  simp only [colorInclusion_eq_coloredTensorMap, Category.assoc]
  exact coloredWordIso_intertwines_uniform n w (fun j => V (f j)) (⨁ V)
    (fun j => biproduct.ι V (f j))

/-- Every actual braid word intertwines the colored projections in the
opposite direction. -/
theorem braidWordAction_intertwines_colorProjection (n : ℕ)
    (w : List (Fin (n + 1) × Bool)) (f : Fin (n + 2) → I) :
    ((braidWordAction (⨁ V) n (FreeGroup.mk w.reverse)).val).asIso.hom ≫
      colorProjection V (n + 2) (fun j => f (coloredWordSwap n w j)) =
    colorProjection V (n + 2) f ≫ (coloredWordIso n w (fun j => V (f j))).hom := by
  let c := coloredConstantIso (⨁ V) (n + 2)
  have hc := coloredWordIso_constant n w (⨁ V)
  have hn := coloredWordIso_natural n w (X := fun _ => ⨁ V) (Y := fun j => V (f j))
    (fun j => biproduct.π V (f j))
  rw [colorProjection_eq_coloredTensorMap, colorProjection_eq_coloredTensorMap]
  apply (cancel_epi c.hom).1
  change (coloredWordIso n w (fun _ => ⨁ V)).hom ≫ c.hom =
    c.hom ≫ ((braidWordAction (⨁ V) n (FreeGroup.mk w.reverse)).val).asIso.hom at hc
  change _ = _
  simp only [← Category.assoc]
  rw [← hc]
  simp only [c, Category.assoc, Iso.hom_inv_id_assoc]
  exact hn

/-- The component inclusion agrees with the independently constructed
colored-block inclusion for the actual biproduct injections. -/
theorem colorInclusion_eq_coloredBlockInclusion (n : ℕ) (f : Fin n → I) :
    colorInclusion V n f = coloredBlockInclusion n (fun j => V (f j)) (⨁ V)
      (fun j => biproduct.ι V (f j)) :=
  colorInclusion_eq_coloredTensorMap V n f

/-- The component projection agrees with the independently constructed
colored-block projection for the actual biproduct projections. -/
theorem colorProjection_eq_coloredBlockProjection (n : ℕ) (f : Fin n → I) :
    colorProjection V n f = coloredBlockProjection n (fun j => V (f j)) (⨁ V)
      (fun j => biproduct.π V (f j)) :=
  colorProjection_eq_coloredTensorMap V n f

/-- The colored retract blocks associated to the biproduct summands resolve
the identity on the whole tensor power. -/
theorem coloredBlockProjection_inclusion_total (n : ℕ) :
    (∑ f : Fin n → I,
      coloredBlockProjection n (fun j => V (f j)) (⨁ V) (fun j => biproduct.π V (f j)) ≫
      coloredBlockInclusion n (fun j => V (f j)) (⨁ V) (fun j => biproduct.ι V (f j))) =
      𝟙 (tensorPower (⨁ V) n) := by
  simp only [← colorProjection_eq_coloredBlockProjection,
    ← colorInclusion_eq_coloredBlockInclusion]
  exact colorProjection_inclusion_total V n

end MTC.Braided.Cabling
end
