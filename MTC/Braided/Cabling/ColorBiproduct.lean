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

end MTC.Braided.Cabling
end
