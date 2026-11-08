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

end MTC.Braided.Cabling
end
