module
public import PropertyF.Ground.Cabling.ExprStructure
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

set_option backward.isDefEq.respectTransparency false in
/-- Braiding any tensor expressions in X is a normalized cabled braid. -/
theorem PowerExpr.isCable_braiding (X : C) (a b : PowerExpr) :
    IsCable X (.tensor a b) (.tensor b a) (β_ (a.eval X) (b.eval X)).hom := by
  induction a generalizing b with
  | unit =>
    have h := isCable_comp X (isCable_leftUnit X b)
      (isCable_inv X (a := .tensor b .unit) (b := b) (ρ_ (b.eval X)) (isCable_rightUnit X b))
    simpa [eval, braiding_tensorUnit_left] using h
  | atom =>
    induction b with
    | unit =>
      have h := isCable_comp X (isCable_rightUnit X .atom)
        (isCable_inv X (a := .tensor .unit .atom) (b := .atom) (λ_ X) (isCable_leftUnit X .atom))
      simpa [eval, braiding_tensorUnit_right] using h
    | atom => exact isCable_atom_braid X
    | tensor p q ihp ihq =>
      have h₁ := isCable_inv X (a := .tensor (.tensor .atom p) q) (b := .tensor .atom (.tensor p q)) (α_ X (p.eval X) (q.eval X))
        (isCable_assoc X .atom p q)
      have h₂ := isCable_tensor X ihp (isCable_id X q)
      have h₃ := isCable_assoc X p .atom q
      have h₄ := isCable_tensor X (isCable_id X p) ihq
      have h₅ := isCable_inv X (a := .tensor (.tensor p q) .atom) (b := .tensor p (.tensor q .atom)) (α_ (p.eval X) (q.eval X) X)
        (isCable_assoc X p q .atom)
      have h := isCable_comp X (isCable_comp X (isCable_comp X (isCable_comp X h₁ h₂) h₃) h₄) h₅
      simpa [eval, braiding_tensor_right_hom, Category.assoc, tensorHom_id, id_tensorHom] using h
  | tensor p q ihp ihq =>
    have h₁ := isCable_assoc X p q b
    have h₂ := isCable_tensor X (isCable_id X p) (ihq b)
    have h₃ := isCable_inv X (a := .tensor (.tensor p b) q) (b := .tensor p (.tensor b q)) (α_ (p.eval X) (b.eval X) (q.eval X))
      (isCable_assoc X p b q)
    have h₄ := isCable_tensor X (ihp b) (isCable_id X q)
    have h₅ := isCable_assoc X b p q
    have h := isCable_comp X (isCable_comp X (isCable_comp X (isCable_comp X h₁ h₂) h₃) h₄) h₅
    simpa [eval, braiding_tensor_left_hom, Category.assoc, tensorHom_id, id_tensorHom] using h
end PropertyF
