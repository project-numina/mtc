module
public import PropertyF.Ground.Cabling.ExprBraiding
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The expression for a right-associated tensor power. -/
def PowerExpr.power : ℕ → PowerExpr
  | 0 => .unit
  | n+1 => .tensor .atom (power n)

theorem PowerExpr.power_length : ∀ n, (power n).length = n
  | 0 => rfl
  | n+1 => by simp [power, length, power_length n, Nat.add_comm]

/-- Evaluation of a power expression is the actual tensor power. -/
theorem PowerExpr.eval_power (X : C) : ∀ n, (power n).eval X = tensorPower X n
  | 0 => rfl
  | n+1 => by change X ⊗ (power n).eval X = X ⊗ tensorPower X n; rw [eval_power X n]

set_option backward.isDefEq.respectTransparency false in
/-- Normalizing a power expression and transporting its length gives its
evaluation comparison. -/
theorem PowerExpr.normalize_power (X : C) : ∀ n,
    ((power n).normalize X).hom ≫
      eqToHom (congrArg (tensorPower X) (power_length n)) = eqToHom (eval_power X n)
  | 0 => by simp [power, normalize, length, tensorPower]
  | n+1 => by
    let l := (power n).length
    let h₁ : tensorPower X (1+l) = tensorPower X (l+1) := congrArg (tensorPower X) (by omega)
    let h₂ : tensorPower X (l+1) = tensorPower X (n+1) :=
      congrArg (fun j => tensorPower X (j+1)) (power_length n)
    have htrans : eqToHom h₁ ≫ eqToHom h₂ =
        eqToHom (congrArg (tensorPower X) (power_length (n+1))) := by rw [eqToHom_trans]
    have hmapGen {a b : ℕ} (h : a = b) :
        eqToHom (congrArg (fun j => tensorPower X (j+1)) h) =
          (𝟙 X ⊗ₘ eqToHom (congrArg (tensorPower X) h)) := by
      cases h
      change 𝟙 (X ⊗ tensorPower X a) = 𝟙 X ⊗ₘ 𝟙 (tensorPower X a)
      exact (id_tensorHom_id _ _).symm
    have hmap : eqToHom h₂ = 𝟙 X ⊗ₘ eqToHom (congrArg (tensorPower X) (power_length n)) :=
      hmapGen (power_length n)
    have hn : (tensorPowerTensorIso X 1 l).hom ≫ eqToHom h₁ =
        (ρ_ X).hom ▷ tensorPower X l := powerTensor_one_left X l
    change (((ρ_ X).inv ⊗ₘ ((power n).normalize X).hom) ≫
      (tensorPowerTensorIso X 1 l).hom) ≫
        eqToHom (congrArg (tensorPower X) (power_length (n+1))) = eqToHom (eval_power X (n+1))
    rw [← htrans]
    simp only [Category.assoc]
    rw [reassoc_of% hn, hmap]
    have hi := normalize_power X n
    change ((power n).normalize X).hom ≫
      eqToHom (congrArg (tensorPower X) (power_length n)) = eqToHom (eval_power X n) at hi
    rw [← tensorHom_id]
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    simp only [Iso.inv_hom_id, Category.comp_id]
    rw [tensorHom_comp_tensorHom]
    rw [Category.id_comp, Category.comp_id]
    change (𝟙 X ⊗ₘ (((power n).normalize X).hom ≫
      eqToHom (congrArg (tensorPower X) (power_length n)))) = eqToHom (eval_power X (n+1))
    rw [hi]
    have hmapEval {A B : C} (h : A = B) : (𝟙 X ⊗ₘ eqToHom h) =
        eqToHom (congrArg (fun Z : C => X ⊗ Z) h) := by cases h; simp
    rw [hmapEval]
end PropertyF
