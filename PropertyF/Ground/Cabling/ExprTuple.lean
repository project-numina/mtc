module
public import PropertyF.Ground.Cabling.ExprPowers
public import PropertyF.Ground.Cabling.TupleIsoStep
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The right-associated expression corresponding to a tuple of power blocks. -/
def PowerExpr.tuple {I : Type} (k : I → ℕ) : ∀ n, (Fin n → I) → PowerExpr
  | 0, _ => .unit
  | n+1, t => .tensor (power (k (t 0))) (tuple k n (Fin.tail t))

theorem PowerExpr.tuple_length {I : Type} (k : I → ℕ) : ∀ n (t : Fin n → I),
    (tuple k n t).length = ∑ i, k (t i)
  | 0, _ => by simp [tuple, length]
  | n+1, t => by simp [tuple, length, power_length, tuple_length k n (Fin.tail t), Fin.sum_univ_succ, Fin.tail]

theorem PowerExpr.eval_tuple {I : Type} (X : C) (k : I → ℕ) : ∀ n (t : Fin n → I),
    (tuple k n t).eval X = tupleTensor (fun i => tensorPower X (k i)) n t
  | 0, _ => rfl
  | n+1, t => by
    change (power (k (t 0))).eval X ⊗ (tuple k n (Fin.tail t)).eval X =
      tensorPower X (k (t 0)) ⊗ tupleTensor (fun i => tensorPower X (k i)) n (Fin.tail t)
    rw [eval_power, eval_tuple X k n (Fin.tail t)]

/-- Tensor-power comparison commutes with transport of both strand counts. -/
theorem powerTensor_transport (X : C) {a a' b b' : ℕ} (ha : a = a') (hb : b = b') :
    (tensorPowerTensorIso X a b).hom ≫
      eqToHom (congrArg (tensorPower X) (congrArg₂ Nat.add ha hb)) =
    (eqToHom (congrArg (tensorPower X) ha) ⊗ₘ eqToHom (congrArg (tensorPower X) hb)) ≫
      (tensorPowerTensorIso X a' b').hom := by
  cases ha; cases hb
  simp

theorem tensor_eqToHom {A A' B B' : C} (ha : A = A') (hb : B = B') :
    eqToHom ha ⊗ₘ eqToHom hb = eqToHom (congrArg₂ (· ⊗ ·) ha hb) := by
  cases ha; cases hb
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Expression normalization agrees with the tuple-to-power isomorphism. -/
theorem PowerExpr.normalize_tuple (X : C) (k : Fin count → ℕ) : ∀ n (t : Fin n → Fin count),
    ((tuple k n t).normalize X).hom ≫
      eqToHom (congrArg (tensorPower X) (tuple_length k n t)) =
    eqToHom (eval_tuple X k n t) ≫ (tupleTensorPowersIso X k n t).hom
  | 0, t => by simp [tuple, normalize, tupleTensorPowersIso, eval, tensorPower]
  | n+1, t => by
    let l := k (t 0)
    let r := tuple k n (Fin.tail t)
    let m := ∑ i, k (Fin.tail t i)
    have h₁ : (power l).length = l := power_length l
    have h₂ : r.length = m := tuple_length k n (Fin.tail t)
    have hp := normalize_power X l
    have ht := normalize_tuple X k n (Fin.tail t)
    have htrans := powerTensor_transport X h₁ h₂
    change ((power l).normalize X).hom ≫ eqToHom (congrArg (tensorPower X) h₁) =
      eqToHom (eval_power X l) at hp
    change (r.normalize X).hom ≫ eqToHom (congrArg (tensorPower X) h₂) =
      eqToHom (eval_tuple X k n (Fin.tail t)) ≫
        (tupleTensorPowersIso X k n (Fin.tail t)).hom at ht
    let s : l+m = ∑ i, k (t i) := by simp [l, m, Fin.sum_univ_succ, Fin.tail]
    have hsum : eqToHom (congrArg (tensorPower X) (congrArg₂ Nat.add h₁ h₂)) ≫
        eqToHom (congrArg (tensorPower X) s) =
        eqToHom (congrArg (tensorPower X) (tuple_length k (n+1) t)) := by rw [eqToHom_trans]
    have heval : eqToHom (eval_power X l) ⊗ₘ eqToHom (eval_tuple X k n (Fin.tail t)) =
        eqToHom (eval_tuple X k (n+1) t) := by
      exact tensor_eqToHom (eval_power X l) (eval_tuple X k n (Fin.tail t))
    have hiso := tupleTensorPowersIso_succ_hom X k n t
    change (tupleTensorPowersIso X k (n+1) t).hom =
      (𝟙 (tensorPower X l) ⊗ₘ (tupleTensorPowersIso X k n (Fin.tail t)).hom) ≫
        (tensorPowerTensorIso X l m).hom ≫ eqToHom (congrArg (tensorPower X) s) at hiso
    change ((((power l).normalize X).hom ⊗ₘ (r.normalize X).hom) ≫
      (tensorPowerTensorIso X (power l).length r.length).hom) ≫
        eqToHom (congrArg (tensorPower X) (tuple_length k (n+1) t)) =
      eqToHom (eval_tuple X k (n+1) t) ≫ (tupleTensorPowersIso X k (n+1) t).hom
    rw [← hsum]
    simp only [Category.assoc]
    rw [reassoc_of% htrans]
    slice_lhs 1 2 =>
      rw [tensorHom_comp_tensorHom, hp, ht]
    rw [hiso, ← heval]
    slice_rhs 1 2 =>
      rw [tensorHom_comp_tensorHom, Category.comp_id]
end PropertyF
