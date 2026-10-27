module
public import PropertyF.Ground.Cabling.ExprPowers
public import PropertyF.Ground.Cabling.TensorDecomposition
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

lemma castIso_hom_right {A B D : C} (h : D = B) (e : A ≅ D) :
    (cast (congrArg (fun Z : C => A ≅ Z) h) e).hom = e.hom ≫ eqToHom h := by
  cases h
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Successor step of the tuple-to-power comparison, with strand-count
transport made explicit. -/
theorem tupleTensorPowersIso_succ_hom (X : C) (k : Fin count → ℕ) (n : ℕ) (t : Fin (n+1) → Fin count) :
    (tupleTensorPowersIso X k (n+1) t).hom =
      (𝟙 (tensorPower X (k (t 0))) ⊗ₘ (tupleTensorPowersIso X k n (Fin.tail t)).hom) ≫
        (tensorPowerTensorIso X (k (t 0)) (∑ i, k (Fin.tail t i))).hom ≫
          eqToHom (congrArg (tensorPower X) (by simp [Fin.sum_univ_succ, Fin.tail])) := by
  let m := ∑ i, k (Fin.tail t i)
  let s : k (t 0) + m = ∑ i, k (t i) := by simp [m, Fin.sum_univ_succ, Fin.tail]
  let e := (Iso.refl (tensorPower X (k (t 0))) ⊗ᵢ tupleTensorPowersIso X k n (Fin.tail t)) ≪≫
    tensorPowerTensorIso X (k (t 0)) m
  let h := congrArg (tensorPower X) s
  change (cast (congrArg (fun Z : C => tupleTensor (fun i => tensorPower X (k i)) (n+1) t ≅ Z) h) e).hom = _
  simpa [e, h, m, Category.assoc] using castIso_hom_right h e
end PropertyF
