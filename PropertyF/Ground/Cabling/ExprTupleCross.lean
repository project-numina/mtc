module
public import PropertyF.Ground.Cabling.ExprTuple
public import PropertyF.Ground.Cabling.TupleIso
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A tuple block inclusion with its domain expressed as a tensor expression. -/
def exprTupleInclusion (X : C) (k : Fin count → ℕ) (n : ℕ) (t : Fin n → Fin count) :
    (PowerExpr.tuple k n t).eval X ⟶ tensorPower (⨁ fun i => tensorPower X (k i)) n :=
  eqToHom (PowerExpr.eval_tuple X k n t) ≫ tupleTensorInclusion (fun i => tensorPower X (k i)) n t

set_option backward.isDefEq.respectTransparency false in
/-- The expression tuple inclusion tensors its first factor with its tail. -/
theorem exprTupleInclusion_succ (X : C) (k : Fin count → ℕ) (n : ℕ) (t : Fin (n+1) → Fin count) :
    exprTupleInclusion X k (n+1) t =
      (eqToHom (PowerExpr.eval_power X (k (t 0))) ≫ biproduct.ι (fun i => tensorPower X (k i)) (t 0)) ⊗ₘ
        exprTupleInclusion X k n (Fin.tail t) := by
  have he : eqToHom (PowerExpr.eval_tuple X k (n+1) t) =
      eqToHom (PowerExpr.eval_power X (k (t 0))) ⊗ₘ
        eqToHom (PowerExpr.eval_tuple X k n (Fin.tail t)) := by
    symm
    exact tensor_eqToHom (PowerExpr.eval_power X (k (t 0))) (PowerExpr.eval_tuple X k n (Fin.tail t))
  change eqToHom (PowerExpr.eval_tuple X k (n+1) t) ≫
      (biproduct.ι (fun i => tensorPower X (k i)) (t 0) ⊗ₘ
        tupleTensorInclusion (fun i => tensorPower X (k i)) n (Fin.tail t)) = _
  rw [he, tensorHom_comp_tensorHom]
  rfl
set_option backward.isDefEq.respectTransparency false in
/-- The mixed crossing of two expression blocks with a spectator expression
is a cabled map. -/
theorem PowerExpr.isCable_firstMixed (X : C) (a b c : PowerExpr) :
    IsCable X (.tensor a (.tensor b c)) (.tensor b (.tensor a c))
      (firstMixedBraid (a.eval X) (b.eval X) (c.eval X)).hom := by
  have h₁ := isCable_inv X (a := .tensor (.tensor a b) c) (b := .tensor a (.tensor b c))
    (α_ (a.eval X) (b.eval X) (c.eval X)) (isCable_assoc X a b c)
  have h₂ := isCable_tensor X (isCable_braiding X a b) (isCable_id X c)
  have h₃ := isCable_assoc X b a c
  have h := isCable_comp X (isCable_comp X h₁ h₂) h₃
  simpa [firstMixedBraid, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
/-- A mixed crossing with an arbitrary first-strand map can be shifted past
a spectator. -/
theorem tailBraid_components_general (Y : C) (n : ℕ) (i : Fin (n+1))
    {A U V : C} (f : A ⟶ Y) (u : U ⟶ tensorPower Y (n+2))
    (v : V ⟶ tensorPower Y (n+2)) (g : U ⟶ V)
    (h : u ≫ (braidGenerator Y n i).asIso.hom = g ≫ v) :
    (f ⊗ₘ u) ≫ (braidGenerator Y (n+1) i.succ).asIso.hom =
      (𝟙 A ⊗ₘ g) ≫ (f ⊗ₘ v) := by
  rcases i with ⟨i, hi⟩
  have hg : braidGenerator Y (n+1) (⟨i, hi⟩ : Fin (n+1)).succ =
      Aut.of (Iso.refl Y ⊗ᵢ (braidGenerator Y n ⟨i, hi⟩).asIso) := by
    rfl
  rw [hg]
  simp only [tensorIso_hom, Iso.refl_hom, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, h]
set_option backward.isDefEq.respectTransparency false in
/-- The first crossing of expression tuple blocks is a cabled isomorphism. -/
theorem exprTuple_first_cabled (X : C) (k : Fin count → ℕ) (n : ℕ)
    (t : Fin (n+2) → Fin count) :
    ∃ e : (PowerExpr.tuple k (n+2) t).eval X ≅
        (PowerExpr.tuple k (n+2) (swapTuple 0 t)).eval X,
      PowerExpr.IsCable X (PowerExpr.tuple k (n+2) t)
        (PowerExpr.tuple k (n+2) (swapTuple 0 t)) e.hom ∧
      exprTupleInclusion X k (n+2) t ≫ (braidGenerator (⨁ fun i => tensorPower X (k i)) n 0).asIso.hom =
        e.hom ≫ exprTupleInclusion X k (n+2) (swapTuple 0 t) := by
  rw [swapTuple_zero]
  let a := PowerExpr.power (k (t 0))
  let b := PowerExpr.power (k (t 1))
  let c := PowerExpr.tuple k n (Fin.tail (Fin.tail t))
  let e := firstMixedBraid (a.eval X) (b.eval X) (c.eval X)
  refine ⟨e, ?_, ?_⟩
  · exact PowerExpr.isCable_firstMixed X a b c
  · let Y := ⨁ fun i => tensorPower X (k i)
    let f := eqToHom (PowerExpr.eval_power X (k (t 0))) ≫ biproduct.ι (fun i => tensorPower X (k i)) (t 0)
    let g := eqToHom (PowerExpr.eval_power X (k (t 1))) ≫ biproduct.ι (fun i => tensorPower X (k i)) (t 1)
    let h := exprTupleInclusion X k n (Fin.tail (Fin.tail t))
    have hn := firstMixedBraid_natural f g h
    have heval : braidGenerator Y n 0 = Aut.of (firstMixedBraid Y Y (tensorPower Y n)) := by cases n <;> rfl
    rw [heval]
    simp only [exprTupleInclusion_succ, Fin.cons_zero, Fin.tail_cons]
    exact hn.symm
set_option backward.isDefEq.respectTransparency false in
/-- Each generator acts on each expression tuple by a cabled isomorphism. -/
theorem exprTuple_cross_cabled (X : C) (k : Fin count → ℕ) :
    ∀ (n : ℕ) (i : Fin (n+1)) (t : Fin (n+2) → Fin count),
      ∃ e : (PowerExpr.tuple k (n+2) t).eval X ≅
          (PowerExpr.tuple k (n+2) (swapTuple i t)).eval X,
        PowerExpr.IsCable X (PowerExpr.tuple k (n+2) t)
          (PowerExpr.tuple k (n+2) (swapTuple i t)) e.hom ∧
        exprTupleInclusion X k (n+2) t ≫ (braidGenerator (⨁ fun i => tensorPower X (k i)) n i).asIso.hom =
          e.hom ≫ exprTupleInclusion X k (n+2) (swapTuple i t) := by
  intro n
  induction n with
  | zero =>
    intro i t
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact exprTuple_first_cabled X k 0 t
  | succ n ih =>
    intro i t
    refine Fin.cases (exprTuple_first_cabled X k (n+1) t) (fun j => ?_) i
    obtain ⟨e, he, hg⟩ := ih j (Fin.tail t)
    rw [swapTuple_succ]
    let a := PowerExpr.power (k (t 0))
    refine ⟨Iso.refl (a.eval X) ⊗ᵢ e, ?_, ?_⟩
    · exact PowerExpr.isCable_tensor X (PowerExpr.isCable_id X a) he
    · let f := eqToHom (PowerExpr.eval_power X (k (t 0))) ≫
        biproduct.ι (fun i => tensorPower X (k i)) (t 0)
      have h := tailBraid_components_general (⨁ fun i => tensorPower X (k i)) n j f
        (exprTupleInclusion X k (n+2) (Fin.tail t))
        (exprTupleInclusion X k (n+2) (swapTuple j (Fin.tail t))) e.hom hg
      rw [exprTupleInclusion_succ X k (n+2) t,
        exprTupleInclusion_succ X k (n+2) (Fin.cons (t 0) (swapTuple j (Fin.tail t)))]
      change (f ⊗ₘ exprTupleInclusion X k (n+2) (Fin.tail t)) ≫
        (braidGenerator (⨁ fun i => tensorPower X (k i)) (n+1) j.succ).asIso.hom =
          (𝟙 (a.eval X) ⊗ₘ e.hom) ≫
            (f ⊗ₘ exprTupleInclusion X k (n+2) (swapTuple j (Fin.tail t)))
      exact h
end PropertyF
