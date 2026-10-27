module
public import PropertyF.Ground.Cabling.ExprTupleCross
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Cabled maps are stable under equality transports of their strand counts. -/
theorem cableHom_reindex (X : C) {a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    (f : tensorPower X a ⟶ tensorPower X b) (hf : cableHom X a b f) :
    cableHom X a' b' (eqToHom (congrArg (tensorPower X) ha.symm) ≫ f ≫
      eqToHom (congrArg (tensorPower X) hb)) := by
  subst a'
  subst b'
  simpa using hf

set_option backward.isDefEq.respectTransparency false in
/-- Each tuple generator crossing, under the original tuple normalization,
is an actual cabled braid. -/
theorem powerSum_tuple_cross_cabled (X : C) (k : Fin count → ℕ)
    (n : ℕ) (j : Fin (n+1)) (t : Fin (n+2) → Fin count) :
    ∃ e : tupleTensor (fun a => tensorPower X (k a)) (n+2) t ≅
        tupleTensor (fun a => tensorPower X (k a)) (n+2) (swapTuple j t),
      tupleTensorInclusion (fun a => tensorPower X (k a)) (n+2) t ≫
        (braidGenerator (⨁ fun a => tensorPower X (k a)) n j).asIso.hom =
          e.hom ≫ tupleTensorInclusion (fun a => tensorPower X (k a)) (n+2) (swapTuple j t) ∧
      cableHom X (∑ i, k (t i)) (∑ i, k (swapTuple j t i))
        ((tupleTensorPowersIso X k (n+2) t).inv ≫ e.hom ≫
          (tupleTensorPowersIso X k (n+2) (swapTuple j t)).hom) := by
  let t' := swapTuple j t
  let A := PowerExpr.tuple k (n+2) t
  let B := PowerExpr.tuple k (n+2) t'
  let s := eqToIso (PowerExpr.eval_tuple X k (n+2) t)
  let r := eqToIso (PowerExpr.eval_tuple X k (n+2) t')
  let p := eqToIso (congrArg (tensorPower X) (PowerExpr.tuple_length k (n+2) t))
  let q := eqToIso (congrArg (tensorPower X) (PowerExpr.tuple_length k (n+2) t'))
  let S := tupleTensorPowersIso X k (n+2) t
  let T := tupleTensorPowersIso X k (n+2) t'
  have hS : A.normalize X ≪≫ p = s ≪≫ S := by
    apply Iso.ext
    exact PowerExpr.normalize_tuple X k (n+2) t
  have hT : B.normalize X ≪≫ q = r ≪≫ T := by
    apply Iso.ext
    exact PowerExpr.normalize_tuple X k (n+2) t'
  obtain ⟨e, he, hcross⟩ := exprTuple_cross_cabled X k n j t
  let e' := s.symm ≪≫ e ≪≫ r
  refine ⟨e', ?_, ?_⟩
  · have h := congrArg (fun z => s.inv ≫ z) hcross
    change s.inv ≫ ((s.hom ≫ tupleTensorInclusion (fun a => tensorPower X (k a)) (n+2) t) ≫ _) =
      s.inv ≫ (e.hom ≫ (r.hom ≫ tupleTensorInclusion (fun a => tensorPower X (k a)) (n+2) t')) at h
    simpa [e', Category.assoc] using h
  · have hc := cableHom_reindex X (PowerExpr.tuple_length k (n+2) t)
      (PowerExpr.tuple_length k (n+2) t') _ he
    have hleft : S.inv ≫ s.inv = p.inv ≫ (A.normalize X).inv := by
      have h := congrArg Iso.inv hS
      simpa using h.symm
    have hright : r.hom ≫ T.hom = (B.normalize X).hom ≫ q.hom := by
      have h := congrArg Iso.hom hT
      simpa using h.symm
    change cableHom X _ _ (S.inv ≫ e'.hom ≫ T.hom)
    have heq : S.inv ≫ e'.hom ≫ T.hom =
        p.inv ≫ ((A.normalize X).inv ≫ e.hom ≫ (B.normalize X).hom) ≫ q.hom := by
      dsimp only [e', Iso.trans_hom, Iso.symm_hom]
      simp only [Category.assoc]
      rw [← Category.assoc S.inv s.inv, hleft]
      simp only [Category.assoc]
      rw [hright]
    rw [heq]
    exact hc
end PropertyF
