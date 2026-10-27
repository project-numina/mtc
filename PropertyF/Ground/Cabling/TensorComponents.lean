module
public import PropertyF.Ground.Cabling.TensorDecomposition
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C]
attribute [local instance] Abelian.hasFiniteBiproducts

omit [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] in
set_option backward.isDefEq.respectTransparency false in
/-- Flattening sends each pair-indexed injection to the iterated injection. -/
theorem flattenFiniteBiproduct_ι_inv {I J : Type} [Fintype I] [Fintype J]
    (f : I → J → C) (i : I) (j : J) :
    biproduct.ι (fun p : I × J => f p.1 p.2) (i,j) ≫ (flattenFiniteBiproduct f).inv =
      biproduct.ι (f i) j ≫ biproduct.ι (fun i => ⨁ f i) i := by
  classical
  apply biproduct.hom_ext
  intro k
  apply biproduct.hom_ext
  intro l
  simp [flattenFiniteBiproduct, Category.assoc, biproduct.isoProduct_inv,
    Pi.whiskerEquiv, piPiIso, Pi.map'_comp_π, biproduct.ι_π]
  by_cases h : i = k
  · subst k
    by_cases h' : j = l <;> simp [h', biproduct.ι_π]
  · simp [h]
omit [BraidedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse tensor-distribution map sends a block injection to the
tensor product of its two factor injections. -/
theorem tensorFiniteBiproduct_ι_inv {I J : Type} [Fintype I] [Fintype J]
    (f : I → C) (g : J → C) (i : I) (j : J) :
    biproduct.ι (fun p : I × J => f p.1 ⊗ g p.2) (i,j) ≫ (tensorFiniteBiproduct f g).inv =
      biproduct.ι f i ⊗ₘ biproduct.ι g j := by
  simp only [tensorFiniteBiproduct, Iso.trans_inv, Category.assoc]
  rw [reassoc_of% (flattenFiniteBiproduct_ι_inv (fun i j => f i ⊗ g j) i j)]
  simp [biproduct.mapIso_inv, tensorHom_def, whisker_exchange]
/-- Inclusion of a tuple block into the tensor power of the biproduct. -/
def tupleTensorInclusion {I : Type} [Fintype I] (f : I → C) : ∀ (n : ℕ) (t : Fin n → I),
    tupleTensor f n t ⟶ tensorPower (⨁ f) n
  | 0, _ => 𝟙 _
  | n + 1, t => biproduct.ι f (t 0) ⊗ₘ tupleTensorInclusion f n (Fin.tail t)

omit [BraidedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed decomposition has the expected tuple-block inclusions. -/
theorem tensorPowerBiproductIso_ι_inv {I : Type} [Fintype I] (f : I → C) :
    ∀ (n : ℕ) (t : Fin n → I),
      biproduct.ι (tupleTensor f n) t ≫ (tensorPowerBiproductIso f n).inv = tupleTensorInclusion f n t
  | 0, t => by
      simp [tensorPowerBiproductIso, tupleTensorInclusion, biproductUniqueIso]
  | n + 1, t => by
      simp only [tensorPowerBiproductIso, tupleTensorInclusion, Iso.trans_inv,
        tensorIso_inv, Iso.refl_inv, biproduct.whiskerEquiv_inv,
        biproduct.ι_desc_assoc, Fin.consEquiv, Equiv.coe_fn_symm_mk,
        Category.assoc]
      rw [reassoc_of% (tensorFiniteBiproduct_ι_inv f (tupleTensor f n) (t 0) (Fin.tail t))]
      simp only [eqToHom_refl, Category.id_comp]
      dsimp only [id, Iso.refl_hom]
      change 𝟙 (f (t 0) ⊗ tupleTensor f n (Fin.tail t)) ≫
        (biproduct.ι f (t 0) ⊗ₘ biproduct.ι (tupleTensor f n) (Fin.tail t)) ≫
        (𝟙 (⨁ f) ⊗ₘ (tensorPowerBiproductIso f n).inv) =
        biproduct.ι f (t 0) ⊗ₘ tupleTensorInclusion f n (Fin.tail t)
      rw [Category.id_comp, tensorHom_comp_tensorHom, Category.comp_id, tensorPowerBiproductIso_ι_inv]
omit [BraidedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The cabled block inclusion is the tuple inclusion after the block-power isomorphism. -/
theorem sumPowersTensorPowerIso_ι_inv {I : Type} [Fintype I] (X : C) (k : I → ℕ)
    (n : ℕ) (t : Fin n → I) :
    biproduct.ι (fun t : Fin n → I => tensorPower X (∑ i, k (t i))) t ≫
      (sumPowersTensorPowerIso X k n).inv =
    (tupleTensorPowersIso X k n t).inv ≫
      tupleTensorInclusion (fun i => tensorPower X (k i)) n t := by
  simp only [sumPowersTensorPowerIso, Iso.trans_inv,
    biproduct.mapIso_inv, biproduct.ι_map_assoc]
  rw [tensorPowerBiproductIso_ι_inv]

end PropertyF
