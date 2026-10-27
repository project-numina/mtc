module
public import PropertyF.Ground.CentreCabling.VafaTwist
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Complex.Basic

/-!
# Determinants of twists on multiplicity spaces

Determinants of componentwise scalar maps and natural twists on simple-source
multiplicity spaces give the algebraic ingredients of the Vafa relation.
-/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling

/-- A componentwise scalar map on a finite dependent product has determinant
 equal to the product of the scalars, counted by each component dimension. -/
theorem det_dependent_pi_scalar {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (c : ι → ℂ) :
    (LinearMap.pi (fun i => (c i • (1 : V i →ₗ[ℂ] V i)).comp
      (LinearMap.proj i))).det = ∏ i, c i ^ Module.finrank ℂ (V i) := by
  classical
  let b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i) :=
    fun i => Module.finBasis ℂ (V i)
  let B := Pi.basis b
  let f := LinearMap.pi (fun i => (c i • (1 : V i →ₗ[ℂ] V i)).comp
      (LinearMap.proj i))
  have hm : LinearMap.toMatrix B B f = Matrix.diagonal (fun q => c q.1) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    dsimp only [B, f]
    simp only [LinearMap.toMatrix_apply, Matrix.diagonal_apply, Pi.basis_apply,
      Pi.basis_repr, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, LinearMap.coe_proj, Function.eval, LinearMap.id_coe,
      id_eq]
    by_cases h : i = j
    · subst j
      simp [Finsupp.single_apply, eq_comm]
    · simp [Pi.single_apply, h, Ne.symm h]
  rw [← LinearMap.det_toMatrix B, hm, Matrix.det_diagonal, Fintype.prod_sigma]
  simp

end PropertyF.Ground.CentreCabling

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreCabling
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A natural endomorphism acts on maps out of a simple object by its scalar
component at that simple object. -/
theorem natural_postcomp_simple
    (C : Ground.BraidedFusionCategory.{v,u}) (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj)
    (i : Fin (rank C)) (X : C.Obj) :
    CategoryTheory.Linear.rightComp ℂ (simples C i) (α.app X) =
      (Calculus.groundSimpleScalar C i (End.of (α.app (simples C i)))) •
        (1 : (simples C i ⟶ X) →ₗ[ℂ] (simples C i ⟶ X)) := by
  ext f
  have hn := α.naturality f
  simp only [Functor.id_map] at hn
  change f ≫ α.app X = _
  calc
    _ = α.app (simples C i) ≫ f := hn
    _ = _ := by
      have hs := Calculus.groundSimpleScalar_smul_id C i (End.of (α.app (simples C i)))
      change _ = α.app (simples C i) at hs
      conv_lhs => rw [← hs]
      simp

/-- The determinant of a natural endomorphism on a simple-source Hom space
is the simple scalar raised to its actual vector-space dimension. -/
theorem determinant_natural_postcomp_simple
    (C : Ground.BraidedFusionCategory.{v,u}) (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj)
    (i : Fin (rank C)) (X : C.Obj) :
    LinearMap.det (CategoryTheory.Linear.rightComp ℂ (simples C i) (α.app X)) =
      (Calculus.groundSimpleScalar C i (End.of (α.app (simples C i)))) ^
        Module.finrank ℂ (simples C i ⟶ X) := by
  letI : FiniteDimensional ℂ (simples C i ⟶ X) := IsFusionCategory.hom_finite _ _
  rw [natural_postcomp_simple, LinearMap.det_smul]
  simp

/-- The fusion-rule multiplicity is the dimension of the actual lantern Hom
space, using the chosen representative of the dual simple. -/
theorem vafaMultiplicity_eq_finrank (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) :
    vafaMultiplicity C i = Module.finrank ℂ
      (simples C i ⟶ (simples C i ⊗ simples C (dualIndex C i)) ⊗ simples C i) := by
  let X := simples C i
  let Y := simples C (dualIndex C i)
  let e : (X ⊗ Y) ⊗ X ≅ X ⊗ (X ⊗ Y) := CategoryTheory.BraidedCategory.braiding _ _
  calc
    _ = Module.finrank ℂ (X ⟶ X ⊗ (X ⊗ Y)) := by
      unfold vafaMultiplicity
      rw [tensor_multiplicity]
      apply Finset.sum_congr rfl
      intro j hj
      change fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i =
        fusionCoeff C i (dualIndex C i) j * fusionCoeff C i j i
      rw [fusionCoeff_comm C j i]
    _ = _ := (CategoryTheory.Linear.homCongr ℂ (Iso.refl X) e).finrank_eq.symm

/-- The determinant of postcomposition by a diagonal biproduct endomorphism
is the product of its scalar entries with Hom-space multiplicities. -/
theorem determinant_postcomp_biproduct_scalar
    (C : Ground.BraidedFusionCategory.{v,u}) {ι : Type*} [Fintype ι]
    (X : C.Obj) (V : ι → C.Obj) (c : ι → ℂ) :
    LinearMap.det (CategoryTheory.Linear.rightComp ℂ X
      (biproduct.map (fun i => c i • 𝟙 (V i)))) =
      ∏ i, c i ^ Module.finrank ℂ (X ⟶ V i) := by
  classical
  letI : ∀ i, FiniteDimensional ℂ (X ⟶ V i) := fun i => IsFusionCategory.hom_finite _ _
  let e := homBiproductLinearEquiv X V
  let f := CategoryTheory.Linear.rightComp ℂ X (biproduct.map (fun i => c i • 𝟙 (V i)))
  let g := LinearMap.pi (fun i => (c i • (1 : (X ⟶ V i) →ₗ[ℂ] (X ⟶ V i))).comp
    (LinearMap.proj i))
  have hg : (e : _ →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℂ] _) = g := by
    ext z i
    simp [e, f, g, homBiproductLinearEquiv, Category.assoc]
  calc
    _ = LinearMap.det g := by rw [← hg, LinearMap.det_conj]
    _ = _ := det_dependent_pi_scalar (fun i => X ⟶ V i) c

/-- A natural endomorphism tensored with an identity acts diagonally after
a simple decomposition of its first tensor factor. -/
theorem natural_whisker_diagonal
    (C : Ground.BraidedFusionCategory.{v,u}) (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj)
    (A B : C.Obj) :
    let F := Dimensions.simplePiecesObject C A
    let e : A ⊗ B ≅ ⨁ (fun q : Dimensions.simplePieces C A => F q ⊗ B) :=
      (Dimensions.simpleDecomposition C A ⊗ᵢ Iso.refl B) ≪≫ rightDistributor F B
    (α.app A ▷ B) ≫ e.hom = e.hom ≫ biproduct.map (fun q : Dimensions.simplePieces C A =>
      Calculus.groundSimpleScalar C q.1 (End.of (α.app (simples C q.1))) • 𝟙 (F q ⊗ B)) := by
  classical
  let F := Dimensions.simplePiecesObject C A
  let d := Dimensions.simpleDecomposition C A
  let e : A ⊗ B ≅ ⨁ (fun q : Dimensions.simplePieces C A => F q ⊗ B) :=
    (d ⊗ᵢ Iso.refl B) ≪≫ rightDistributor F B
  change (α.app A ▷ B) ≫ e.hom = e.hom ≫ _
  apply (cancel_epi e.inv).mp
  apply biproduct.hom_ext'
  intro q
  simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_map]
  dsimp only [e, Iso.trans_inv, tensorIso_inv, Iso.refl_inv]
  simp only [Category.assoc, biproduct_ι_comp_rightDistributor_inv_assoc, tensorHom_id]
  have hn := α.naturality (biproduct.ι F q ≫ d.inv)
  simp only [Functor.id_map] at hn
  have hs := Calculus.groundSimpleScalar_smul_id C q.1 (End.of (α.app (simples C q.1)))
  change _ = α.app (F q) at hs
  have hn' : biproduct.ι F q ≫ d.inv ≫ α.app A =
      Calculus.groundSimpleScalar C q.1 (End.of (α.app (simples C q.1))) •
        (biproduct.ι F q ≫ d.inv) := by
    calc
      _ = α.app (F q) ≫ (biproduct.ι F q ≫ d.inv) := by simpa [Category.assoc] using hn
      _ = _ := by
        conv_lhs => rw [← hs]
        simp [Category.assoc, F, Dimensions.simplePiecesObject, Linear.smul_comp]
  simp only [← comp_whiskerRight_assoc]
  rw [hn']
  simp [e, Category.assoc, Linear.smul_comp, F, Dimensions.simplePiecesObject]

set_option backward.isDefEq.respectTransparency false in
/-- Determinant of a natural endomorphism on the first tensor factor, acting
on an arbitrary simple-source Hom space, computed in a simple decomposition. -/
theorem determinant_natural_whisker
    (C : Ground.BraidedFusionCategory.{v,u}) (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj)
    (X A B : C.Obj) :
    LinearMap.det (CategoryTheory.Linear.rightComp ℂ X (α.app A ▷ B)) =
      ∏ q : Dimensions.simplePieces C A,
        (Calculus.groundSimpleScalar C q.1 (End.of (α.app (simples C q.1)))) ^
          Module.finrank ℂ (X ⟶ Dimensions.simplePiecesObject C A q ⊗ B) := by
  classical
  let F := Dimensions.simplePiecesObject C A
  let e : A ⊗ B ≅ ⨁ (fun q : Dimensions.simplePieces C A => F q ⊗ B) :=
    (Dimensions.simpleDecomposition C A ⊗ᵢ Iso.refl B) ≪≫ rightDistributor F B
  let c (q : Dimensions.simplePieces C A) :=
    Calculus.groundSimpleScalar C q.1 (End.of (α.app (simples C q.1)))
  let E := CategoryTheory.Linear.homCongr ℂ (Iso.refl X) e
  let f : (X ⟶ A ⊗ B) →ₗ[ℂ] (X ⟶ A ⊗ B) :=
    CategoryTheory.Linear.rightComp ℂ X (α.app A ▷ B)
  let g := CategoryTheory.Linear.rightComp ℂ X (biproduct.map (fun q => c q • 𝟙 (F q ⊗ B)))
  have hc := natural_whisker_diagonal C α A B
  change (α.app A ▷ B) ≫ e.hom = e.hom ≫ biproduct.map (fun q => c q • 𝟙 (F q ⊗ B)) at hc
  have hg : (E : _ →ₗ[ℂ] _) ∘ₗ f ∘ₗ (E.symm : _ →ₗ[ℂ] _) = g := by
    ext z
    simp only [E, f, g, LinearMap.comp_apply, CategoryTheory.Linear.rightComp_apply]
    simp [CategoryTheory.Linear.homCongr, Category.assoc, hc]
  change LinearMap.det f = _
  calc
    _ = LinearMap.det g := by rw [← hg, LinearMap.det_conj]
    _ = _ := determinant_postcomp_biproduct_scalar C X (fun q => F q ⊗ B) c

/-- The first pair-twist determinant in the Vafa lantern argument, expressed
using fusion coefficients. -/
theorem determinant_vafa_first_pair
    (C : Ground.BraidedFusionCategory.{v,u}) (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj)
    (i : Fin (rank C)) :
    LinearMap.det (CategoryTheory.Linear.rightComp ℂ (simples C i)
      (α.app (simples C i ⊗ simples C (dualIndex C i)) ▷ simples C i)) =
    ∏ j, (Calculus.groundSimpleScalar C j (End.of (α.app (simples C j)))) ^
      (fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i) := by
  classical
  rw [determinant_natural_whisker]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j hj
  change (∏ _ : Fin (fusionCoeff C i (dualIndex C i) j),
      (Calculus.groundSimpleScalar C j (End.of (α.app (simples C j)))) ^
        fusionCoeff C j i i) = _
  simp [← pow_mul, Nat.mul_comm]

/-- Pair-twist determinant for arbitrary simple labels and source. -/
theorem determinant_vafa_pair
    (C : Ground.BraidedFusionCategory.{v,u}) (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj)
    (s a b c : Fin (rank C)) :
    LinearMap.det (CategoryTheory.Linear.rightComp ℂ (simples C s)
      (α.app (simples C a ⊗ simples C b) ▷ simples C c)) =
    ∏ j, (Calculus.groundSimpleScalar C j (End.of (α.app (simples C j)))) ^
      (fusionCoeff C a b j * fusionCoeff C j c s) := by
  classical
  rw [determinant_natural_whisker, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j hj
  change (∏ _ : Fin (fusionCoeff C a b j),
      (Calculus.groundSimpleScalar C j (End.of (α.app (simples C j)))) ^
        fusionCoeff C j c s) = _
  simp [← pow_mul, Nat.mul_comm]

/-- Conjugating an endomorphism by an isomorphism of its target object does
not change its determinant on a Hom space. -/
theorem determinant_postcomp_iso_conjugate
    (C : Ground.BraidedFusionCategory.{v,u}) (X Y Z : C.Obj)
    (e : Y ≅ Z) (a : Z ⟶ Z) :
    LinearMap.det (CategoryTheory.Linear.rightComp ℂ X (e.hom ≫ a ≫ e.inv)) =
      LinearMap.det (CategoryTheory.Linear.rightComp ℂ X a) := by
  let E := CategoryTheory.Linear.homCongr ℂ (Iso.refl X) e
  let f := CategoryTheory.Linear.rightComp ℂ X (e.hom ≫ a ≫ e.inv)
  let g := CategoryTheory.Linear.rightComp ℂ X a
  have hg : (E : _ →ₗ[ℂ] _) ∘ₗ f ∘ₗ (E.symm : _ →ₗ[ℂ] _) = g := by
    ext z
    simp [E, f, g, CategoryTheory.Linear.homCongr, Category.assoc]
  calc
    _ = LinearMap.det g := by rw [← hg, LinearMap.det_conj]
    _ = _ := rfl

/-- Any transported pair-twist operator has the same fusion-rule determinant. -/
theorem determinant_vafa_pair_conjugate
    (C : Ground.BraidedFusionCategory.{v,u}) (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj)
    (s a b c : Fin (rank C)) (W : C.Obj)
    (e : W ≅ (simples C a ⊗ simples C b) ⊗ simples C c) :
    LinearMap.det (CategoryTheory.Linear.rightComp ℂ (simples C s)
      (e.hom ≫ (α.app (simples C a ⊗ simples C b) ▷ simples C c) ≫ e.inv)) =
    ∏ j, (Calculus.groundSimpleScalar C j (End.of (α.app (simples C j)))) ^
      (fusionCoeff C a b j * fusionCoeff C j c s) := by
  rw [determinant_postcomp_iso_conjugate, determinant_vafa_pair]

/-- Postcomposition determinants multiply under composition. -/
theorem determinant_postcomp_comp
    (C : Ground.BraidedFusionCategory.{v,u}) (X Y : C.Obj) (f g : Y ⟶ Y) :
    LinearMap.det (CategoryTheory.Linear.rightComp ℂ X (f ≫ g)) =
      LinearMap.det (CategoryTheory.Linear.rightComp ℂ X f) *
        LinearMap.det (CategoryTheory.Linear.rightComp ℂ X g) := by
  have h : CategoryTheory.Linear.rightComp ℂ X (f ≫ g) =
      (CategoryTheory.Linear.rightComp ℂ X g).comp (CategoryTheory.Linear.rightComp ℂ X f) := by
    ext z
    simp [Category.assoc]
  rw [h, LinearMap.det_comp, mul_comm]

/-- Postcomposition by a scalar multiple scales the determinant by that scalar
raised to the actual dimension of the Hom space. -/
theorem determinant_postcomp_smul
    (C : Ground.BraidedFusionCategory.{v,u}) (X Y : C.Obj) (z : ℂ) (f : Y ⟶ Y) :
    LinearMap.det (CategoryTheory.Linear.rightComp ℂ X (z • f)) =
      z ^ Module.finrank ℂ (X ⟶ Y) *
        LinearMap.det (CategoryTheory.Linear.rightComp ℂ X f) := by
  letI : FiniteDimensional ℂ (X ⟶ Y) := IsFusionCategory.hom_finite _ _
  have h : CategoryTheory.Linear.rightComp ℂ X (z • f) =
      z • CategoryTheory.Linear.rightComp ℂ X f := by
    ext w
    simp
  rw [h, LinearMap.det_smul]

end PropertyF.Ground.CentreCabling
