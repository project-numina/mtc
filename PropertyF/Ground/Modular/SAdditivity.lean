module
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Dimensions.BiproductTrace

/-!
# Additivity of the categorical S entry

Double-braiding naturality and cyclic pivotal trace make S additive over finite
biproducts. The actual semisimple tensor-product decomposition therefore gives
the fusion-coefficient expansion; the remaining Hopf-link product identity is
isolated precisely as the input needed for the Verlinde character equations.
-/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory CategoryTheory.Limits
open PropertyF.Ground.Dimensions
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

omit [RightRigidCategory C] [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- Double braiding is natural in its first argument. -/
theorem doubleBraiding_natural_left {X Z : C} (f : X ⟶ Z) (Y : C) :
    doubleBraiding X Y ≫ (f ▷ Y) = (f ▷ Y) ≫ doubleBraiding Z Y := by
  unfold doubleBraiding
  simp only [← tensorHom_id]
  rw [Category.assoc, ← braiding_naturality (𝟙 Y) f, ← Category.assoc,
    ← braiding_naturality f (𝟙 Y), Category.assoc]

/-- The S entry is additive over finite biproducts in its first argument. -/
theorem SEntry_biproduct_left {ι : Type*} [Fintype ι] (V : ι → C) [HasBiproduct V]
    (p : PivotalStructure (C := C)) (Y : C) :
    SEntry p (⨁ V) Y = ∑ i, SEntry p (V i) Y := by
  classical
  change p.rightTrace (doubleBraiding (⨁ V) Y) = _
  rw [rightTrace_decomposition p (fun i => biproduct.ι V i ▷ Y)
    (fun i => biproduct.π V i ▷ Y)
    (by simp only [← comp_whiskerRight, ← sum_whiskerRight, biproduct.total, id_whiskerRight]) _]
  apply Finset.sum_congr rfl
  intro i _
  unfold SEntry
  rw [← Category.assoc, ← doubleBraiding_natural_left (biproduct.ι V i) Y,
    Category.assoc, ← comp_whiskerRight, biproduct.ι_π_self, id_whiskerRight,
    Category.comp_id]


omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The S entry is invariant under isomorphism in its first argument. -/
theorem SEntry_iso_left (p : PivotalStructure (C := C)) {X Z : C} (e : X ≅ Z) (Y : C) :
    SEntry p X Y = SEntry p Z Y :=
  (SEntry_symmetric p X Y).trans <|
    (SEntry_iso_right p Y e).trans (SEntry_symmetric p Y Z)

/-- Expanding a tensor product into simple summands expands its S entry with
exactly the fusion coefficients. -/
theorem SEntry_tensor_decomposition (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (i j k : Fin (rank D)) :
    Ground.unitScalarEquiv D (SEntry p (simples D i ⊗ simples D j) (simples D k)) =
      ∑ l, (fusionCoeff D i j l : ℂ) * categoricalS D p l k := by
  let X := simples D i ⊗ simples D j
  let m : Fin (rank D) → ℕ := fun l => fusionCoeff D i j l
  let V : (Σ l, Fin (m l)) → D.Obj := fun t => simples D t.1
  obtain ⟨e⟩ := exists_canonical_decomposition D X
  have he : SEntry p X (simples D k) = SEntry p (⨁ V) (simples D k) :=
    SEntry_iso_left p e _
  rw [he, SEntry_biproduct_left]
  simp [Fintype.sum_sigma, V, m, categoricalS, nsmul_eq_mul]


/-- The categorical Hopf-link product identity implies the Verlinde character
equations once tensor products are decomposed into their simple summands. -/
theorem categoricalS_verlinde_of_hopf_product (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj))
    (hopf : ∀ i j k,
      Ground.unitScalarEquiv D (SEntry p (simples D i ⊗ simples D j) (simples D k)) *
        simpleDimension D p k = categoricalS D p i k * categoricalS D p j k) :
    ∀ i j k,
      (categoricalS D p i k / simpleDimension D p k) *
        (categoricalS D p j k / simpleDimension D p k) =
      ∑ l, (fusionCoeff D i j l : ℂ) * (categoricalS D p l k / simpleDimension D p k) := by
  intro i j k
  have hk := hopf i j k
  rw [SEntry_tensor_decomposition] at hk
  have hd := simpleDimension_ne_zero D p k
  calc
    _ = (categoricalS D p i k * categoricalS D p j k) / simpleDimension D p k ^ 2 := by ring
    _ = ((∑ l, (fusionCoeff D i j l : ℂ) * categoricalS D p l k) *
      simpleDimension D p k) / simpleDimension D p k ^ 2 := by rw [hk]
    _ = (∑ l, (fusionCoeff D i j l : ℂ) * categoricalS D p l k) / simpleDimension D p k := by
      field_simp
    _ = _ := by rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro l _; ring

end PropertyF.Ground.Modular
