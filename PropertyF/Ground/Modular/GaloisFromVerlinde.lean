module
public import PropertyF.Ground.Modular.Classification
public import PropertyF.Ground.Modular.DimensionNonzero

/-!
# Galois action from Verlinde's equations

The classification and complex-automorphism action require no old modular-data
bundle. The remaining hypotheses of the categorical theorem are stated as the
specific S-square, global nonvanishing and Verlinde equations that must be
proved from a nondegenerate spherical fusion category.
-/
open scoped BigOperators
open PropertyF.Ground.Dimensions
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular

/-- The full action on normalized columns follows from S-square and the
Verlinde character equations, without an assumed character classification. -/
theorem exists_galoisLabel_of_verlinde {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : FusionRules ι) (S : Matrix ι ι ℂ) (dual : ι → ι)
    (d : ι → ℂ) (D : ℂ) (hd : ∀ y, d y ≠ 0) (hD : D ≠ 0)
    (hsym : ∀ x y, S x y = S y x) (hunit : ∀ x, S x N.unit = d x)
    (hsq : ∀ x y, ∑ z, S x z * S z y = if x = dual y then D else 0)
    (hVerlinde : ∀ i j y, (S i y / d y) * (S j y / d y) =
      ∑ k, (N.coeff i j k : ℂ) * (S k y / d y)) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm ι, ∀ (σ : ℂ ≃+* ℂ) i j,
      σ (S i j / d j) = S i (act σ j) / d (act σ j) := by
  let columns : ι → Character N := fun j => {
    value := fun i => S i j / d j
    unit_eq := by rw [hsym, hunit]; exact div_self (hd j)
    mul_eq := fun i k => hVerlinde i k j }
  have hlin : LinearIndependent ℂ (fun j => (columns j).value) :=
    normalized_columns_linearIndependent S dual d D hd hD hsym hsq
  let e : ι ≃ Character N := Equiv.ofBijective columns (characters_bijective N columns hlin)
  refine ⟨Character.galoisLabel e, ?_⟩
  intro σ i j
  exact (Character.galoisLabel_character e σ j i).symm

/-- Once S-square and Verlinde are proved categorically, the corresponding
normalized S-columns carry the genuine action of all complex automorphisms. -/
theorem categoricalS_galois_action (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (dual : Fin (rank C) → Fin (rank C))
    (hD : globalDimension C ≠ 0)
    (hsq : ∀ x y, ∑ z, categoricalS C p x z * categoricalS C p z y =
      if x = dual y then globalDimension C else 0)
    (hVerlinde : ∀ i j y,
      (categoricalS C p i y / simpleDimension C p y) *
        (categoricalS C p j y / simpleDimension C p y) =
      ∑ k, (fusionCoeff C i j k : ℂ) * (categoricalS C p k y / simpleDimension C p y)) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm (Fin (rank C)), ∀ (σ : ℂ ≃+* ℂ) i j,
      σ (categoricalS C p i j / simpleDimension C p j) =
        categoricalS C p i (act σ j) / simpleDimension C p (act σ j) := by
  let N : FusionRules (Fin (rank C)) := ⟨unitIndex C, fusionCoeff C⟩
  exact exists_galoisLabel_of_verlinde N (categoricalS C p) dual (simpleDimension C p)
    (globalDimension C) (simpleDimension_ne_zero C p) hD (categoricalS_symmetric C p) (categoricalS_unit C p) hsq hVerlinde


/-- Proposition 2.1 from the numerical S identities and the character equation,
with no modular-data hypothesis bundle. -/
theorem galois_unit_properties {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι) (S : Matrix ι ι ℂ) (dual : ι → ι) (d : ι → ℂ) (D : ℂ)
    (hd : ∀ y, d y ≠ 0) (hD : D ≠ 0) (hu : d u = 1)
    (hglobal : D = ∑ x, d x ^ 2) (hsym : ∀ x y, S x y = S y x)
    (hunit : ∀ x, S x u = d x)
    (hsq : ∀ x y, ∑ z, S x z * S z y = if x = dual y then D else 0)
    (σ : ℂ ≃+* ℂ) (y : ι)
    (hchar : ∀ x, σ (S x u / d u) = S x y / d y) :
    (∀ x, S x y = d y * σ (d x)) ∧ y = dual y ∧ σ D = D / d y ^ 2 := by
  have hcol (x : ι) : S x y = d y * σ (d x) := by
    have hh := hchar x
    rw [hunit, hu, div_one] at hh
    exact (div_eq_iff (hd y)).mp hh.symm |>.trans (mul_comm _ _)
  have hsquare : d y ^ 2 * σ D = if y = dual y then D else 0 := by
    calc
      d y ^ 2 * σ D = ∑ x, (d y * σ (d x)) ^ 2 := by
        rw [hglobal, map_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [map_pow, mul_pow]
      _ = ∑ x, S x y ^ 2 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hcol]
      _ = ∑ x, S y x * S x y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hsym y x, pow_two]
      _ = _ := hsq y y
  have hself : y = dual y := by
    by_contra hn
    rw [ite_eq_right hn] at hsquare
    exact mul_ne_zero (pow_ne_zero 2 (hd y))
      (by simpa using σ.injective.ne hD) hsquare
  refine ⟨hcol, hself, ?_⟩
  apply (eq_div_iff (pow_ne_zero 2 (hd y))).mpr
  rw [mul_comm, hsquare, ite_eq_left hself]

end PropertyF.Ground.Modular
