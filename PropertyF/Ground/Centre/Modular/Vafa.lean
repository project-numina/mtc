module
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import PropertyF.Ground.CentreCabling.TwistFinite
public import PropertyF.Ground.CentreInduction.Representatives
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Fusion.ObjectDimension
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import PropertyF.Ground.Modular.SSquare
public import PropertyF.Ground.Modular.Verlinde

/-!
# Vafa finiteness for centre modularity

Determinant relations and tensor decompositions imply finiteness of mixed monodromy.
-/

@[expose] public noncomputable section

section
open scoped BigOperators
namespace PropertyF.Ground.CentreModular
universe u v w
variable (C : BraidedFusionCategory.{v,u})

/-- A regular dimension vector is an eigenvector for every fusion operator. -/
abbrev IsRegularFusionVector {ι K : Type*} [Fintype ι] [Semiring K]
    (N : ι → ι → ι → K) (d : ι → K) : Prop :=
  ∀ i k, (∑ j, d j * N i j k) = d i * d k

/-- A derivation of fusion coefficients relative to a dimension character. -/
abbrev IsFusionDerivation {ι K M : Type*} [Fintype ι] [Semiring K] [AddCommMonoid M] [Module K M]
    (N : ι → ι → ι → K) (d : ι → K) (b : ι → M) : Prop :=
  ∀ i j, (∑ k, N i j k • b k) = d j • b i + d i • b j

section
variable {ι K M : Type*} [Fintype ι] [Field K] [AddCommGroup M] [Module K M]

/-- A derivation vanishes when a regular eigenvector has nonzero squared norm. -/
theorem derivation_vanishes_of_regular_eigenvector (N : ι → ι → ι → K) (d : ι → K)
    (hreg : IsRegularFusionVector N d) (hD : (∑ j, d j ^ 2) ≠ 0)
    (b : ι → M) (hderiv : IsFusionDerivation N d b) :
    ∀ i, b i = 0 := by
  classical
  intro i
  let R : M := ∑ j, d j • b j
  have hsum : (∑ j, d j • ∑ k, N i j k • b k) = d i • R := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hreg, mul_smul]
    rw [show R = ∑ j, d j • b j from rfl, Finset.smul_sum]
  exact (smul_eq_zero.mp (add_right_cancel (b := d i • R) (by
    simpa only [hderiv, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul,
      R, pow_two, Finset.smul_sum, mul_comm, zero_add] using hsum))).resolve_left hD

end

/-- The Frobenius–Perron dimensions form a regular fusion eigenvector. -/
theorem fpSimple_regular (i k : Fin (rank C)) :
    (∑ j, fpSimple C j * (fusionCoeff C i j k : ℝ)) = fpSimple C i * fpSimple C k := by
  simp_rw [Modular.fusionCoeff_dual_adjoint C i]
  simpa only [mul_comm, fpSimple_dual] using (fpSimple_mul C (dualIndex C i) k).symm

/-- The FP regular-element cancellation at the heart of the determinant argument. -/
theorem regular_fusion_derivation_vanishes {M : Type w} {σ : Type*}
    [AddCommGroup M] [Module ℝ M] (B : Fin (rank C) → σ → M)
    (hhex : ∀ z, IsFusionDerivation (fun i j k ↦ (fusionCoeff C i j k : ℝ))
      (fpSimple C) (fun i ↦ B i z)) : ∀ i z, B i z = 0 :=
  fun i z ↦ derivation_vanishes_of_regular_eigenvector
    (fun i j k ↦ (fusionCoeff C i j k : ℝ)) (fpSimple C) (fpSimple_regular C)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C))) (fun i ↦ B i z)
    (hhex z) i

end PropertyF.Ground.CentreModular
end

section
open TensorProduct
namespace PropertyF.Ground.CentreModular

/-- A real vector space recording complex units up to torsion. -/
abbrev vafaUnitSpace : Type := ℝ ⊗[ℚ] (ℚ ⊗[ℤ] Additive ℂˣ)

/-- The class of a commutative-group element after rationalization and scalar extension. -/
def rationalUnitClass {K G : Type*} [CommSemiring K] [Algebra ℚ K] [CommGroup G] (z : G) :
    K ⊗[ℚ] (ℚ ⊗[ℤ] Additive G) := 1 ⊗ₜ[ℚ] (1 ⊗ₜ[ℤ] Additive.ofMul z)

/-- The image of a complex unit in the torsion-detecting vector space. -/
def vafaUnitClass (z : ℂˣ) : vafaUnitSpace := rationalUnitClass (K := ℝ) z

/-- A rationalized group element vanishes exactly when it has finite order. -/
theorem rationalUnitClass_eq_zero_iff {K G : Type*} [CommRing K] [Algebra ℚ K]
    [Module.FaithfullyFlat ℚ K] [CommGroup G] (z : G) :
    rationalUnitClass (K := K) z = 0 ↔ IsOfFinOrder z := by
  rw [rationalUnitClass, Module.FaithfullyFlat.one_tmul_eq_zero_iff]
  have hh := IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ (Additive G) 1) (m := Additive.ofMul z)
  change ((1 ⊗ₜ[ℤ] Additive.ofMul z : ℚ ⊗[ℤ] Additive G) = 0) ↔
    ∃ s : nonZeroDivisors ℤ, (s : ℤ) • Additive.ofMul z = 0 at hh
  rw [hh, isOfFinOrder_iff_zpow_eq_one]
  simp only [Subtype.exists, mem_nonZeroDivisors_iff_ne_zero, exists_prop]
  rfl

/-- Multiplication becomes addition after rationalization. -/
theorem rationalUnitClass_mul {K G : Type*} [CommSemiring K] [Algebra ℚ K] [CommGroup G]
    (z w : G) : rationalUnitClass (K := K) (z * w) =
      rationalUnitClass (K := K) z + rationalUnitClass (K := K) w := by
  simp [rationalUnitClass, TensorProduct.tmul_add]

/-- Natural powers become scalar multiples after rationalization. -/
theorem rationalUnitClass_pow {K G : Type*} [CommSemiring K] [Algebra ℚ K] [CommGroup G]
    (z : G) (n : ℕ) : rationalUnitClass (K := K) (z ^ n) = n • rationalUnitClass (K := K) z := by
  simp [rationalUnitClass]

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- An object automorphism acts linearly on maps from a fixed source. -/
def homAction {R : Type*} [CommSemiring R] {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D]
    (S X : D) (a : X ≅ X) : (S ⟶ X) ≃ₗ[R] (S ⟶ X) :=
  CategoryTheory.Linear.homCongr R (Iso.refl _) a

/-- The action on a Hom space respects composition of automorphisms. -/
theorem homAction_trans {R : Type*} [CommSemiring R] {D : Type u} [Category.{v} D]
    [Preadditive D] [Linear R D] {S X : D} (a b : X ≅ X) :
    homAction (R := R) S X (a ≪≫ b) = (homAction (R := R) S X a).trans (homAction (R := R) S X b) :=
  LinearEquiv.ext fun f ↦ by simp [homAction, CategoryTheory.Linear.homCongr_apply, Category.assoc]

/-- The actual FP-weighted categorical determinant of an automorphism,
valued in a real vector space that detects torsion. -/
def fpDeterminant {X : C.Obj} (a : X ≅ X) :
    vafaUnitSpace :=
  ∑ i, fpSimple C i • vafaUnitClass (homAction (R := ℂ) (simples C i) X a).det

/-- FP determinants turn composition into addition. -/
theorem fpDeterminant_trans {X : C.Obj}
    (a b : X ≅ X) : fpDeterminant C (a ≪≫ b) =
      fpDeterminant C a + fpDeterminant C b := by
  simp [fpDeterminant, homAction_trans, LinearEquiv.det_trans, vafaUnitClass, rationalUnitClass_mul,
    smul_add, Finset.sum_add_distrib, add_comm]

/-- The actual scalar automorphism of an object. -/
def scalarIso {R : Type*} [CommSemiring R] {D : Type u} [Category.{v} D]
    [Preadditive D] [Linear R D] (X : D) (z : Rˣ) : X ≅ X where
  hom := (z : R) • 𝟙 X
  inv := ((z⁻¹ : Rˣ) : R) • 𝟙 X
  hom_inv_id := by simp [Linear.comp_smul, smul_smul]
  inv_hom_id := by simp [Linear.comp_smul, smul_smul]

/-- A scalar linear equivalence has determinant equal to the scalar's dimension power. -/
theorem linearEquiv_det_of_scalar {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) (z : Kˣ) (h : e.toLinearMap = (z : K) • LinearMap.id) :
    e.det = z ^ Module.finrank K V := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det e.toLinearMap = (z : K) ^ _
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one]

/-- On a scalar map, each Hom-space determinant is the corresponding power. -/
theorem homAction_det_scalar {R : Type*} [Field R] {D : Type u} [Category.{v} D]
    [Preadditive D] [Linear R D] {S X : D} (z : Rˣ) :
    (homAction (R := R) S X (scalarIso X z)).det = z ^ Module.finrank R (S ⟶ X) :=
  linearEquiv_det_of_scalar _ z (by
    ext f
    simp [homAction, scalarIso, CategoryTheory.Linear.homCongr_apply])

/-- A scalar automorphism has FP determinant equal to its unit class weighted
by the actual FP dimension of the object. -/
theorem fpDeterminant_scalar (X : C.Obj) (z : ℂˣ) :
    fpDeterminant C (scalarIso X z) = fpDimension C X • vafaUnitClass z := by
  simp only [fpDeterminant, fpDimension, homAction_det_scalar, vafaUnitClass, rationalUnitClass_pow,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Finset.sum_smul, mul_comm]

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Tensoring an automorphism scales its FP determinant by the tensor factor's dimension. -/
abbrev HasTensorDeterminant (X : C.Obj) {Y : C.Obj} (a : Y ≅ Y) : Prop :=
  fpDeterminant C (Iso.refl X ⊗ᵢ a) = fpDimension C X • fpDeterminant C a

/-- FP determinants are invariant under actual categorical conjugation. -/
theorem fpDeterminant_conjugate
    {X Y : C.Obj} (e : X ≅ Y) (a : X ≅ X) :
    fpDeterminant C (e.symm ≪≫ a ≪≫ e) = fpDeterminant C a := by
  unfold fpDeterminant
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  let E := CategoryTheory.Linear.homCongr ℂ (Iso.refl (simples C i)) e
  have h : homAction (R := ℂ) (simples C i) Y (e.symm ≪≫ a ≪≫ e) =
      ((E.symm.trans (homAction (R := ℂ) (simples C i) X a)).trans E) := by
    ext f
    simp [homAction, E, CategoryTheory.Linear.homCongr_apply,
      CategoryTheory.Linear.homCongr_symm_apply, Category.assoc]
  rw [h, LinearEquiv.det_conj]

/-- Conjugation followed by composition adds the corresponding FP determinants. -/
theorem fpDeterminant_conjugate_trans {X Y : C.Obj} (e : X ≅ Y)
    (a : Y ≅ Y) (b : X ≅ X) :
    fpDeterminant C (e ≪≫ a ≪≫ e.symm ≪≫ b) =
      fpDeterminant C a + fpDeterminant C b := by
  rw [← Iso.trans_assoc, ← Iso.trans_assoc, fpDeterminant_trans, Iso.trans_assoc]
  congr 1
  simpa only [Iso.symm_symm_eq] using fpDeterminant_conjugate C e.symm a

/-- Tensoring a scalar automorphism preserves the scalar action. -/
theorem tensor_scalarIso {R : Type*} [CommSemiring R] {D : Type u}
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] [Linear R D]
    [MonoidalPreadditive D] [MonoidalLinear R D] (X Y : D) (z : Rˣ) :
    Iso.refl X ⊗ᵢ scalarIso Y z = scalarIso (X ⊗ Y) z :=
  Iso.ext (by simp [scalarIso, tensorHom_def])

/-- The tensor-product determinant rule when the second automorphism is scalar. -/
theorem fpDeterminant_tensor_scalar
    (X Y : C.Obj) (z : ℂˣ) :
    HasTensorDeterminant C X (scalarIso Y z) := by
  dsimp only [HasTensorDeterminant]
  rw [tensor_scalarIso, fpDeterminant_scalar, fpDeterminant_scalar, fpDimension_tensor, mul_smul]

end PropertyF.Ground.CentreModular
end

section
open scoped BigOperators
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Weighted group classes satisfy the fusion balance relation. -/
abbrev HasWeightedTwistBalance {ι K G : Type*} [Fintype ι] [Field K] [Algebra ℚ K]
    [CommGroup G] (N : ι → ι → ι → K) (d : ι → K) (t : ι → G) : Prop :=
  ∀ i j, (∑ k, N i j k • (d k • rationalUnitClass (K := K) (t k))) =
    (d i * d j) • (rationalUnitClass (K := K) (t i) + rationalUnitClass (K := K) (t j))

/-- A nondegenerate regular dimension character makes balanced twists torsion. -/
theorem finite_order_of_weighted_twist_balance {ι K G : Type*} [Fintype ι] [Field K]
    [Algebra ℚ K] [Module.FaithfullyFlat ℚ K] [CommGroup G]
    (N : ι → ι → ι → K) (d : ι → K)
    (hreg : IsRegularFusionVector N d) (hD : (∑ j, d j ^ 2) ≠ 0)
    (hd : ∀ i, d i ≠ 0) (t : ι → G) (hbalance : HasWeightedTwistBalance N d t) :
    ∀ i, IsOfFinOrder (t i) := by
  have hderiv : IsFusionDerivation N d (fun i ↦ d i • rationalUnitClass (K := K) (t i)) := by
    intro i j
    simpa only [smul_add, smul_smul, mul_comm] using hbalance i j
  intro i
  apply (rationalUnitClass_eq_zero_iff (K := K) _).mp
  exact (smul_eq_zero.mp (derivation_vanishes_of_regular_eigenvector N d hreg hD _ hderiv i)).resolve_left (hd i)

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable {η : 𝟭 C.Obj ≅ 𝟭 C.Obj} {t : Fin (rank C) → ℂˣ}

/-- The values of a natural automorphism on the chosen simple objects are scalar. -/
abbrev HasSimpleScalars (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (t : Fin (rank C) → ℂˣ) : Prop :=
  ∀ i, (η.app (simples C i)).hom = (t i : ℂ) • 𝟙 (simples C i)

/-- A natural automorphism acts on a Hom space by its scalar on the source. -/
theorem homAction_natural_scalar {R : Type*} [CommSemiring R] {D : Type u}
    [Category.{v} D] [Preadditive D] [Linear R D] (η : 𝟭 D ≅ 𝟭 D) {S X : D}
    (z : R) (hz : (η.app S).hom = z • 𝟙 S) :
    (homAction (R := R) S X (η.app X)).toLinearMap = z • LinearMap.id := by
  ext f
  simpa [homAction, CategoryTheory.Linear.homCongr_apply,
    show η.hom.app S = z • 𝟙 S from hz] using η.hom.naturality f

/-- The actual FP determinant of a natural automorphism is the sum of its
simple scalar classes, weighted by FP dimensions and Hom multiplicities. -/
theorem fpDeterminant_natural
    (ht : HasSimpleScalars C η t)
    (X : C.Obj) :
    fpDeterminant C (η.app X) = ∑ i,
      (Module.finrank ℂ (simples C i ⟶ X) : ℝ) • (fpSimple C i • vafaUnitClass (t i)) := by
  simp only [fpDeterminant, vafaUnitClass]
  apply Finset.sum_congr rfl
  intro i _
  change fpSimple C i • rationalUnitClass (homAction (R := ℂ) (simples C i) X (η.app X)).det = _
  rw [linearEquiv_det_of_scalar _ (t i) (homAction_natural_scalar η (t i : ℂ) (ht i)),
    rationalUnitClass_pow, ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [smul_smul, mul_comm]

/-- A natural automorphism whose actual FP determinant satisfies the
multiplicative balance on simple tensor products has finite-order simple
scalars. The displayed determinant identity remains an explicit premise. -/
theorem natural_scalars_finite_of_fpDeterminant_balance
    (ht : HasSimpleScalars C η t)
    (hdet : ∀ i j, fpDeterminant C (η.app (simples C i ⊗ simples C j)) =
        fpDimension C (simples C i ⊗ simples C j) •
          (vafaUnitClass (t i) + vafaUnitClass (t j))) :
    ∀ i, IsOfFinOrder (t i) :=
  finite_order_of_weighted_twist_balance (fun i j k ↦ (fusionCoeff C i j k : ℝ)) (fpSimple C)
    (fpSimple_regular C) (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)))
    (fun i ↦ ne_of_gt (fpSimple_pos C i)) t fun i j ↦ by
      simpa only [vafaUnitClass, fpDeterminant_natural C ht, fpDimension_tensor,
        fpDimension_simple, fusionCoeff] using hdet i j

section
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

/-- The actual double braiding as an automorphism. -/
def monodromyIso (X Y : D) : X ⊗ Y ≅ X ⊗ Y :=
  (β_ X Y) ≪≫ (β_ Y X)

/-- For a fixed first strand, double braiding is a natural automorphism of
the actual tensor-left functor. -/
def monodromyNaturalIso (Z : D) :
    tensorLeft Z ≅ tensorLeft Z :=
  NatIso.ofComponents (fun W => monodromyIso Z W) (by
    intro X Y f
    change (Z ◁ f) ≫ ((β_ Z Y).hom ≫ (β_ Y Z).hom) =
      ((β_ Z X).hom ≫ (β_ X Z).hom) ≫ (Z ◁ f)
    simp only [← id_tensorHom, Category.assoc]
    rw [braiding_naturality_assoc, braiding_naturality])

/-- The categorical double-braiding hexagon, as a product of conjugate
monodromy automorphisms. -/
theorem monodromy_hexagon_iso (Z X Y : D) :
    let e := ((β_ Z X) ⊗ᵢ Iso.refl Y) ≪≫ (α_ X Z Y)
    (α_ Z X Y) ≪≫ monodromyIso Z (X ⊗ Y) ≪≫ (α_ Z X Y).symm =
      e ≪≫ (Iso.refl X ⊗ᵢ monodromyIso Z Y) ≪≫ e.symm ≪≫
        (monodromyIso Z X ⊗ᵢ Iso.refl Y) :=
  Iso.ext (by simp [monodromyIso, tensorIso_hom, tensorHom_id, id_tensorHom, Category.assoc,
    ← comp_whiskerRight])

end

/-- The FP determinant of the double braiding between two objects. -/
abbrev monodromyDet (Z W : C.Obj) : vafaUnitSpace :=
  fpDeterminant C (monodromyIso Z W)

/-- The natural automorphism satisfies the balancing equation on simple pairs. -/
abbrev HasSimpleBalance (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (t : Fin (rank C) → ℂˣ) : Prop :=
  ∀ i j, η.app (simples C i ⊗ simples C j) =
    scalarIso (simples C i ⊗ simples C j) (t i * t j) ≪≫
      monodromyIso (simples C i) (simples C j)

/-- Vanishing FP determinants of simple double braidings and an actual
balancing equation force finite order of every simple twist scalar. Both
categorical premises are explicit. -/
theorem natural_scalars_finite_of_monodromy_determinant
    (ht : HasSimpleScalars C η t)
    (hbalance : HasSimpleBalance C η t)
    (hmon : ∀ i j, monodromyDet C (simples C i) (simples C j) = 0) :
    ∀ i, IsOfFinOrder (t i) :=
  natural_scalars_finite_of_fpDeterminant_balance C ht fun i j ↦ by
    dsimp only [monodromyDet] at hmon
    rw [hbalance, fpDeterminant_trans, hmon, add_zero,
      fpDeterminant_scalar C (simples C i ⊗ simples C j), vafaUnitClass, rationalUnitClass_mul]
    simp only [vafaUnitClass]

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Hom into a binary biproduct is the product of the two Hom spaces. -/
def homBiprodLinearEquiv {R : Type*} [CommSemiring R] {D : Type u}
    [Category.{v} D] [Preadditive D] [Linear R D] [HasBinaryBiproducts D]
    (S X Y : D) : (S ⟶ X ⊞ Y) ≃ₗ[R] ((S ⟶ X) × (S ⟶ Y)) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  invFun f := f.1 ≫ biprod.inl + f.2 ≫ biprod.inr
  left_inv f := by ext <;> simp [Preadditive.add_comp, Category.assoc]
  right_inv f := by ext <;> simp [Preadditive.add_comp, Category.assoc]
  map_add' f g := by ext <;> simp
  map_smul' r f := by ext <;> simp

/-- The determinant of the Hom action factors over a binary biproduct. -/
theorem homAction_det_biprod {R : Type*} [Field R] {D : Type u} [Category.{v} D] [Preadditive D]
    [Linear R D] [HasBinaryBiproducts D] {S X Y : D}
    [FiniteDimensional R (S ⟶ X)] [FiniteDimensional R (S ⟶ Y)]
    (a : X ≅ X) (b : Y ≅ Y) :
    (homAction (R := R) S (X ⊞ Y) (biprod.mapIso a b)).det =
      (homAction (R := R) S X a).det * (homAction (R := R) S Y b).det :=
  let E := homBiprodLinearEquiv (R := R) S X Y
  let A := homAction (R := R) S (X ⊞ Y) (biprod.mapIso a b)
  let L := homAction (R := R) S X a
  let right := homAction (R := R) S Y b
  have h : (E.symm.trans A).trans E = L.prodCongr right := by
    ext f <;> simp [E, A, L, right, homBiprodLinearEquiv, homAction,
      CategoryTheory.Linear.homCongr_apply, Category.assoc]
  Units.ext (by
    rw [← LinearEquiv.det_conj A E, h, LinearEquiv.coe_det]
    change LinearMap.det (L.toLinearMap.prodMap right.toLinearMap) = _
    rw [LinearMap.det_prodMap, Units.val_mul, LinearEquiv.coe_det, LinearEquiv.coe_det])

/-- FP determinants are additive over direct sums of automorphisms. -/
theorem fpDeterminant_biprod
    {X Y : C.Obj} (a : X ≅ X) (b : Y ≅ Y) :
    fpDeterminant C (biprod.mapIso a b) =
      fpDeterminant C a + fpDeterminant C b := by
  let : ∀ A B : C.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  unfold fpDeterminant
  simp_rw [homAction_det_biprod, vafaUnitClass, rationalUnitClass_mul, smul_add]
  rw [Finset.sum_add_distrib]

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts
local instance (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    PreservesBinaryBiproducts (tensorLeft X) := preservesBinaryBiproducts_of_preservesBiproducts _

/-- Tensoring a biproduct automorphism respects the canonical biproduct comparison. -/
theorem tensor_biprod_mapIso {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [Preadditive D] [HasBinaryBiproducts D]
    (X : D) [(tensorLeft X).PreservesZeroMorphisms] {Y Z : D}
    [PreservesBinaryBiproducts (tensorLeft X)] (a : Y ≅ Y) (b : Z ≅ Z) :
    Iso.refl X ⊗ᵢ biprod.mapIso a b = (Functor.mapBiprod (tensorLeft X) Y Z) ≪≫
      biprod.mapIso (Iso.refl X ⊗ᵢ a) (Iso.refl X ⊗ᵢ b) ≪≫
        (Functor.mapBiprod (tensorLeft X) Y Z).symm :=
  let e := Functor.mapBiprod (tensorLeft X) Y Z
  let A := biprod.mapIso (Iso.refl X ⊗ᵢ a) (Iso.refl X ⊗ᵢ b)
  show Iso.refl X ⊗ᵢ biprod.mapIso a b = e ≪≫ A ≪≫ e.symm from
    Iso.ext ((cancel_epi e.inv).1 (by
      have hleft : biprod.inl ≫ e.inv = X ◁ biprod.inl := by
        rw [Functor.mapBiprod_inv, biprod.inl_desc]
        rfl
      have hright : biprod.inr ≫ e.inv = X ◁ biprod.inr := by
        rw [Functor.mapBiprod_inv, biprod.inr_desc]
        rfl
      apply biprod.hom_ext' <;>
        simp only [Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc] <;>
        simp only [← Category.assoc, hleft, hright, tensorIso_hom, Iso.refl_hom, id_tensorHom,
          ← whiskerLeft_comp] <;>
        simp only [A, biprod.mapIso_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom] <;>
        simp only [biprod.inl_map, biprod.inr_map, whiskerLeft_comp, Category.assoc]
      · exact (congrArg (fun f => (X ◁ a.hom) ≫ f) hleft).symm
      · exact (congrArg (fun f => (X ◁ b.hom) ≫ f) hright).symm))

/-- The tensor determinant identity is closed under binary direct sums. -/
theorem fpDeterminant_tensor_biprod
    (X : C.Obj) {Y Z : C.Obj} (a : Y ≅ Y) (b : Z ≅ Z)
    (ha : HasTensorDeterminant C X a) (hb : HasTensorDeterminant C X b) :
    HasTensorDeterminant C X (biprod.mapIso a b) := by
  dsimp only [HasTensorDeterminant] at ha hb ⊢
  let e := Functor.mapBiprod (tensorLeft X) Y Z
  let A := biprod.mapIso (Iso.refl X ⊗ᵢ a) (Iso.refl X ⊗ᵢ b)
  rw [tensor_biprod_mapIso]
  have hd := fpDeterminant_conjugate C e.symm A
  change fpDeterminant C (e ≪≫ A ≪≫ e.symm) = fpDeterminant C A at hd
  rw [hd, fpDeterminant_biprod, fpDeterminant_biprod, ha, hb, smul_add]

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every base object is a finite iterated binary sum of simple objects. -/
theorem base_finite_simple_sum (X : C.Obj) :
    CentreInduction.FiniteSimpleSum C.Obj X := by
  let (A B : C.Obj) : FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite _ _
  let (W : C.Obj) : Injective W := object_injective C W
  apply CentreInduction.finiteSimpleSum_of_injective (k := ℂ) ?_ X
  intro W hW
  obtain ⟨i, hi⟩ := exists_positive_multiplicity C hW
  let : Simple (simples C i) := simples_simple C i
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hi
  exact ⟨simples C i, f, simples_simple C i, mono_of_nonzero_from_simple hf⟩

/-- Identity automorphisms have zero FP determinant. -/
theorem fpDeterminant_refl (X : C.Obj) :
    fpDeterminant C (Iso.refl X) = 0 := by
  simpa using (fpDeterminant_trans C (Iso.refl X) (Iso.refl X))

/-- The tensor determinant rule holds on any simple object. -/
theorem fpDeterminant_tensor_of_simple
    (X S : C.Obj) [Simple S] (a : S ≅ S) :
    HasTensorDeterminant C X a := by
  let : FiniteDimensional ℂ (S ⟶ S) := IsFusionCategory.hom_finite _ _
  obtain ⟨z, hz⟩ := endomorphism_simple_eq_smul_id ℂ a.hom
  have hne : z ≠ 0 := fun h ↦ id_nonzero S (by simpa [← hz, h] using a.hom_inv_id.symm)
  rw [show a = scalarIso S (Units.mk0 z hne) from Iso.ext hz.symm]
  exact fpDeterminant_tensor_scalar C X S _

/-- Components of a natural automorphism of a functor are conjugate along
isomorphisms in the source. -/
theorem functor_natural_app_conjugate {D : Type u} {E : Type*}
    [Category.{v} D] [Category E] (F : D ⥤ E) (η : F ≅ F) {X Y : D} (e : X ≅ Y) :
    η.app X = F.mapIso e ≪≫ η.app Y ≪≫ (F.mapIso e).symm :=
  Iso.ext ((cancel_mono (F.mapIso e).hom).1 (by simp))

/-- An additive functor's natural automorphism is block diagonal on a binary
biproduct under its canonical comparison isomorphism. -/
theorem functor_natural_app_biprod {D : Type u} {E : Type*}
    [Category.{v} D] [Category E] [Preadditive D] [Preadditive E]
    [HasBinaryBiproducts D] [HasBinaryBiproducts E]
    (F : D ⥤ E) [F.Additive] [PreservesBinaryBiproducts F] (η : F ≅ F) (X Y : D) :
    η.app (X ⊞ Y) = F.mapBiprod X Y ≪≫
      biprod.mapIso (η.app X) (η.app Y) ≪≫ (F.mapBiprod X Y).symm :=
  Iso.ext ((cancel_mono (F.mapBiprod X Y).hom).1 (by
    change (η.app (X ⊞ Y)).hom ≫ (F.mapBiprod X Y).hom =
      ((F.mapBiprod X Y).hom ≫ (biprod.mapIso (η.app X) (η.app Y)).hom ≫
        (F.mapBiprod X Y).inv) ≫ (F.mapBiprod X Y).hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext
    · simpa only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst, biprod.lift_fst_assoc,
        biprod.mapIso_hom, biprod.map_fst, Iso.app_hom] using
        (η.hom.naturality (biprod.fst : X ⊞ Y ⟶ X)).symm
    · simpa only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd, biprod.lift_snd_assoc,
        biprod.mapIso_hom, biprod.map_snd, Iso.app_hom] using
        (η.hom.naturality (biprod.snd : X ⊞ Y ⟶ Y)).symm))

/-- Tensoring a conjugated automorphism conjugates its tensor extension. -/
theorem tensor_conjugate_iso {D : Type u} [Category.{v} D] [MonoidalCategory D]
    (X : D) {Y Z : D} (e : Y ≅ Z) (a : Z ≅ Z) :
    (Iso.refl X ⊗ᵢ (e ≪≫ a ≪≫ e.symm)) =
      (Iso.refl X ⊗ᵢ e) ≪≫ (Iso.refl X ⊗ᵢ a) ≪≫ (Iso.refl X ⊗ᵢ e).symm :=
  Iso.ext (by simp [tensorIso_hom, tensorHom_def, whiskerLeft_comp])

variable (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (X : C.Obj)

include η X in
/-- The tensor determinant equation for a natural automorphism at two objects. -/
abbrev HasTensorDeterminantRule (Y : C.Obj) : Prop :=
  HasTensorDeterminant C X (η.app Y)

/-- The tensor determinant equation is invariant under isomorphism in its second object. -/
theorem tensorDeterminantRule_iff_of_iso {Y Z : C.Obj} (e : Y ≅ Z) :
    HasTensorDeterminantRule C η X Y ↔ HasTensorDeterminantRule C η X Z := by
  have hη : η.app Y = e ≪≫ η.app Z ≪≫ e.symm := by
    simpa only [show (𝟭 C.Obj).mapIso e = e from Iso.ext rfl] using
      functor_natural_app_conjugate (𝟭 C.Obj) η e
  have hl := fpDeterminant_conjugate C (Iso.refl X ⊗ᵢ e).symm
    (Iso.refl X ⊗ᵢ η.app Z)
  have hr := fpDeterminant_conjugate C e.symm (η.app Z)
  simp only [Iso.symm_symm_eq] at hl hr
  change (fpDeterminant C (Iso.refl X ⊗ᵢ η.app Y) =
    fpDimension C X • fpDeterminant C (η.app Y)) ↔ _
  rw [hη, tensor_conjugate_iso, hl, hr]

/-- The categorical FP determinant tensor rule holds for components of
any natural automorphism, by semisimplicity. -/
theorem fpDeterminant_tensor_natural (Y : C.Obj) : HasTensorDeterminantRule C η X Y := by
  change fpDeterminant C (Iso.refl X ⊗ᵢ η.app Y) =
    fpDimension C X • fpDeterminant C (η.app Y)
  induction base_finite_simple_sum C Y with
  | @zero W hz =>
    have hη : η.app W = Iso.refl W := Iso.ext (hz.eq_of_src _ _)
    have ht : Iso.refl X ⊗ᵢ Iso.refl W = Iso.refl (X ⊗ W) := Iso.ext (by simp)
    simp only [hη, ht, fpDeterminant_refl C (X ⊗ W), fpDeterminant_refl C W, smul_zero]
  | @cons Y S K hs hk he ih =>
    obtain ⟨e⟩ := he
    let : Simple S := hs
    let : PreservesBinaryBiproducts (𝟭 C.Obj) := preservesBinaryBiproducts_of_preservesBiproducts _
    have hsum' : η.app (S ⊞ K) = biprod.mapIso (η.app S) (η.app K) := by
      simpa [show (𝟭 C.Obj).mapBiprod S K = Iso.refl (S ⊞ K) from
        Iso.ext (by apply biprod.hom_ext <;> simp)] using
          functor_natural_app_biprod (𝟭 C.Obj) η S K
    apply (tensorDeterminantRule_iff_of_iso C η X e).mpr
    change HasTensorDeterminant C X (η.app (S ⊞ K))
    rw [hsum']
    exact fpDeterminant_tensor_biprod C X (η.app S) (η.app K)
      (fpDeterminant_tensor_of_simple C X S (η.app S)) ih

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u w
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The multiplicity expansion of a simple object has a single nonzero term. -/
theorem simple_multiplicity_expansion {M : Type w} [AddCommGroup M] [Module ℝ M]
    (f : C.Obj → M) (hiso : ∀ {X Y : C.Obj}, (X ≅ Y) → f X = f Y)
    (S : C.Obj) [Simple S] :
    f S = ∑ i, (Module.finrank ℂ (simples C i ⟶ S) : ℝ) • f (simples C i) := by
  classical
  let : ∀ A B : C.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  obtain ⟨j, ⟨e⟩⟩ := exists_simple_iso C S
  have hr (i : Fin (rank C)) : Module.finrank ℂ (simples C i ⟶ S) =
      Module.finrank ℂ (simples C i ⟶ simples C j) :=
    (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq
  simpa [hr, finrank_simples_hom] using hiso e

/-- Any isomorphism-invariant additive object function is determined by
its values on simples and the actual Hom-space multiplicities. -/
theorem additive_object_function_decomposition {M : Type w} [AddCommGroup M] [Module ℝ M]
    (f : C.Obj → M)
    (hiso : ∀ {X Y : C.Obj}, (X ≅ Y) → f X = f Y)
    (hzero : ∀ X, IsZero X → f X = 0)
    (hadd : ∀ X Y, f (X ⊞ Y) = f X + f Y)
    (X : C.Obj) :
    f X = ∑ i, (Module.finrank ℂ (simples C i ⟶ X) : ℝ) • f (simples C i) := by
  classical
  let : ∀ A B : C.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  have h := base_finite_simple_sum C X
  induction h with
  | @zero W hz =>
    rw [hzero W hz]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro i _
    have : Subsingleton (simples C i ⟶ W) := ⟨fun a b => hz.eq_of_tgt a b⟩
    simp [Module.finrank_zero_of_subsingleton]
  | @cons W S K hs hk he ih =>
    obtain ⟨e⟩ := he
    let : Simple S := hs
    rw [hiso e, hadd, simple_multiplicity_expansion C f hiso S, ih,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hdim : Module.finrank ℂ (simples C i ⟶ W) =
        Module.finrank ℂ (simples C i ⟶ S) + Module.finrank ℂ (simples C i ⟶ K) := by
      exact ((CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq).trans
        ((homBiprodLinearEquiv (simples C i) S K).finrank_eq.trans Module.finrank_prod)
    rw [hdim, Nat.cast_add, add_smul]

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The FP determinant of a natural automorphism of an additive functor
expands over the simple summands of the source object. -/
theorem fpDeterminant_functor_natural_decomposition
    (F : C.Obj ⥤ C.Obj) [F.Additive] (η : F ≅ F) (X : C.Obj) :
    fpDeterminant C (η.app X) = ∑ i,
      (Module.finrank ℂ (simples C i ⟶ X) : ℝ) •
        fpDeterminant C (η.app (simples C i)) :=
  additive_object_function_decomposition C (fun X ↦ fpDeterminant C (η.app X))
    (fun {X Y} e ↦ by
      rw [functor_natural_app_conjugate F η e]
      exact fpDeterminant_conjugate C (F.mapIso e).symm (η.app Y))
    (fun X hX ↦ by
      rw [show η.app X = Iso.refl (F.obj X) from Iso.ext ((F.map_isZero hX).eq_of_src _ _),
        fpDeterminant_refl])
    (fun X Y ↦ by
      let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
      rw [functor_natural_app_biprod F η X Y]
      simpa only [Iso.symm_symm_eq, fpDeterminant_biprod] using
        fpDeterminant_conjugate C (F.mapBiprod X Y).symm
          (biprod.mapIso (η.app X) (η.app Y))) X

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable {η : 𝟭 C.Obj ≅ 𝟭 C.Obj} {t : Fin (rank C) → ℂˣ}

/-- The FP tensor determinant rule holds for scalar multiples of a component
of an arbitrary natural automorphism. -/
theorem fpDeterminant_tensor_scalar_natural
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (X Y : C.Obj) (z : ℂˣ) :
    HasTensorDeterminant C X (scalarIso Y z ≪≫ η.app Y) := by
  dsimp only [HasTensorDeterminant]
  have h : (Iso.refl X ⊗ᵢ (scalarIso Y z ≪≫ η.app Y)) =
      (Iso.refl X ⊗ᵢ scalarIso Y z) ≪≫ (Iso.refl X ⊗ᵢ η.app Y) :=
    Iso.ext (by simp [tensorIso_hom, tensorHom_def, whiskerLeft_comp])
  have hn : fpDeterminant C (Iso.refl X ⊗ᵢ η.app Y) =
      fpDimension C X • fpDeterminant C (η.app Y) := fpDeterminant_tensor_natural C η X Y
  rw [h, fpDeterminant_trans, fpDeterminant_trans, fpDeterminant_tensor_scalar, hn, smul_add]

variable (hbalance : HasSimpleBalance C η t)

include hbalance in
/-- Balancing identifies the mixed double braiding of two simples with a
scalar multiple of the twist component. -/
theorem monodromy_simple_eq_scalar_natural (i j : Fin (rank C)) :
    monodromyIso (simples C i) (simples C j) =
      scalarIso (simples C i ⊗ simples C j) (t i * t j)⁻¹ ≪≫
        η.app (simples C i ⊗ simples C j) := by
  rw [hbalance, show scalarIso (simples C i ⊗ simples C j) (t i * t j)⁻¹ =
    (scalarIso (simples C i ⊗ simples C j) (t i * t j)).symm from Iso.ext rfl,
    Iso.symm_self_id_assoc]

include hbalance in
/-- Under the explicit balancing equation, the tensor determinant rule holds
for every simple mixed monodromy. -/
theorem fpDeterminant_tensor_simple_monodromy
    (X : C.Obj) (i j : Fin (rank C)) :
    HasTensorDeterminant C X (monodromyIso (simples C i) (simples C j)) :=
  (monodromy_simple_eq_scalar_natural C hbalance i j).symm ▸
    fpDeterminant_tensor_scalar_natural C η X _ _

/-- Braiding transports tensoring an automorphism on the right to tensoring it
on the left, preserving its categorical FP determinant. -/
theorem fpDeterminant_tensor_flip
    (X : C.Obj) {Y : C.Obj} (a : Y ≅ Y) :
    fpDeterminant C (a ⊗ᵢ Iso.refl X) =
      fpDeterminant C (Iso.refl X ⊗ᵢ a) := by
  let e := β_ Y X
  have h : a ⊗ᵢ Iso.refl X = e ≪≫ (Iso.refl X ⊗ᵢ a) ≪≫ e.symm := by
    apply Iso.ext
    apply (cancel_mono e.hom).1
    simp [e, tensorIso_hom]
  rw [h]
  exact fpDeterminant_conjugate C e.symm (Iso.refl X ⊗ᵢ a)

include hbalance in
/-- Under balancing, tensoring a simple mixed monodromy on either side
satisfies the FP determinant rule. -/
theorem fpDeterminant_simple_monodromy_tensor
    (X : C.Obj) (i j : Fin (rank C)) :
    fpDeterminant C (monodromyIso (simples C i) (simples C j) ⊗ᵢ Iso.refl X) =
      fpDimension C X • fpDeterminant C (monodromyIso (simples C i) (simples C j)) :=
  (fpDeterminant_tensor_flip C X (monodromyIso (simples C i) (simples C j))).trans
    (fpDeterminant_tensor_simple_monodromy C hbalance X i j)

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- The FP determinant of monodromy is additive in the second tensor factor. -/
theorem fpDeterminant_monodromy_tensor (Z X Y : C.Obj) :
    monodromyDet C Z (X ⊗ Y) =
      fpDeterminant C (Iso.refl X ⊗ᵢ monodromyIso Z Y) +
      fpDeterminant C (monodromyIso Z X ⊗ᵢ Iso.refl Y) := by
  have h := fpDeterminant_conjugate C (α_ Z X Y).symm (monodromyIso Z (X ⊗ Y))
  change fpDeterminant C ((α_ Z X Y) ≪≫ monodromyIso Z (X ⊗ Y) ≪≫ (α_ Z X Y).symm) = _ at h
  rw [monodromy_hexagon_iso, fpDeterminant_conjugate_trans] at h
  exact h.symm

/-- The actual FP determinant of the monodromy hexagon is the weighted sum
of the two simple monodromy determinants, under simple twist balancing. -/
theorem fpDeterminant_monodromy_hexagon
    {η : 𝟭 C.Obj ≅ 𝟭 C.Obj} {t : Fin (rank C) → ℂˣ}
    (hbalance : HasSimpleBalance C η t)
    (z i j : Fin (rank C)) :
    monodromyDet C (simples C z) (simples C i ⊗ simples C j) =
      fpSimple C i • monodromyDet C (simples C z) (simples C j) +
      fpSimple C j • monodromyDet C (simples C z) (simples C i) := by
  rw [fpDeterminant_monodromy_tensor C,
    fpDeterminant_tensor_simple_monodromy C hbalance,
    fpDeterminant_simple_monodromy_tensor C hbalance,
    fpDimension_simple, fpDimension_simple]

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable {η : 𝟭 C.Obj ≅ 𝟭 C.Obj} {t : Fin (rank C) → ℂˣ}

/-- FP determinant of a mixed monodromy expands over simple summands of
the second strand. -/
theorem fpDeterminant_monodromy_decomposition
    (Z W : C.Obj) :
    monodromyDet C Z W = ∑ i,
      (Module.finrank ℂ (simples C i ⟶ W) : ℝ) • monodromyDet C Z (simples C i) :=
  fpDeterminant_functor_natural_decomposition C (tensorLeft Z) (monodromyNaturalIso Z) W

variable (ht : HasSimpleScalars C η t) (hbalance : HasSimpleBalance C η t)

include hbalance in
/-- Under simple twist balancing, the FP determinant of every simple mixed
monodromy vanishes. -/
theorem fpDeterminant_simple_monodromy_eq_zero (z i : Fin (rank C)) :
    monodromyDet C (simples C z) (simples C i) = 0 := by
  let B : Fin (rank C) → Fin (rank C) → vafaUnitSpace := fun i z =>
    monodromyDet C (simples C z) (simples C i)
  refine regular_fusion_derivation_vanishes C B ?_ i z
  intro z i j
  have h := fpDeterminant_monodromy_hexagon C hbalance z i j
  rw [fpDeterminant_monodromy_decomposition] at h
  change (∑ k, (fusionCoeff C i j k : ℝ) • B k z) = _ at h
  simpa [B, add_comm] using h

include ht hbalance in
/-- Under an actual natural twist and its simple balancing equation,
the simple twist scalars have finite order. -/
theorem natural_scalars_finite_of_simple_balancing :
    ∀ i, IsOfFinOrder (t i) :=
  natural_scalars_finite_of_monodromy_determinant C ht hbalance fun i j ↦
    fpDeterminant_simple_monodromy_eq_zero C hbalance i j

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- The pivotal twist satisfies the balancing equation. -/
abbrev IsPivotalTwistBalanced (p : Dimensions.PivotalStructure (C := C.Obj)) : Prop :=
  ∀ X Y, Modular.doubleBraiding X Y ≫
    ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
      (Dimensions.pivotalBraidedTwist C p Y).hom) =
    (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom

/-- The pivotal twist acts by its chosen scalar on each simple object. -/
theorem pivotal_twist_has_simple_scalars (p : Dimensions.PivotalStructure (C := C.Obj)) :
    HasSimpleScalars C (Dimensions.pivotalBraidedTwistNaturalIso C p)
      (CentreCabling.pivotalTwistUnit C p) := fun i ↦
  letI : Simple (simples C i) := simples_simple C i
  Dimensions.pivotalBraidedTwist_simple C p (simples C i)

/-- Pivotal twist balancing gives the simple balancing equation. -/
theorem pivotal_twist_simple_balance (p : Dimensions.PivotalStructure (C := C.Obj))
    (hbalance : IsPivotalTwistBalanced C p) :
    HasSimpleBalance C (Dimensions.pivotalBraidedTwistNaturalIso C p)
      (CentreCabling.pivotalTwistUnit C p) := fun i j ↦ Iso.ext (by
    have h := hbalance (simples C i) (simples C j)
    change Modular.doubleBraiding _ _ ≫
      (((Dimensions.pivotalBraidedTwistNaturalIso C p).app (simples C i)).hom ⊗ₘ
        ((Dimensions.pivotalBraidedTwistNaturalIso C p).app (simples C j)).hom) =
        ((Dimensions.pivotalBraidedTwistNaturalIso C p).app (simples C i ⊗ simples C j)).hom at h
    rw [pivotal_twist_has_simple_scalars C p i, pivotal_twist_has_simple_scalars C p j] at h
    simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight,
      Linear.smul_comp, Linear.comp_smul, smul_smul] at h
    simpa [scalarIso, monodromyIso, Modular.doubleBraiding, Category.assoc,
      Linear.smul_comp, mul_comm] using h.symm)

/-- Pivotal twist scalars have finite order whenever its actual balancing law
holds; no lantern relation or modularity hypothesis is used. -/
theorem pivotal_twist_finite_of_balancing (p : Dimensions.PivotalStructure (C := C.Obj))
    (hbalance : IsPivotalTwistBalanced C p) :
    ∀ i, IsOfFinOrder (End.of ((Dimensions.pivotalBraidedTwist C p (simples C i)).hom)) := fun i ↦
  letI : Simple (simples C i) := simples_simple C i
  letI : FiniteDimensional ℂ (simples C i ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  by simpa [CentreCabling.pivotalTwistUnit, Dimensions.pivotalBraidedTwistScalar] using
    (Ground.simpleEndScalar (simples C i)).symm.toMonoidHom.isOfFinOrder
      (Units.isOfFinOrder_val.mpr (natural_scalars_finite_of_simple_balancing C
        (pivotal_twist_has_simple_scalars C p) (pivotal_twist_simple_balance C p hbalance) i))

/-- The actual pivotal twist balancing law alone forces every mixed
monodromy to have finite order; no lantern relation is required. -/
theorem mixed_monodromy_finite_of_pivotal_balancing (p : Dimensions.PivotalStructure (C := C.Obj))
    (hbalance : IsPivotalTwistBalanced C p)
    (X Y : C.Obj) : IsOfFinOrder (End.of (Modular.doubleBraiding X Y)) :=
  CentreCabling.mixed_monodromy_finite_of_balanced_finite_twist
    (Dimensions.pivotalBraidedTwistNaturalIso C p)
    (pivotal_twist_finite_of_balancing C p hbalance) hbalance X Y

end PropertyF.Ground.CentreModular
end
