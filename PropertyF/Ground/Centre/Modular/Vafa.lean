module
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import PropertyF.Ground.CentreCabling.TwistFinite
public import PropertyF.Ground.CentreInduction.FiniteSum
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

/-- The FP regular-element cancellation at the heart of the determinant
argument: every additive fusion-bicharacter vanishes in characteristic zero. -/
theorem regular_fusion_derivation_vanishes
    (M : Type w) [AddCommGroup M] [Module ℝ M]
    (B : Fin (rank C) → Fin (rank C) → M)
    (hhex : ∀ i j z,
      (∑ k, (fusionCoeff C i j k : ℝ) • B k z) =
        fpSimple C j • B i z + fpSimple C i • B j z) :
    ∀ i z, B i z = 0 := by
  classical
  intro i z
  let R : M := ∑ j, fpSimple C j • B j z
  let D : ℝ := ∑ j, fpSimple C j ^ 2
  have hreg (k : Fin (rank C)) :
      (∑ j, fpSimple C j * (fusionCoeff C i j k : ℝ)) = fpSimple C i * fpSimple C k := by
    simp_rw [Modular.fusionCoeff_dual_adjoint C i]
    simpa only [mul_comm, fpSimple_dual] using (fpSimple_mul C (dualIndex C i) k).symm
  have hsum : (∑ j, fpSimple C j • ∑ k, (fusionCoeff C i j k : ℝ) • B k z) =
      fpSimple C i • R := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hreg, mul_smul]
    dsimp [R]
    rw [Finset.smul_sum]
  have hsum' : (∑ j, fpSimple C j • ∑ k, (fusionCoeff C i j k : ℝ) • B k z) =
      D • B i z + fpSimple C i • R := by
    simp_rw [hhex, smul_add, smul_smul]
    simp only [Finset.sum_add_distrib, ← Finset.sum_smul, D, R, pow_two,
      Finset.smul_sum, smul_smul, mul_comm]
  have hzero : D • B i z = 0 := by
    have h := hsum'.symm.trans hsum
    exact add_right_cancel (h.trans (zero_add (fpSimple C i • R)).symm)
  have hpos : 0 < D := by
    change 0 < globalFPDimension C
    exact lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)
  exact (smul_eq_zero.mp hzero).resolve_left (ne_of_gt hpos)

end PropertyF.Ground.CentreModular
end

section
open TensorProduct
namespace PropertyF.Ground.CentreModular

/-- A real vector space recording complex units up to torsion. -/
abbrev vafaUnitSpace : Type := ℝ ⊗[ℚ] (ℚ ⊗[ℤ] Additive ℂˣ)

/-- The image of a complex unit in the torsion-detecting vector space. -/
def vafaUnitClass (z : ℂˣ) : vafaUnitSpace := 1 ⊗ₜ[ℚ] (1 ⊗ₜ[ℤ] Additive.ofMul z)

/-- The unit class vanishes exactly for a root of unity. -/
theorem vafaUnitClass_eq_zero_iff (z : ℂˣ) : vafaUnitClass z = 0 ↔ IsOfFinOrder z := by
  have h : (1 ⊗ₜ[ℚ] (1 ⊗ₜ[ℤ] Additive.ofMul z) : vafaUnitSpace) = 0 ↔
      (1 ⊗ₜ[ℤ] Additive.ofMul z : ℚ ⊗[ℤ] Additive ℂˣ) = 0 :=
    Module.FaithfullyFlat.one_tmul_eq_zero_iff ℚ (ℚ ⊗[ℤ] Additive ℂˣ) _
  rw [vafaUnitClass, h]
  have hh := IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ (Additive ℂˣ) 1) (m := Additive.ofMul z)
  change ((1 ⊗ₜ[ℤ] Additive.ofMul z : ℚ ⊗[ℤ] Additive ℂˣ) = 0) ↔
    ∃ s : nonZeroDivisors ℤ, (s : ℤ) • Additive.ofMul z = 0 at hh
  rw [hh, isOfFinOrder_iff_zpow_eq_one]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_, ?_⟩
    · exact nonZeroDivisors.ne_zero s.property
    · exact hs
  · rintro ⟨n, hn, hz⟩
    refine ⟨⟨n, ?_⟩, ?_⟩
    · exact mem_nonZeroDivisors_iff_ne_zero.mpr hn
    · exact hz

/-- Multiplication of units becomes addition in the Vafa vector space. -/
theorem vafaUnitClass_mul (z w : ℂˣ) :
    vafaUnitClass (z * w) = vafaUnitClass z + vafaUnitClass w := by
  simp [vafaUnitClass, TensorProduct.tmul_add]

/-- Natural powers become scalar multiples in the Vafa vector space. -/
theorem vafaUnitClass_pow (z : ℂˣ) (n : ℕ) :
    vafaUnitClass (z ^ n) = n • vafaUnitClass z := by
  simp [vafaUnitClass]

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
    homAction (R := R) S X (a ≪≫ b) = (homAction (R := R) S X a).trans (homAction (R := R) S X b) := by
  ext f
  simp [homAction, CategoryTheory.Linear.homCongr_apply, Category.assoc]

/-- The actual FP-weighted categorical determinant of an automorphism,
valued in a real vector space that detects torsion. -/
def fpDeterminant (X : C.Obj) (a : X ≅ X) :
    vafaUnitSpace :=
  ∑ i, fpSimple C i • vafaUnitClass (homAction (R := ℂ) (simples C i) X a).det

/-- FP determinants turn composition into addition. -/
theorem fpDeterminant_trans {X : C.Obj}
    (a b : X ≅ X) : fpDeterminant C X (a ≪≫ b) =
      fpDeterminant C X a + fpDeterminant C X b := by
  unfold fpDeterminant
  simp_rw [homAction_trans, LinearEquiv.det_trans, vafaUnitClass_mul, smul_add]
  rw [Finset.sum_add_distrib, add_comm]

/-- The actual scalar automorphism of an object. -/
def scalarIso {R : Type*} [CommSemiring R] {D : Type u} [Category.{v} D]
    [Preadditive D] [Linear R D] (X : D) (z : Rˣ) : X ≅ X where
  hom := (z : R) • 𝟙 X
  inv := ((z⁻¹ : Rˣ) : R) • 𝟙 X
  hom_inv_id := by simp [Linear.comp_smul, smul_smul]
  inv_hom_id := by simp [Linear.comp_smul, smul_smul]

/-- On a scalar map, each Hom-space determinant is the corresponding power. -/
theorem homAction_det_scalar {R : Type*} [Field R] {D : Type u} [Category.{v} D]
    [Preadditive D] [Linear R D] {S X : D} (z : Rˣ) :
    (homAction (R := R) S X (scalarIso X z)).det = z ^ Module.finrank R (S ⟶ X) := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det _ = (z : R) ^ _
  have h : (homAction (R := R) S X (scalarIso X z)).toLinearMap = (z : R) • LinearMap.id := by
    ext f
    simp [homAction, scalarIso, CategoryTheory.Linear.homCongr_apply]
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one]

/-- A scalar automorphism has FP determinant equal to its unit class weighted
by the actual FP dimension of the object. -/
theorem fpDeterminant_scalar (X : C.Obj) (z : ℂˣ) :
    fpDeterminant C X (scalarIso X z) = fpDimension C X • vafaUnitClass z := by
  simp only [fpDeterminant, fpDimension, homAction_det_scalar, vafaUnitClass_pow,
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

/-- FP determinants are invariant under actual categorical conjugation. -/
theorem fpDeterminant_conjugate
    {X Y : C.Obj} (e : X ≅ Y) (a : X ≅ X) :
    fpDeterminant C Y (e.symm ≪≫ a ≪≫ e) = fpDeterminant C X a := by
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

/-- Tensoring a scalar automorphism preserves the scalar action. -/
theorem tensor_scalarIso {R : Type*} [CommSemiring R] {D : Type u}
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] [Linear R D]
    [MonoidalPreadditive D] [MonoidalLinear R D] (X Y : D) (z : Rˣ) :
    Iso.refl X ⊗ᵢ scalarIso Y z = scalarIso (X ⊗ Y) z :=
  Iso.ext (by simp [scalarIso, tensorHom_def])

/-- The tensor-product determinant rule when the second automorphism is scalar. -/
theorem fpDeterminant_tensor_scalar
    (X Y : C.Obj) (z : ℂˣ) :
    fpDeterminant C (X ⊗ Y) (Iso.refl X ⊗ᵢ scalarIso Y z) =
      fpDimension C X • fpDeterminant C Y (scalarIso Y z) := by
  rw [tensor_scalarIso, fpDeterminant_scalar, fpDeterminant_scalar, fpDimension_tensor, mul_smul]

end PropertyF.Ground.CentreModular
end

section
open scoped BigOperators
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- The FP-weighted twist-balance relation forces all twist scalars to have
finite order. This is a numerical consequence; the categorical balance
relation is not assumed proved here. -/
theorem finite_order_of_fp_twist_balance
    (t : Fin (rank C) → ℂˣ)
    (hbalance : ∀ i j,
      (∑ k, (fusionCoeff C i j k : ℝ) • (fpSimple C k • vafaUnitClass (t k))) =
        (fpSimple C i * fpSimple C j) • (vafaUnitClass (t i) + vafaUnitClass (t j))) :
    ∀ i, IsOfFinOrder (t i) := by
  let B : Fin (rank C) → Fin (rank C) → vafaUnitSpace :=
    fun i _ => fpSimple C i • vafaUnitClass (t i)
  have hhex : ∀ i j z, (∑ k, (fusionCoeff C i j k : ℝ) • B k z) =
      fpSimple C j • B i z + fpSimple C i • B j z := by
    intro i j z
    dsimp [B]
    rw [hbalance]
    simp only [smul_add, smul_smul]
    rw [mul_comm (fpSimple C j) (fpSimple C i)]
  have hzero := regular_fusion_derivation_vanishes C vafaUnitSpace B hhex
  intro i
  have hi := hzero i (unitIndex C)
  change fpSimple C i • vafaUnitClass (t i) = 0 at hi
  exact (vafaUnitClass_eq_zero_iff _).mp
    ((smul_eq_zero.mp hi).resolve_left (ne_of_gt (fpSimple_pos C i)))

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
    fpDeterminant C X (η.app X) = ∑ i,
      (Module.finrank ℂ (simples C i ⟶ X) : ℝ) • (fpSimple C i • vafaUnitClass (t i)) := by
  unfold fpDeterminant
  apply Finset.sum_congr rfl
  intro i _
  have hd : (homAction (R := ℂ) (simples C i) X (η.app X)).det =
      (t i) ^ Module.finrank ℂ (simples C i ⟶ X) := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    change LinearMap.det _ = (t i : ℂ) ^ _
    rw [homAction_natural_scalar η (t i : ℂ) (ht i), LinearMap.det_smul,
      LinearMap.det_id, mul_one]
  rw [hd, vafaUnitClass_pow, ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [smul_smul, mul_comm]

/-- A natural automorphism whose actual FP determinant satisfies the
multiplicative balance on simple tensor products has finite-order simple
scalars. The displayed determinant identity remains an explicit premise. -/
theorem natural_scalars_finite_of_fpDeterminant_balance
    (ht : HasSimpleScalars C η t)
    (hdet : ∀ i j, fpDeterminant C (simples C i ⊗ simples C j)
      (η.app (simples C i ⊗ simples C j)) =
        fpDimension C (simples C i ⊗ simples C j) •
          (vafaUnitClass (t i) + vafaUnitClass (t j))) :
    ∀ i, IsOfFinOrder (t i) := by
  apply finite_order_of_fp_twist_balance C t
  intro i j
  simpa only [fpDeterminant_natural C ht, fpDimension_tensor, fpDimension_simple, fusionCoeff] using hdet i j

/-- The actual double braiding as an automorphism. -/
def monodromyIso {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (X Y : D) : X ⊗ Y ≅ X ⊗ Y :=
  (β_ X Y) ≪≫ (β_ Y X)

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
    (hmon : ∀ i j, fpDeterminant C (simples C i ⊗ simples C j)
      (monodromyIso (simples C i) (simples C j)) = 0) :
    ∀ i, IsOfFinOrder (t i) := by
  apply natural_scalars_finite_of_fpDeterminant_balance C ht
  intro i j
  rw [hbalance, fpDeterminant_trans, hmon, add_zero, fpDeterminant_scalar,
    vafaUnitClass_mul]

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
      (homAction (R := R) S X a).det * (homAction (R := R) S Y b).det := by
  let E := homBiprodLinearEquiv (R := R) S X Y
  let A := homAction (R := R) S (X ⊞ Y) (biprod.mapIso a b)
  let L := homAction (R := R) S X a
  let right := homAction (R := R) S Y b
  have h : (E.symm.trans A).trans E = L.prodCongr right := by
    ext f <;> simp [E, A, L, right, homBiprodLinearEquiv, homAction,
      CategoryTheory.Linear.homCongr_apply, Category.assoc]
  apply Units.ext
  rw [← LinearEquiv.det_conj A E, h, LinearEquiv.coe_det]
  change LinearMap.det (L.toLinearMap.prodMap right.toLinearMap) = _
  rw [LinearMap.det_prodMap]
  simp only [Units.val_mul, LinearEquiv.coe_det]
  rfl

/-- FP determinants are additive over direct sums of automorphisms. -/
theorem fpDeterminant_biprod
    {X Y : C.Obj} (a : X ≅ X) (b : Y ≅ Y) :
    fpDeterminant C (X ⊞ Y) (biprod.mapIso a b) =
      fpDeterminant C X a + fpDeterminant C Y b := by
  let : ∀ A B : C.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  unfold fpDeterminant
  simp_rw [homAction_det_biprod, vafaUnitClass_mul, smul_add]
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

/-- The tensor determinant identity is closed under binary direct sums. -/
theorem fpDeterminant_tensor_biprod
    (X : C.Obj) {Y Z : C.Obj} (a : Y ≅ Y) (b : Z ≅ Z)
    (ha : fpDeterminant C (X ⊗ Y) (Iso.refl X ⊗ᵢ a) = fpDimension C X • fpDeterminant C Y a)
    (hb : fpDeterminant C (X ⊗ Z) (Iso.refl X ⊗ᵢ b) = fpDimension C X • fpDeterminant C Z b) :
    fpDeterminant C (X ⊗ (Y ⊞ Z)) (Iso.refl X ⊗ᵢ biprod.mapIso a b) =
      fpDimension C X • fpDeterminant C (Y ⊞ Z) (biprod.mapIso a b) := by
  let e := Functor.mapBiprod (tensorLeft X) Y Z
  let A := biprod.mapIso (Iso.refl X ⊗ᵢ a) (Iso.refl X ⊗ᵢ b)
  have hc : Iso.refl X ⊗ᵢ biprod.mapIso a b = e ≪≫ A ≪≫ e.symm := by
    apply Iso.ext
    apply (cancel_epi e.inv).1
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
    · exact (congrArg (fun f => (X ◁ b.hom) ≫ f) hright).symm
  rw [hc]
  have hd := fpDeterminant_conjugate C e.symm A
  change fpDeterminant C (X ⊗ (Y ⊞ Z)) (e ≪≫ A ≪≫ e.symm) = fpDeterminant C _ A at hd
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
  let m : C.Obj → ℕ := fun W => Module.finrank ℂ (W ⟶ W)
  induction X using (measure m).wf.induction with
  | h X ih =>
    by_cases hz : IsZero X
    · exact .zero hz
    · obtain ⟨i, hi⟩ := exists_positive_multiplicity C X hz
      let S := simples C i
      let : Simple S := simples_simple C i
      let : FiniteDimensional ℂ (S ⟶ X) := IsFusionCategory.hom_finite _ _
      obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hi
      let : Mono f := mono_of_nonzero_from_simple hf
      obtain ⟨r, hr⟩ := split_from_simple f hf
      let : IsSplitMono f := IsSplitMono.mk' { retraction := r, id := hr }
      let E := ShortComplex.cokernelSequence f
      let split : E.Splitting := ShortComplex.Splitting.ofExactOfRetraction E
        (ShortComplex.cokernelSequence_exact f) (retraction f)
        (IsSplitMono.id f) inferInstance
      let K := cokernel f
      let e : X ≅ S ⊞ K := split.isoBinaryBiproduct
      let : ∀ A B : C.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
      have hs : ¬ IsZero S := by
        intro h
        exact id_nonzero _ ((IsZero.iff_id_eq_zero _).mp h)
      have he : Module.finrank ℂ (X ⟶ X) = Module.finrank ℂ (S ⊞ K ⟶ S ⊞ K) :=
        (CategoryTheory.Linear.homCongr ℂ e e).finrank_eq
      have hk : m K < m X := by
        change Module.finrank ℂ (K ⟶ K) < Module.finrank ℂ (X ⟶ X)
        rw [he]
        exact CentreInduction.finrank_end_complement_lt _ K hs
      exact .cons (simples_simple C i) (ih K hk) ⟨e⟩

/-- Identity automorphisms have zero FP determinant. -/
theorem fpDeterminant_refl (X : C.Obj) :
    fpDeterminant C X (Iso.refl X) = 0 := by
  simpa using (fpDeterminant_trans C (Iso.refl X) (Iso.refl X))

/-- The tensor determinant rule holds on any simple object. -/
theorem fpDeterminant_tensor_of_simple
    (X S : C.Obj) [Simple S] (a : S ≅ S) :
    fpDeterminant C (X ⊗ S) (Iso.refl X ⊗ᵢ a) =
      fpDimension C X • fpDeterminant C S a := by
  let : FiniteDimensional ℂ (S ⟶ S) := IsFusionCategory.hom_finite _ _
  obtain ⟨z, hz⟩ := endomorphism_simple_eq_smul_id ℂ a.hom
  have hne : z ≠ 0 := by
    intro h
    have ha : a.hom = 0 := by simpa [h] using hz.symm
    have hh := a.hom_inv_id
    simp [ha] at hh
    exact id_nonzero _ hh.symm
  have ha : a = scalarIso S (Units.mk0 z hne) := by
    apply Iso.ext
    exact hz.symm
  rw [ha]
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
      biprod.mapIso (η.app X) (η.app Y) ≪≫ (F.mapBiprod X Y).symm := by
  apply Iso.ext
  apply (cancel_mono (F.mapBiprod X Y).hom).1
  change (η.app (X ⊞ Y)).hom ≫ (F.mapBiprod X Y).hom =
    ((F.mapBiprod X Y).hom ≫ (biprod.mapIso (η.app X) (η.app Y)).hom ≫
      (F.mapBiprod X Y).inv) ≫ (F.mapBiprod X Y).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply biprod.hom_ext
  · simpa only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst, biprod.lift_fst_assoc,
      biprod.mapIso_hom, biprod.map_fst, Iso.app_hom] using (η.hom.naturality (biprod.fst : X ⊞ Y ⟶ X)).symm
  · simpa only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd, biprod.lift_snd_assoc,
      biprod.mapIso_hom, biprod.map_snd, Iso.app_hom] using (η.hom.naturality (biprod.snd : X ⊞ Y ⟶ Y)).symm

/-- Tensoring a conjugated automorphism conjugates its tensor extension. -/
theorem tensor_conjugate_iso {D : Type u} [Category.{v} D] [MonoidalCategory D]
    (X : D) {Y Z : D} (e : Y ≅ Z) (a : Z ≅ Z) :
    (Iso.refl X ⊗ᵢ (e ≪≫ a ≪≫ e.symm)) =
      (Iso.refl X ⊗ᵢ e) ≪≫ (Iso.refl X ⊗ᵢ a) ≪≫ (Iso.refl X ⊗ᵢ e).symm :=
  Iso.ext (by simp [tensorIso_hom, tensorHom_def, whiskerLeft_comp])

/-- The categorical FP determinant tensor rule holds for components of
any natural automorphism, by semisimplicity. -/
theorem fpDeterminant_tensor_natural
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (X Y : C.Obj) :
    fpDeterminant C (X ⊗ Y) (Iso.refl X ⊗ᵢ η.app Y) =
      fpDimension C X • fpDeterminant C Y (η.app Y) := by
  have hY := base_finite_simple_sum C Y
  induction hY with
  | @zero W hz =>
    have hη : η.app W = Iso.refl W := Iso.ext (hz.eq_of_src _ _)
    have ht : Iso.refl X ⊗ᵢ Iso.refl W = Iso.refl (X ⊗ W) := Iso.ext (by simp)
    simp only [hη, ht, fpDeterminant_refl, smul_zero]
  | @cons Y S K hs hk he ih =>
    obtain ⟨e⟩ := he
    have hS : fpDeterminant C (X ⊗ S) (Iso.refl X ⊗ᵢ η.app S) =
        fpDimension C X • fpDeterminant C S (η.app S) := by
      let : Simple S := hs
      exact fpDeterminant_tensor_of_simple C X S (η.app S)
    have hsum := fpDeterminant_tensor_biprod C X (η.app S) (η.app K) hS ih
    let : PreservesBinaryBiproducts (𝟭 C.Obj) := preservesBinaryBiproducts_of_preservesBiproducts _
    have hid : (𝟭 C.Obj).mapBiprod S K = Iso.refl (S ⊞ K) := by
      apply Iso.ext
      apply biprod.hom_ext <;> simp
    have hsum' : η.app (S ⊞ K) = biprod.mapIso (η.app S) (η.app K) := by
      simpa [hid] using functor_natural_app_biprod (𝟭 C.Obj) η S K
    rw [← hsum'] at hsum
    have he : (𝟭 C.Obj).mapIso e = e := Iso.ext rfl
    have hη : η.app Y = e ≪≫ η.app (S ⊞ K) ≪≫ e.symm := by
      simpa only [he] using functor_natural_app_conjugate (𝟭 C.Obj) η e
    rw [hη, tensor_conjugate_iso]
    have hl := fpDeterminant_conjugate C (Iso.refl X ⊗ᵢ e).symm
      (Iso.refl X ⊗ᵢ η.app (S ⊞ K))
    have hr := fpDeterminant_conjugate C e.symm (η.app (S ⊞ K))
    change fpDeterminant C (X ⊗ Y) ((Iso.refl X ⊗ᵢ e) ≪≫
      (Iso.refl X ⊗ᵢ η.app (S ⊞ K)) ≪≫ (Iso.refl X ⊗ᵢ e).symm) = _ at hl
    change fpDeterminant C Y (e ≪≫ η.app (S ⊞ K) ≪≫ e.symm) = _ at hr
    rw [hl, hr]
    exact hsum

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

/-- Any isomorphism-invariant additive object function is determined by
its values on simples and the actual Hom-space multiplicities. -/
theorem additive_object_function_decomposition (M : Type w) [AddCommGroup M] [Module ℝ M]
    (f : C.Obj → M)
    (hiso : ∀ {X Y : C.Obj}, (X ≅ Y) → f X = f Y)
    (hzero : ∀ X, IsZero X → f X = 0)
    (hadd : ∀ X Y, f (X ⊞ Y) = f X + f Y)
    (X : C.Obj) :
    f X = ∑ i, (Module.finrank ℂ (simples C i ⟶ X) : ℝ) • f (simples C i) := by
  classical
  let : ∀ A B : C.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  have hsimple (S : C.Obj) [Simple S] :
      f S = ∑ i, (Module.finrank ℂ (simples C i ⟶ S) : ℝ) • f (simples C i) := by
    obtain ⟨j, ⟨e⟩⟩ := exists_simple_iso C S
    have hr (i : Fin (rank C)) : Module.finrank ℂ (simples C i ⟶ S) =
        Module.finrank ℂ (simples C i ⟶ simples C j) :=
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq
    simp_rw [hr, finrank_simples_hom]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_eq_single j]
    · simpa using hiso e
    · intro i _ hij
      simp [hij]
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
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
    rw [hiso e, hadd, hsimple S, ih]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hdim : Module.finrank ℂ (simples C i ⟶ W) =
        Module.finrank ℂ (simples C i ⟶ S) + Module.finrank ℂ (simples C i ⟶ K) := by
      calc
        _ = Module.finrank ℂ (simples C i ⟶ S ⊞ K) :=
          (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq
        _ = Module.finrank ℂ ((simples C i ⟶ S) × (simples C i ⟶ K)) :=
          (homBiprodLinearEquiv (simples C i) S K).finrank_eq
        _ = _ := Module.finrank_prod
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
    fpDeterminant C (F.obj X) (η.app X) = ∑ i,
      (Module.finrank ℂ (simples C i ⟶ X) : ℝ) •
        fpDeterminant C (F.obj (simples C i)) (η.app (simples C i)) := by
  apply additive_object_function_decomposition C vafaUnitSpace
    (fun X => fpDeterminant C (F.obj X) (η.app X))
  · intro X Y e
    rw [functor_natural_app_conjugate F η e]
    exact fpDeterminant_conjugate C (F.mapIso e).symm (η.app Y)
  · intro X hX
    have hFX : IsZero (F.obj X) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      rw [← F.map_id, (IsZero.iff_id_eq_zero X).mp hX, F.map_zero]
    have hη : η.app X = Iso.refl (F.obj X) := by
      apply Iso.ext
      exact hFX.eq_of_src _ _
    rw [hη, fpDeterminant_refl]
  · intro X Y
    let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
    rw [functor_natural_app_biprod F η X Y]
    have h := fpDeterminant_conjugate C (F.mapBiprod X Y).symm
      (biprod.mapIso (η.app X) (η.app Y))
    change fpDeterminant C (F.obj (X ⊞ Y))
      (F.mapBiprod X Y ≪≫ biprod.mapIso (η.app X) (η.app Y) ≪≫ (F.mapBiprod X Y).symm) = _ at h
    rw [h, fpDeterminant_biprod]

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
    fpDeterminant C (X ⊗ Y) (Iso.refl X ⊗ᵢ (scalarIso Y z ≪≫ η.app Y)) =
      fpDimension C X • fpDeterminant C Y (scalarIso Y z ≪≫ η.app Y) := by
  have h : (Iso.refl X ⊗ᵢ (scalarIso Y z ≪≫ η.app Y)) =
      (Iso.refl X ⊗ᵢ scalarIso Y z) ≪≫ (Iso.refl X ⊗ᵢ η.app Y) := by
    apply Iso.ext
    simp [tensorIso_hom, tensorHom_def, whiskerLeft_comp]
  rw [h, fpDeterminant_trans, fpDeterminant_trans, fpDeterminant_tensor_scalar,
    fpDeterminant_tensor_natural, smul_add]

/-- Balancing identifies the mixed double braiding of two simples with a
scalar multiple of the twist component. -/
theorem monodromy_simple_eq_scalar_natural
    (hbalance : HasSimpleBalance C η t)
    (i j : Fin (rank C)) :
    monodromyIso (simples C i) (simples C j) =
      scalarIso (simples C i ⊗ simples C j) (t i * t j)⁻¹ ≪≫
        η.app (simples C i ⊗ simples C j) := by
  rw [hbalance]
  have h : scalarIso (simples C i ⊗ simples C j) (t i * t j)⁻¹ =
      (scalarIso (simples C i ⊗ simples C j) (t i * t j)).symm := by
    apply Iso.ext
    rfl
  rw [h]
  simp

/-- Under the explicit balancing equation, the tensor determinant rule holds
for every simple mixed monodromy. -/
theorem fpDeterminant_tensor_simple_monodromy
    (hbalance : HasSimpleBalance C η t)
    (X : C.Obj) (i j : Fin (rank C)) :
    fpDeterminant C (X ⊗ (simples C i ⊗ simples C j))
      (Iso.refl X ⊗ᵢ monodromyIso (simples C i) (simples C j)) =
      fpDimension C X • fpDeterminant C (simples C i ⊗ simples C j)
        (monodromyIso (simples C i) (simples C j)) := by
  rw [monodromy_simple_eq_scalar_natural C hbalance]
  exact fpDeterminant_tensor_scalar_natural C η X _ _

/-- Braiding transports tensoring an automorphism on the right to tensoring it
on the left, preserving its categorical FP determinant. -/
theorem fpDeterminant_tensor_flip
    (X : C.Obj) {Y : C.Obj} (a : Y ≅ Y) :
    fpDeterminant C (Y ⊗ X) (a ⊗ᵢ Iso.refl X) =
      fpDeterminant C (X ⊗ Y) (Iso.refl X ⊗ᵢ a) := by
  let e := β_ Y X
  have h : a ⊗ᵢ Iso.refl X = e ≪≫ (Iso.refl X ⊗ᵢ a) ≪≫ e.symm := by
    apply Iso.ext
    apply (cancel_mono e.hom).1
    simp [e, tensorIso_hom]
  rw [h]
  exact fpDeterminant_conjugate C e.symm (Iso.refl X ⊗ᵢ a)

/-- Under balancing, tensoring a simple mixed monodromy on either side
satisfies the FP determinant rule. -/
theorem fpDeterminant_simple_monodromy_tensor
    (hbalance : HasSimpleBalance C η t)
    (X : C.Obj) (i j : Fin (rank C)) :
    fpDeterminant C ((simples C i ⊗ simples C j) ⊗ X)
      (monodromyIso (simples C i) (simples C j) ⊗ᵢ Iso.refl X) =
      fpDimension C X • fpDeterminant C (simples C i ⊗ simples C j)
        (monodromyIso (simples C i) (simples C j)) := by
  rw [fpDeterminant_tensor_flip]
  exact fpDeterminant_tensor_simple_monodromy C hbalance X i j

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- The categorical double-braiding hexagon, as a product of conjugate
monodromy automorphisms. -/
theorem monodromy_hexagon_iso {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] (Z X Y : D) :
    (α_ Z X Y) ≪≫ monodromyIso Z (X ⊗ Y) ≪≫ (α_ Z X Y).symm =
      (((β_ Z X) ⊗ᵢ Iso.refl Y) ≪≫ (α_ X Z Y)) ≪≫
        (Iso.refl X ⊗ᵢ monodromyIso Z Y) ≪≫
        (((β_ Z X) ⊗ᵢ Iso.refl Y) ≪≫ (α_ X Z Y)).symm ≪≫
        (monodromyIso Z X ⊗ᵢ Iso.refl Y) :=
  Iso.ext (by simp [monodromyIso, tensorIso_hom, tensorHom_id, id_tensorHom, Category.assoc,
    ← comp_whiskerRight])

/-- The actual FP determinant of the monodromy hexagon is the weighted sum
of the two simple monodromy determinants, under simple twist balancing. -/
theorem fpDeterminant_monodromy_hexagon
    {η : 𝟭 C.Obj ≅ 𝟭 C.Obj} {t : Fin (rank C) → ℂˣ}
    (hbalance : HasSimpleBalance C η t)
    (z i j : Fin (rank C)) :
    fpDeterminant C (simples C z ⊗ (simples C i ⊗ simples C j))
      (monodromyIso (simples C z) (simples C i ⊗ simples C j)) =
    fpSimple C i • fpDeterminant C (simples C z ⊗ simples C j)
      (monodromyIso (simples C z) (simples C j)) +
    fpSimple C j • fpDeterminant C (simples C z ⊗ simples C i)
      (monodromyIso (simples C z) (simples C i)) := by
  let Z := simples C z
  let X := simples C i
  let Y := simples C j
  let t' := α_ Z X Y
  let u := ((β_ Z X) ⊗ᵢ Iso.refl Y) ≪≫ (α_ X Z Y)
  let q := Iso.refl X ⊗ᵢ monodromyIso Z Y
  let r := monodromyIso Z X ⊗ᵢ Iso.refl Y
  have hconj := fpDeterminant_conjugate C t'.symm (monodromyIso Z (X ⊗ Y))
  change fpDeterminant C ((Z ⊗ X) ⊗ Y)
    (t' ≪≫ monodromyIso Z (X ⊗ Y) ≪≫ t'.symm) = _ at hconj
  rw [monodromy_hexagon_iso] at hconj
  have hq := fpDeterminant_conjugate C u.symm q
  change fpDeterminant C ((Z ⊗ X) ⊗ Y) (u ≪≫ q ≪≫ u.symm) = _ at hq
  change fpDeterminant C ((Z ⊗ X) ⊗ Y) (u ≪≫ q ≪≫ u.symm ≪≫ r) = _ at hconj
  have heq : (u ≪≫ q ≪≫ u.symm ≪≫ r) = (u ≪≫ q ≪≫ u.symm) ≪≫ r := by
    apply Iso.ext
    simp
  rw [heq, fpDeterminant_trans, hq] at hconj
  have h1 := fpDeterminant_tensor_simple_monodromy C hbalance X z j
  have h2 := fpDeterminant_simple_monodromy_tensor C hbalance Y z i
  change fpDeterminant C (X ⊗ (Z ⊗ Y)) q = _ at h1
  change fpDeterminant C ((Z ⊗ X) ⊗ Y) r = _ at h2
  rw [h1, h2, fpDimension_simple, fpDimension_simple] at hconj
  exact hconj.symm

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

/-- For a fixed first strand, double braiding is a natural automorphism of
the actual tensor-left functor. -/
def monodromyNaturalIso {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] (Z : D) :
    tensorLeft Z ≅ tensorLeft Z :=
  NatIso.ofComponents (fun W => monodromyIso Z W) (by
    intro X Y f
    change (Z ◁ f) ≫ ((β_ Z Y).hom ≫ (β_ Y Z).hom) =
      ((β_ Z X).hom ≫ (β_ X Z).hom) ≫ (Z ◁ f)
    simp only [← id_tensorHom, Category.assoc]
    rw [braiding_naturality_assoc, braiding_naturality])

/-- FP determinant of a mixed monodromy expands over simple summands of
the second strand. -/
theorem fpDeterminant_monodromy_decomposition
    (Z W : C.Obj) :
    fpDeterminant C (Z ⊗ W) (monodromyIso Z W) = ∑ i,
      (Module.finrank ℂ (simples C i ⟶ W) : ℝ) •
        fpDeterminant C (Z ⊗ simples C i) (monodromyIso Z (simples C i)) :=
  fpDeterminant_functor_natural_decomposition C (tensorLeft Z) (monodromyNaturalIso Z) W

/-- Under simple twist balancing, the FP determinant of every simple mixed
monodromy vanishes. -/
theorem fpDeterminant_simple_monodromy_eq_zero
    (hbalance : HasSimpleBalance C η t)
    (z i : Fin (rank C)) :
    fpDeterminant C (simples C z ⊗ simples C i)
      (monodromyIso (simples C z) (simples C i)) = 0 := by
  let B : Fin (rank C) → Fin (rank C) → vafaUnitSpace := fun i z =>
    fpDeterminant C (simples C z ⊗ simples C i)
      (monodromyIso (simples C z) (simples C i))
  have hhex : ∀ i j z, (∑ k, (fusionCoeff C i j k : ℝ) • B k z) =
      fpSimple C j • B i z + fpSimple C i • B j z := by
    intro i j z
    have h := fpDeterminant_monodromy_hexagon C hbalance z i j
    rw [fpDeterminant_monodromy_decomposition] at h
    change (∑ k, (fusionCoeff C i j k : ℝ) • B k z) = _ at h
    simpa [B, add_comm] using h
  exact regular_fusion_derivation_vanishes C vafaUnitSpace B hhex i z

/-- Under an actual natural twist and its simple balancing equation,
the simple twist scalars have finite order. -/
theorem natural_scalars_finite_of_simple_balancing
    (ht : HasSimpleScalars C η t)
    (hbalance : HasSimpleBalance C η t) :
    ∀ i, IsOfFinOrder (t i) := by
  apply natural_scalars_finite_of_monodromy_determinant C ht hbalance
  intro i j
  exact fpDeterminant_simple_monodromy_eq_zero C hbalance i j

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

/-- Pivotal twist scalars have finite order whenever its actual balancing law
holds; no lantern relation or modularity hypothesis is used. -/
theorem pivotal_twist_finite_of_balancing (p : Dimensions.PivotalStructure (C := C.Obj))
    (hbalance : IsPivotalTwistBalanced C p) :
    ∀ i, IsOfFinOrder (End.of ((Dimensions.pivotalBraidedTwist C p (simples C i)).hom)) := by
  let η := Dimensions.pivotalBraidedTwistNaturalIso C p
  let t := CentreCabling.pivotalTwistUnit C p
  have ht (i : Fin (rank C)) : (η.app (simples C i)).hom = (t i : ℂ) • 𝟙 (simples C i) := by
    let : Simple (simples C i) := simples_simple C i
    exact Dimensions.pivotalBraidedTwist_simple C p (simples C i)
  have hb (i j : Fin (rank C)) : η.app (simples C i ⊗ simples C j) =
      scalarIso (simples C i ⊗ simples C j) (t i * t j) ≪≫
        monodromyIso (simples C i) (simples C j) := by
    apply Iso.ext
    have h := hbalance (simples C i) (simples C j)
    change Modular.doubleBraiding _ _ ≫ ((η.app (simples C i)).hom ⊗ₘ
      (η.app (simples C j)).hom) = (η.app (simples C i ⊗ simples C j)).hom at h
    rw [ht i, ht j] at h
    simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul,
      MonoidalLinear.smul_whiskerRight,
      Linear.smul_comp, Linear.comp_smul, smul_smul] at h
    simpa [scalarIso, monodromyIso, Modular.doubleBraiding, Category.assoc,
      Linear.smul_comp, mul_comm] using h.symm
  have hf := natural_scalars_finite_of_simple_balancing C ht hb
  intro i
  have hf' : IsOfFinOrder ((t i : ℂˣ) : ℂ) := Units.isOfFinOrder_val.mpr (hf i)
  let : Simple (simples C i) := simples_simple C i
  simpa [t, CentreCabling.pivotalTwistUnit, Dimensions.pivotalBraidedTwistScalar] using
    (Dimensions.simpleEndScalarEquiv C (simples C i)).symm.toMonoidHom.isOfFinOrder hf'

/-- The actual pivotal twist balancing law alone forces every mixed
monodromy to have finite order; no lantern relation is required. -/
theorem mixed_monodromy_finite_of_pivotal_balancing (p : Dimensions.PivotalStructure (C := C.Obj))
    (hbalance : IsPivotalTwistBalanced C p)
    (X Y : C.Obj) : IsOfFinOrder (End.of (Modular.doubleBraiding X Y)) := by
  apply CentreCabling.mixed_monodromy_finite_of_balanced_finite_twist C
    (Dimensions.pivotalBraidedTwistNaturalIso C p)
  · exact pivotal_twist_finite_of_balancing C p hbalance
  · exact hbalance

end PropertyF.Ground.CentreModular
end
