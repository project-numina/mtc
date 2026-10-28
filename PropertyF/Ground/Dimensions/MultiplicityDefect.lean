module
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Iso

/-! # Tensor defects and multiplicities

Natural fourth-dual roots induce operators on multiplicity spaces and satisfy involution identities.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Scalar comparing the chosen simple fourth-dual square root to the
braided double-dual component. -/
def fourthDualRootScalar (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) : ℂ := by
  let : Simple (simples C i) := simples_simple C i
  let : FiniteDimensional ℂ (simples C i ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  exact Classical.choose (isomorphisms_scalar (k := ℂ)
    (doubleDualIso C (simples C i)) (fourthDualSimpleRoot C i))

theorem fourthDualRootScalar_spec
    (i : Fin (rank C)) : fourthDualRootScalar C i ≠ 0 ∧
    (fourthDualSimpleRoot C i).hom = fourthDualRootScalar C i •
      (doubleDualIso C (simples C i)).hom :=
  letI : Simple (simples C i) := simples_simple C i
  letI : FiniteDimensional ℂ (simples C i ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  let h := Classical.choose_spec (isomorphisms_scalar (k := ℂ)
    (doubleDualIso C (simples C i)) (fourthDualSimpleRoot C i))
  ⟨h.1, h.2.1⟩

/-- The chosen simple square roots extend to a natural isomorphism from the
identity to the double-dual functor. It is not asserted to be monoidal. -/
def fourthDualRootNaturalIso (C : BraidedFusionCategory.{v,u}) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj :=
  simpleScalarNaturalIso C (fourthDualRootScalar C) (fun i => (fourthDualRootScalar_spec C i).1) ≪≫
    drinfeldNaturalIso C

/-- The natural extension has exactly the chosen simple components. -/
theorem fourthDualRootNaturalIso_app_simple
    (i : Fin (rank C)) :
    (fourthDualRootNaturalIso C).app (simples C i) = fourthDualSimpleRoot C i := by
  apply Iso.ext
  simp only [fourthDualRootNaturalIso, NatIso.trans_app, Iso.trans_hom,
    simpleScalarNaturalIso_app_simple]
  change (fourthDualRootScalar C i • 𝟙 (simples C i)) ≫
    (doubleDualIso C (simples C i)).hom = _
  simpa using (fourthDualRootScalar_spec C i).2.symm

/-- Natural transformations from the identity are determined by their
components on the simple representatives. -/
theorem natTrans_eq_of_simple_components
    {F : C.Obj ⥤ C.Obj} {α β : 𝟭 C.Obj ⟶ F}
    (h : ∀ i, α.app (simples C i) = β.app (simples C i)) : α = β := by
  apply NatTrans.ext
  funext X
  apply simpleInclusion_hom_ext C
  intro i t
  change simpleInclusion C X i t ≫ α.app X = simpleInclusion C X i t ≫ β.app X
  simpa only [Functor.id_map] using
    (α.naturality (simpleInclusion C X i t)).trans (by
      rw [h i]
      exact (β.naturality (simpleInclusion C X i t)).symm)

/-- The natural double-dual root, squared using the double-dual functor. -/
def fourthDualRootNaturalSquare (C : BraidedFusionCategory.{v,u}) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj ⋙ doubleDualFunctor C.Obj :=
  fourthDualRootNaturalIso C ≪≫
    Functor.isoWhiskerRight (fourthDualRootNaturalIso C) (doubleDualFunctor C.Obj)

/-- The natural double-dual root squares to the natural braided fourth-dual
isomorphism on every object. Monoidal compatibility remains a separate issue. -/
theorem fourthDualRootNaturalSquare_eq :
    fourthDualRootNaturalSquare C = fourthDualNaturalIso C := by
  apply Iso.ext
  apply natTrans_eq_of_simple_components C
  intro i
  change ((fourthDualRootNaturalIso C).app (simples C i)).hom ≫
    ((((fourthDualRootNaturalIso C).app (simples C i)).homᘁ)ᘁ) =
      (fourthDualIso C (simples C i)).hom
  rw [fourthDualRootNaturalIso_app_simple]
  exact congrArg Iso.hom (fourthDualSimpleRoot_sq C i)

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
namespace PropertyF.Ground.Dimensions

section
variable {k : Type*} [Field k] [NeZero (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V] {T : V →ₗ[k] V}

/-- The positive spectral projection of an involution is idempotent. -/
theorem involution_half_projection (hT : T * T = 1) :
    IsIdempotentElem ((2 : k)⁻¹ • (1 + T)) := by
  have hinv (x : V) : T (T x) = x := congrArg (fun f : V →ₗ[k] V ↦ f x) hT
  let P : V →ₗ[k] V := (2 : k)⁻¹ • (1 + T)
  change P * P = P
  ext x
  change P (P x) = P x
  simp only [P, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    map_smul, map_add, hinv, smul_add, smul_smul]
  match_scalars <;> field_simp <;> ring

variable [FiniteDimensional k V]

/-- The trace of an involution is the difference of its positive and
negative eigenspace dimensions. This is the finite-dimensional ingredient in
ENO's trace matrices. -/
theorem involution_trace_formula (hT : T * T = 1) :
    ∃ m : ℕ, m ≤ Module.finrank k V ∧
      LinearMap.trace k V T = 2 * (m : k) - (Module.finrank k V : k) := by
  let P : V →ₗ[k] V := (2 : k)⁻¹ • (1 + T)
  have htp := congrArg (LinearMap.trace k V)
    (show (2 : k) • P = 1 + T by simp [P, smul_smul, NeZero.ne (2 : k)])
  rw [map_smul, map_add, smul_eq_mul,
    (LinearMap.IsIdempotentElem.isProj_range P (involution_half_projection hT)).trace,
    show LinearMap.trace k V (1 : V →ₗ[k] V) = _ from LinearMap.trace_id k V] at htp
  exact ⟨Module.finrank k (LinearMap.range P), (LinearMap.range P).finrank_le, by
    linear_combination -htp⟩

/-- The trace of an involution is an integer whose absolute value is at most
the dimension of its underlying vector space. -/
theorem involution_trace_integer_bound (hT : T * T = 1) :
    ∃ n : ℤ, LinearMap.trace k V T = (n : k) ∧
      |n| ≤ (Module.finrank k V : ℤ) :=
  (involution_trace_formula hT).elim fun m ⟨hm, htrace⟩ ↦
    ⟨2 * (m : ℤ) - (Module.finrank k V : ℤ), by simpa using htrace, by
      rw [abs_le]
      omega⟩

omit [NeZero (2 : k)] in
/-- An involution whose trace reaches the dimension is the identity. -/
theorem involution_eq_one_of_trace_eq_finrank [CharZero k] (hT : T * T = 1)
    (htrace : LinearMap.trace k V T = (Module.finrank k V : k)) : T = 1 := by
  let Q : V →ₗ[k] V := (2 : k)⁻¹ • (1 - T)
  have hq : IsIdempotentElem Q := by
    simpa [Q, sub_eq_add_neg] using involution_half_projection (T := -T) (by simpa using hT)
  have hzero : Q = 0 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff hq).mp (by simp [Q, htrace])
  exact (sub_eq_zero.mp (by
    simpa [hzero] using (show (2 : k) • Q = 1 - T by simp [Q, smul_smul]).symm)).symm


end

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {T : V →ₗ[ℂ] V}
variable [FiniteDimensional ℂ V]

/-- The trace of a complex involution is real. -/
theorem star_involution_trace (hT : T * T = 1) :
    star (LinearMap.trace ℂ V T) = LinearMap.trace ℂ V T :=
  (involution_trace_integer_bound hT).elim fun _ ⟨hn, _⟩ ↦ by simp [hn]

variable (hT : T * T = 1) {c : ℂ} (hc : ‖c‖ = 1)
  (htrace : LinearMap.trace ℂ V T * c = (Module.finrank ℂ V : ℂ))
include hT hc htrace

/-- A phase-scaled involution with maximal trace is the identity. -/
theorem involution_phase_eq_one_of_trace :
    c • T = 1 := by
  by_cases hz : Module.finrank ℂ V = 0
  · let : Subsingleton V := Module.finrank_zero_iff.mp hz
    ext x
    exact Subsingleton.elim _ _
  have ht : LinearMap.trace ℂ V T ≠ 0 := left_ne_zero_of_mul
    (htrace ▸ (by exact_mod_cast hz : (Module.finrank ℂ V : ℂ) ≠ 0))
  have htr : (starRingEnd ℂ) (LinearMap.trace ℂ V T) = LinearMap.trace ℂ V T :=
    star_involution_trace hT
  have hconj := congrArg (starRingEnd ℂ) htrace
  simp only [map_mul, map_natCast, htr] at hconj
  have hcconj : (starRingEnd ℂ) c = c := mul_left_cancel₀ ht (hconj.trans htrace.symm)
  have hc2 : c * c = 1 := by simpa [hcconj, hc] using Complex.mul_conj' c
  apply involution_eq_one_of_trace_eq_finrank (by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hT, hc2, one_smul])
  rw [map_smul, smul_eq_mul, mul_comm, htrace]

/-- The inverse phase also turns a maximal-trace involution into identity. -/
theorem involution_phase_inv_eq_one_of_trace :
    c⁻¹ • T = 1 := by
  have hs : T = c • (1 : V →ₗ[ℂ] V) := by
    simpa [smul_mul_assoc, hT] using
      (congrArg (fun F ↦ F * T) (involution_phase_eq_one_of_trace hT hc htrace)).symm
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  rw [hs, smul_smul, inv_mul_cancel₀ hc0, one_smul]


end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground.Dimensions
universe v u

/-- If two isomorphisms into a functor have the same functorial square, and
one is a component of a natural isomorphism from the identity, their ratio is
an involution. -/
theorem natural_square_defect_involution {C : Type u} [Category.{v} C]
    (F : C ⥤ C) (a : 𝟭 C ≅ F) {X : C} (b : X ≅ F.obj X)
    (hsq : ((a.app X).hom ≫ F.map (a.app X).hom) = b.hom ≫ F.map b.hom) :
    let d := (a.app X) ≪≫ b.symm
    d.hom ≫ d.hom = 𝟙 X := by
  let d := (a.app X) ≪≫ b.symm
  change d.hom ≫ d.hom = 𝟙 X
  have hd : d.hom ≫ b.hom = (a.app X).hom := by simp [d, Category.assoc]
  have hc : b.hom ≫ F.map d.hom = d.hom ≫ b.hom := by
    apply (cancel_epi d.hom).1
    rw [← Category.assoc, hd]
    exact (a.hom.naturality d.hom).symm
  apply (cancel_mono (b.hom ≫ F.map b.hom)).1
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← hc]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [← Functor.map_comp, hd]
  slice_lhs 1 2 => rw [hd]
  rw [hsq]
  exact (Category.id_comp _).symm

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Tensoring the components of the natural square root gives another
isomorphism from a tensor product to its double dual. -/
def rootTensorIso (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    X ⊗ Y ≅ ((X ⊗ Y)ᘁ)ᘁ :=
  ((fourthDualRootNaturalIso C).app X ⊗ᵢ (fourthDualRootNaturalIso C).app Y) ≪≫
    doubleDualTensorIso X Y

/-- The defect of tensor compatibility of the chosen natural square root. -/
def rootTensorDefect (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    X ⊗ Y ≅ X ⊗ Y :=
  (fourthDualRootNaturalIso C).app (X ⊗ Y) ≪≫ (rootTensorIso C X Y).symm

/-- The actual operator on each fusion multiplicity space induced by the tensor
defect. Its involutivity requires the still-unproved tensor compatibility of
the fourth-dual isomorphism. -/
def multiplicityDefect (C : BraidedFusionCategory.{v,u})
    (i j k : Fin (rank C)) :
    (simples C k ⟶ simples C i ⊗ simples C j) ≃ₗ[ℂ]
      (simples C k ⟶ simples C i ⊗ simples C j) :=
  Linear.homCongr ℂ (Iso.refl _) (rootTensorDefect C (simples C i) (simples C j))

/-- Each tensor-defect operator on a simple multiplicity space is an involution. -/
abbrev MultiplicityDefectsInvolutive (C : BraidedFusionCategory.{v,u}) : Prop :=
  ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
    (multiplicityDefect C i j k).toLinearMap = 1

/-- Scalar twisting makes each multiplicity-defect operator the identity. -/
abbrev ScaledMultiplicityDefectsTrivial (C : BraidedFusionCategory.{v,u})
    (c : Fin (rank C) → ℂ) : Prop :=
  ∀ i j k, (c k / (c i * c j)) • (multiplicityDefect C i j k).toLinearMap = 1

/-- The multiplicity operator is composition with the tensor defect. -/
theorem multiplicityDefect_apply
    {i j k : Fin (rank C)}
    (f : simples C k ⟶ simples C i ⊗ simples C j) :
    multiplicityDefect C i j k f =
      f ≫ (rootTensorDefect C (simples C i) (simples C j)).hom :=
  by simp [multiplicityDefect, Linear.homCongr_apply]

set_option backward.isDefEq.respectTransparency false in
/-- If the categorical multiplicity defect is involutive, its trace is an
integer bounded by the actual fusion coefficient. -/
theorem multiplicityDefect_trace_integer_bound {i j k : Fin (rank C)}
    (hinv : (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) :
    ∃ n : ℤ, LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap = (n : ℂ) ∧
      |n| ≤ (fusionCoeff C i j k : ℤ) :=
  letI : FiniteDimensional ℂ (simples C k ⟶ simples C i ⊗ simples C j) :=
    IsFusionCategory.hom_finite _ _
  involution_trace_integer_bound hinv

/-- If the tensor of the simple root components has the expected fourth-dual
square, the resulting tensor defect is an involution. -/
theorem rootTensorDefect_involution_of_tensor_square {X Y : C.Obj}
    (hsq : (rootTensorIso C X Y).hom ≫ (((rootTensorIso C X Y).homᘁ)ᘁ) =
      (fourthDualIso C (X ⊗ Y)).hom) :
    (rootTensorDefect C X Y).hom ≫ (rootTensorDefect C X Y).hom = 𝟙 (X ⊗ Y) :=
  natural_square_defect_involution (doubleDualFunctor C.Obj)
    (fourthDualRootNaturalIso C) (rootTensorIso C X Y)
    ((congrArg (fun n => (n.app (X ⊗ Y)).hom) (fourthDualRootNaturalSquare_eq C)).trans hsq.symm)

/-- The tensor-square comparison implies involutivity of every corresponding
actual multiplicity-space operator. -/
theorem multiplicityDefect_involution_of_tensor_square {i j : Fin (rank C)} (k : Fin (rank C))
    (hsq : (rootTensorIso C (simples C i) (simples C j)).hom ≫
      (((rootTensorIso C (simples C i) (simples C j)).homᘁ)ᘁ) =
        (fourthDualIso C (simples C i ⊗ simples C j)).hom) :
    (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1 := by
  ext f
  simp [multiplicityDefect_apply, Category.assoc,
    rootTensorDefect_involution_of_tensor_square C hsq]

set_option backward.isDefEq.respectTransparency false in
/-- Squaring the root tensor map gives the tensor of the fourth-dual maps,
with the canonical iterated double-dual tensor comparison. -/
theorem rootTensor_square_eq_fourthDual_tensor
    (X Y : C.Obj) :
    (rootTensorIso C X Y).hom ≫ (((rootTensorIso C X Y).homᘁ)ᘁ) =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ) := by
  have hx := congrArg (fun n => (n.app X).hom) (fourthDualRootNaturalSquare_eq C)
  have hy := congrArg (fun n => (n.app Y).hom) (fourthDualRootNaturalSquare_eq C)
  change ((fourthDualRootNaturalIso C).app X).hom ≫
    ((((fourthDualRootNaturalIso C).app X).homᘁ)ᘁ) = (fourthDualIso C X).hom at hx
  change ((fourthDualRootNaturalIso C).app Y).hom ≫
    ((((fourthDualRootNaturalIso C).app Y).homᘁ)ᘁ) = (fourthDualIso C Y).hom at hy
  rw [← hx, ← hy]
  simp only [rootTensorIso, Iso.trans_hom, tensorIso_hom, comp_rightAdjointMate,
    Category.assoc]
  slice_lhs 2 3 => rw [← doubleDualTensorIso_natural]
  simp only [doubleDualFunctor, Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]

/-- The fourth-dual isomorphism is compatible with tensoring two objects. -/
abbrev fourthDualTensorLaw (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) : Prop :=
  (fourthDualIso C (X ⊗ Y)).hom =
    ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
      (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
        (((doubleDualTensorIso X Y).homᘁ)ᘁ)


end PropertyF.Ground.Dimensions

end
