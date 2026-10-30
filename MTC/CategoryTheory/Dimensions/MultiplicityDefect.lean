module
public import MTC.CategoryTheory.Dimensions.SimpleScalars
public import MTC.CategoryTheory.Dimensions.DualTensorNaturality
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Iso

/-! # Tensor defects and multiplicities

Chosen simple fourth-dual roots extend to a natural double-dual isomorphism.
Its tensor defect induces operators on multiplicity spaces. The module proves
involutivity criteria for those operators and the trace bounds for involutions
used in the ENO matrix argument.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts IsFusionCategory.hom_finite
local instance (i : Fin (rank C)) : Simple (simples C i) := simples_simple C i

/-- Scalar comparing the chosen simple fourth-dual square root to the
braided double-dual component. -/
def fourthDualRootScalar (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) : {c : ℂ // c ≠ 0 ∧
      (fourthDualSimpleRoot C i).hom = c • (doubleDualIso C (simples C i)).hom} :=
  Classical.indefiniteDescription _ (isomorphisms_scalar (k := ℂ)
    (doubleDualIso C (simples C i)) (fourthDualSimpleRoot C i))

/-- The chosen simple square roots extend to a natural isomorphism from the
identity to the double-dual functor. It is not asserted to be monoidal. -/
def fourthDualRootNaturalIso (C : BraidedFusionCategory.{v,u}) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj :=
  simpleScalarNaturalIso C (fun i ↦ (fourthDualRootScalar C i).1)
    (fun i ↦ (fourthDualRootScalar C i).2.1) ≪≫
    drinfeldNaturalIso C.Obj

/-- Natural transformations from the identity are determined on a family
whose finite biproducts contain every object. -/
theorem natTrans_eq_of_biproduct_components {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    [HasFiniteBiproducts D] {ι : Type} [Fintype ι] {T : ι → D}
    {F : D ⥤ D} {α β : 𝟭 D ⟶ F} (hdecomp : ∀ X, HasBiproductDecomposition T X)
    (h : ∀ i, α.app (T i) = β.app (T i)) : α = β :=
  NatTrans.ext <| funext fun X ↦ (hdecomp X).elim fun m ⟨e⟩ ↦
    biproduct_decomposition_hom_ext e fun ⟨i, t⟩ ↦ by
      let s := biproduct.ι (fun p : Σ i, Fin (m i) ↦ T p.1) ⟨i, t⟩ ≫ e.inv
      change s ≫ α.app X = s ≫ β.app X
      simpa only [Functor.id_map] using
        (α.naturality s).trans (by rw [h i]; exact (β.naturality s).symm)

/-- The natural double-dual root, squared using the double-dual functor. -/
def fourthDualRootNaturalSquare (C : BraidedFusionCategory.{v,u}) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj ⋙ doubleDualFunctor C.Obj :=
  fourthDualRootNaturalIso C ≪≫
    Functor.isoWhiskerRight (fourthDualRootNaturalIso C) (doubleDualFunctor C.Obj)

/-- The natural double-dual root squares to the natural braided fourth-dual
isomorphism on every object. Monoidal compatibility remains a separate issue. -/
theorem fourthDualRootNaturalSquare_eq :
    fourthDualRootNaturalSquare C = fourthDualNaturalIso C.Obj :=
  Iso.ext <| natTrans_eq_of_biproduct_components (simples_decompose C) fun i ↦ by
    change ((fourthDualRootNaturalIso C).app (simples C i)).hom ≫
      ((((fourthDualRootNaturalIso C).app (simples C i)).homᘁ)ᘁ) =
        (fourthDualIso (simples C i)).hom
    rw [show (fourthDualRootNaturalIso C).app (simples C i) = fourthDualSimpleRoot C i from
      Iso.ext <| by
        simp only [fourthDualRootNaturalIso, NatIso.trans_app, Iso.trans_hom,
          simpleScalarNaturalIso_app_simple]
        erw [Linear.smul_comp, Category.id_comp]
        exact (fourthDualRootScalar C i).2.2.symm]
    exact congrArg Iso.hom (Classical.choose_spec
      (exists_fourthDual_square_root (k := ℂ) (doubleDualIso C _) (fourthDualIso (simples C i))))

end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
namespace MTC.CategoryTheory.Dimensions

/-- An element is involutive when its square is one. -/
abbrev IsInvolutiveElem {M : Type*} [Monoid M] (a : M) : Prop := a * a = 1

section
variable {k : Type*} [Field k] [NeZero (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V] {T : V →ₗ[k] V}

/-- The positive spectral projection of an involution is idempotent. -/
theorem involution_half_projection (hT : IsInvolutiveElem T) :
    IsIdempotentElem ((2 : k)⁻¹ • (1 + T)) := LinearMap.ext fun x ↦ by
  have hinv : T (T x) = x := congrArg (fun f : V →ₗ[k] V ↦ f x) hT
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    map_smul, map_add, hinv, smul_add, smul_smul]
  match_scalars <;> field_simp <;> ring

variable [FiniteDimensional k V]

/-- The trace of an involution is the difference of its positive and
negative eigenspace dimensions. This is the finite-dimensional ingredient in
ENO's trace matrices. -/
theorem involution_trace_formula (hT : IsInvolutiveElem T) :
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
theorem involution_trace_integer_bound (hT : IsInvolutiveElem T) :
    ∃ n : ℤ, LinearMap.trace k V T = (n : k) ∧
      |n| ≤ (Module.finrank k V : ℤ) :=
  (involution_trace_formula hT).elim fun m ⟨hm, htrace⟩ ↦
    ⟨2 * (m : ℤ) - (Module.finrank k V : ℤ), by simpa using htrace,
      abs_le.mpr ⟨by omega, by omega⟩⟩

omit [NeZero (2 : k)] in
/-- An involution whose trace reaches the dimension is the identity. -/
theorem involution_eq_one_of_trace_eq_finrank [CharZero k] (hT : IsInvolutiveElem T)
    (htrace : LinearMap.trace k V T = (Module.finrank k V : k)) : T = 1 := by
  let Q : V →ₗ[k] V := (2 : k)⁻¹ • (1 - T)
  have hzero : Q = 0 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff (show IsIdempotentElem Q from by
    simpa [Q, sub_eq_add_neg] using involution_half_projection (T := -T) (by simpa [IsInvolutiveElem] using hT))).mp
      (by simp [Q, htrace])
  exact (sub_eq_zero.mp (by
    simpa [hzero] using (show (2 : k) • Q = 1 - T by simp [Q, smul_smul]).symm)).symm


end

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {T : V →ₗ[ℂ] V}
variable [FiniteDimensional ℂ V]

/-- The trace of a complex involution is real. -/
theorem star_involution_trace (hT : IsInvolutiveElem T) :
    star (LinearMap.trace ℂ V T) = LinearMap.trace ℂ V T :=
  (involution_trace_integer_bound hT).elim fun _ ⟨hn, _⟩ ↦ by simp [hn]

variable (hT : IsInvolutiveElem T) {c : ℂ} (hc : ‖c‖ = 1)
  (htrace : LinearMap.trace ℂ V T * c = (Module.finrank ℂ V : ℂ))
include hT hc htrace

/-- A phase-scaled involution with maximal trace is the identity. -/
theorem involution_phase_eq_one_of_trace :
    c • T = 1 := by
  by_cases hz : Module.finrank ℂ V = 0
  · let : Subsingleton V := Module.finrank_zero_iff.mp hz; exact Subsingleton.elim _ _
  have ht : LinearMap.trace ℂ V T ≠ 0 := left_ne_zero_of_mul (htrace ▸ Nat.cast_ne_zero.mpr hz)
  have hconj := congrArg (starRingEnd ℂ) htrace
  simp only [map_mul, map_natCast, show (starRingEnd ℂ) (LinearMap.trace ℂ V T) = _ from
    star_involution_trace hT] at hconj
  have hcconj : (starRingEnd ℂ) c = c := mul_left_cancel₀ ht (hconj.trans htrace.symm)
  have hc2 : c * c = 1 := by simpa [hcconj, hc] using Complex.mul_conj' c
  apply involution_eq_one_of_trace_eq_finrank (by
    simp [IsInvolutiveElem, smul_smul, hT, hc2])
  rw [map_smul, smul_eq_mul, mul_comm, htrace]

/-- The inverse phase also turns a maximal-trace involution into identity. -/
theorem involution_phase_inv_eq_one_of_trace :
    c⁻¹ • T = 1 := by
  have hs : T = c • (1 : V →ₗ[ℂ] V) := by
    simpa [smul_mul_assoc, hT] using
      (congrArg (fun F ↦ F * T) (involution_phase_eq_one_of_trace hT hc htrace)).symm
  rw [hs, smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mp (hc.symm ▸ one_ne_zero)), one_smul]


end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory
namespace MTC.CategoryTheory.Dimensions
universe v u

/-- An endomorphism is involutive when its square is the identity. -/
abbrev IsInvolutiveHom {C : Type u} [Category.{v} C] {X : C} (f : X ⟶ X) : Prop :=
  f ≫ f = 𝟙 X

/-- If two isomorphisms into a functor have the same functorial square, and
one is a component of a natural isomorphism from the identity, their ratio is
an involution. -/
theorem natural_square_defect_involution {C : Type u} [Category.{v} C]
    (F : C ⥤ C) (a : 𝟭 C ≅ F) {X : C} (b : X ≅ F.obj X)
    (hsq : ((a.app X).hom ≫ F.map (a.app X).hom) = b.hom ≫ F.map b.hom) :
    IsInvolutiveHom ((a.app X) ≪≫ b.symm).hom := by
  let d := (a.app X) ≪≫ b.symm
  have hd : d.hom ≫ b.hom = (a.app X).hom := by
    rw [show d.hom = (a.app X).hom ≫ b.inv from rfl, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hc : b.hom ≫ F.map d.hom = d.hom ≫ b.hom := by
    apply (cancel_epi d.hom).1
    rw [← Category.assoc, hd]
    exact (a.hom.naturality d.hom).symm
  apply (cancel_mono (b.hom ≫ F.map b.hom)).1
  simp only [Category.assoc]
  erw [← reassoc_of% hc, reassoc_of% hd, ← Functor.map_comp, hd, hsq, Category.id_comp]

end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Tensoring the components of the natural square root gives another
isomorphism from a tensor product to its double dual. -/
def rootTensorIso (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    X ⊗ Y ≅ ((X ⊗ Y)ᘁ)ᘁ :=
  ((fourthDualRootNaturalIso C).app X ⊗ᵢ (fourthDualRootNaturalIso C).app Y) ≪≫
    doubleDualTensorIso X Y

/-- The functorial square of the root tensor comparison. -/
abbrev rootTensorSquare (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :=
  (rootTensorIso C X Y).hom ≫ (((rootTensorIso C X Y).homᘁ)ᘁ)

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
  ∀ i j k, IsInvolutiveElem (multiplicityDefect C i j k).toLinearMap

/-- Scalar twisting makes each multiplicity-defect operator the identity. -/
abbrev ScaledMultiplicityDefectsTrivial (C : BraidedFusionCategory.{v,u})
    (c : Fin (rank C) → ℂ) : Prop :=
  ∀ i j k, (c k / (c i * c j)) • (multiplicityDefect C i j k).toLinearMap = 1

/-- The multiplicity operator is composition with the tensor defect. -/
theorem multiplicityDefect_apply {i j k : Fin (rank C)}
    (f : simples C k ⟶ simples C i ⊗ simples C j) :
    multiplicityDefect C i j k f =
      f ≫ (rootTensorDefect C (simples C i) (simples C j)).hom :=
  by simp [multiplicityDefect, Linear.homCongr_apply]

/-- If the tensor of the simple root components has the expected fourth-dual
square, the resulting tensor defect is an involution. -/
theorem rootTensorDefect_involution_of_tensor_square {X Y : C.Obj}
    (hsq : rootTensorSquare C X Y = (fourthDualIso (X ⊗ Y)).hom) :
    IsInvolutiveHom (rootTensorDefect C X Y).hom :=
  natural_square_defect_involution (doubleDualFunctor C.Obj)
    (fourthDualRootNaturalIso C) (rootTensorIso C X Y)
    ((congrArg (fun n => (n.app (X ⊗ Y)).hom) (fourthDualRootNaturalSquare_eq C)).trans hsq.symm)

/-- The tensor-square comparison implies involutivity of every corresponding
actual multiplicity-space operator. -/
theorem multiplicityDefect_involution_of_tensor_square {i j : Fin (rank C)} (k : Fin (rank C))
    (hsq : rootTensorSquare C (simples C i) (simples C j) =
      (fourthDualIso (simples C i ⊗ simples C j)).hom) :
    IsInvolutiveElem (multiplicityDefect C i j k).toLinearMap :=
  LinearMap.ext fun f ↦ by
    simp [multiplicityDefect_apply, Category.assoc,
      rootTensorDefect_involution_of_tensor_square C hsq]

set_option backward.isDefEq.respectTransparency false in
/-- Squaring the root tensor map gives the tensor of the fourth-dual maps,
with the canonical iterated double-dual tensor comparison. -/
theorem rootTensor_square_eq_fourthDual_tensor (X Y : C.Obj) :
    rootTensorSquare C X Y = ((fourthDualIso X).hom ⊗ₘ (fourthDualIso Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ) := by
  have hroot (Z : C.Obj) : ((fourthDualRootNaturalIso C).app Z).hom ≫
      ((((fourthDualRootNaturalIso C).app Z).homᘁ)ᘁ) = (fourthDualIso Z).hom :=
    congrArg (fun n ↦ (n.app Z).hom) (fourthDualRootNaturalSquare_eq C)
  rw [← hroot X, ← hroot Y]
  simp only [rootTensorSquare, rootTensorIso, Iso.trans_hom, tensorIso_hom, comp_rightAdjointMate,
    Category.assoc]
  rw [← reassoc_of% (doubleDualTensorIso_natural _ _), tensorHom_comp_tensorHom_assoc]
  rfl

end MTC.CategoryTheory.Dimensions

end
