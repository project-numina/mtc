module
public import MTC.Center.Induction.PivotalCentrality
public import MTC.CategoryTheory.Dimensions.DoubleDualPairing

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions MTC.PropertyF.Reduction

/-! # Centre fusion from a pivotal global dimension

The induced unit has the intrinsic dimension of the base even for a pivotal
structure which is not spherical. Consequently its nonvanishing suffices for
the existing centre semisimplicity construction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Center.Induction
universe v u
variable {C : BraidedFusionCategory.{v,u}}
attribute [local instance] Abelian.hasFiniteBiproducts

/-- For a pivotal fusion category the intrinsic squared norm is the product of
its right dimensions on a simple object and its right dual. -/
theorem squaredNorm_eq_pivotalDimension_mul_dual
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] :
    squaredNorm C X = pivotalDimension C p X * pivotalDimension C p (Xᘁ) := by
  rw [target_squaredNorm_choice_independent (p.iso X), leftQuantumTrace_eq_rightDual,
    ← pivotal_dual]
  simp [pivotalDimension, rightTrace_id]

/-- Dual pivotal dimensions on simple representatives are complex conjugates. -/
theorem pivotalDimension_simple_dual_conj
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) :
    pivotalDimension C p ((simples C i)ᘁ) = star (pivotalDimension C p (simples C i)) :=
  (pivotalDimension_iso p (rightDualLabelIso C i)).trans
    (fusion_character_dual_eq_conj (i₀ := unitIndex C)
      (fun i j k ↦ (fusionCoeff_dual_symmetry C i j k).symm)
      ((pivotalDimension_unitIndex C p).symm ▸ one_ne_zero)
      (pivotalDimension_character C p) i)

/-- The squared norm of a simple representative is the squared absolute
value of its pivotal dimension. -/
theorem squaredNorm_simple_eq_pivotalDimension_norm_sq
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) :
    squaredNorm C (simples C i) = ((‖pivotalDimension C p (simples C i)‖ ^ 2 : ℝ) : ℂ) := by
  let : Simple (simples C i) := simples_simple C i
  rw [squaredNorm_eq_pivotalDimension_mul_dual p, pivotalDimension_simple_dual_conj p]
  simpa only [Complex.ofReal_pow, Complex.star_def] using
    Complex.mul_conj' (pivotalDimension C p (simples C i))

/-- The global dimension is the sum of squared absolute values of the simple
pivotal dimensions; no sphericality is needed. -/
theorem globalDimension_eq_sum_pivotal_norm_sq
    (p : PivotalStructure (C := C.Obj)) :
    globalDimension C = ((∑ i : Fin (rank C), ‖pivotalDimension C p (simples C i)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [globalDimension, Complex.ofReal_sum, squaredNorm_simple_eq_pivotalDimension_norm_sq p]

/-- The intrinsic global dimension is the Hermitian squared length of the
simple pivotal dimension vector. -/
theorem globalDimension_eq_sum_pivotal_conj_mul
    (p : PivotalStructure (C := C.Obj)) :
    globalDimension C = ∑ i, star (pivotalDimension C p (simples C i)) *
      pivotalDimension C p (simples C i) := by
  simpa only [Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.mul_conj',
    Complex.star_def, mul_comm] using globalDimension_eq_sum_pivotal_norm_sq p

/-- In a pseudo-unitary category, every simple pivotal dimension attains its
Frobenius–Perron bound, for any pivotal structure. -/
theorem pivotalDimension_norm_eq_fp_of_pseudoUnitary
    (p : PivotalStructure (C := C.Obj)) (hpu : PseudoUnitary C)
    (i : Fin (rank C)) :
    ‖pivotalDimension C p (simples C i)‖ = fpSimple C i := by
  apply norm_saturation_of_pseudoUnitary (d := fun j ↦ pivotalDimension C p (simples C j))
    ?_ ?_ hpu i
  · intro j
    exact character_norm_le_fpSimple (C := C) (i₀ := unitIndex C)
      ((pivotalDimension_unitIndex C p).symm ▸ one_ne_zero)
      (pivotalDimension_character C p) j
  · exact squaredNorm_simple_eq_pivotalDimension_norm_sq p

/-- The intrinsic global dimension of a pivotal braided fusion category is nonzero. -/
theorem globalDimension_ne_zero_of_pivotal (p : PivotalStructure (C := C.Obj)) :
    globalDimension C ≠ 0 := by
  rw [globalDimension_eq_sum_pivotal_norm_sq p]
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  apply Finset.sum_pos' (fun i _ ↦ sq_nonneg ‖pivotalDimension C p (simples C i)‖)
  exact ⟨unitIndex C, Finset.mem_univ _, by simp [pivotalDimension_unitIndex]⟩

/-- The dimension of an induced underlying object is the global dimension of
the base times the dimension of the object. -/
theorem pivotalDimension_underlying (p : PivotalStructure (C := C.Obj)) (X : C.Obj) :
    pivotalDimension C p (underlying X) = globalDimension C * pivotalDimension C p X := by
  rw [globalDimension]
  simp only [underlying, pivotalDimension, rightDimension_biproduct,
    MTC.Fusion.unitScalar_eq_equiv, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  let : Simple (simples C i) := simples_simple C i
  rw [squaredNorm_eq_pivotalDimension_mul_dual p, ← MTC.Fusion.unitScalar_eq_equiv]
  change pivotalDimension C p (conjugate (simples C i) X) = _
  rw [pivotalDimension_tensor, pivotalDimension_tensor]
  simp only [pivotalDimension, unitScalar_eq_equiv]
  ring

/-- The induced unit has intrinsic global dimension, for any pivotal structure. -/
theorem pivotalDimension_underlying_unit (p : PivotalStructure (C := C.Obj)) :
    pivotalDimension C p (underlying (𝟙_ C.Obj)) = globalDimension C := by
  rw [pivotalDimension_underlying]
  have hu : pivotalDimension C p (𝟙_ C.Obj) = 1 := by
    simpa only [pivotalDimension_unitIndex] using
      (pivotalDimension_iso p (Classical.choice (unitIndex_iso C))).symm
  rw [hu, mul_one]

/-- A compatible pivotal lift gives fusion of the actual centre when the
intrinsic global dimension of the base is nonzero. -/
theorem center_fusion_of_compatible_pivotal_globalDimension_ne_zero
    [RigidCategory (Center C.Obj)] {p : PivotalStructure (C := C.Obj)}
    {pZ : PivotalStructure (C := Center C.Obj)}
    (hcompat : PivotalCompatibleAt p pZ ((induction C).obj (𝟙_ C.Obj)))
    (hne : globalDimension C ≠ 0) : IsFusionCategory (Center C.Obj) :=
  center_fusion_of_nonzero_induced_trace pZ fun hz => by
    have ht := forget_rightTraceWith hcompat (𝟙 _)
    change (pZ.rightTrace (𝟙 ((induction C).obj (𝟙_ C.Obj)))).asHom.f =
      (p.rightTrace (𝟙 (underlying (𝟙_ C.Obj)))).asHom at ht
    have hd := pivotalDimension_underlying_unit p
    change unitScalar C (p.rightTrace (𝟙 (underlying (𝟙_ C.Obj)))) = _ at hd
    rw [show p.rightTrace (𝟙 (underlying (𝟙_ C.Obj))) = 0 from
      End.ext (ht.symm.trans (congrArg (fun a => a.asHom.f) hz))] at hd
    apply hne
    simpa only [MTC.Fusion.unitScalar_eq_equiv, map_zero] using hd.symm

/-- Every pivotal braided fusion category has a fusion Drinfeld centre. -/
theorem center_fusion_of_pivotal [RigidCategory (Center C.Obj)]
    (p : PivotalStructure (C := C.Obj)) : IsFusionCategory (Center C.Obj) :=
  center_fusion_of_compatible_pivotal_globalDimension_ne_zero
    (liftedPivotalStructure_compatible (pivotalComponentsCentral_proved p) _) 
    (globalDimension_ne_zero_of_pivotal p)

end MTC.Center.Induction

namespace MTC.PropertyF.Pivotal
variable (C : BraidedFusionCategory.{v,u})
variable (p : PivotalStructure (C := C.Obj))

include p in
/-- The global dimension of a pivotal braided fusion category is bounded by
its global FP dimension. -/
theorem globalDimension_re_le_globalFPDimension :
    (globalDimension C).re ≤ globalFPDimension C := by
  rw [MTC.Center.Induction.globalDimension_eq_sum_pivotal_norm_sq p]
  simp only [Complex.ofReal_re, globalFPDimension]
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  exact character_norm_le_fpSimple (C := C) (i₀ := unitIndex C)
    ((pivotalDimension_unitIndex C p).symm ▸ one_ne_zero)
    (pivotalDimension_character C p) i

end MTC.PropertyF.Pivotal

namespace MTC.Center.Normalization
variable {C : BraidedFusionCategory.{v,u}}

/-- An FP-proportional S column and its Hermitian norm identity determine
the global dimension from the column scalar. -/
theorem globalDimension_eq_norm_sq_mul_fp_of_gram_column
    (p : PivotalStructure (C := C.Obj)) {j : Fin (rank C)}
    (hcol : ∀ i, MTC.Modular.categoricalS C p i j =
      pivotalDimension C p (simples C j) * (fpSimple C i : ℂ))
    (hgram : (∑ i, star (MTC.Modular.categoricalS C p i j) *
      MTC.Modular.categoricalS C p i j) = globalDimension C) :
    globalDimension C = ((‖pivotalDimension C p (simples C j)‖ ^ 2 : ℝ) : ℂ) *
      (globalFPDimension C : ℂ) := by
  rw [← hgram]
  change (∑ i, starRingEnd ℂ (MTC.Modular.categoricalS C p i j) *
    MTC.Modular.categoricalS C p i j) = _
  rw [fp_proportional_column_gram C _ _ hcol]
  congr 1
  simpa only [starRingEnd_apply, Complex.ofReal_pow] using
    (Complex.conj_mul' (pivotalDimension C p (simples C j)))

end MTC.Center.Normalization
end
