module
public import PropertyF.Ground.CentreModular.VafaRegular
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

@[expose] public noncomputable section
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
  induction n with
  | zero => simp [vafaUnitClass]
  | succ n ih => rw [pow_succ, vafaUnitClass_mul, ih, succ_nsmul]

end PropertyF.Ground.CentreModular
