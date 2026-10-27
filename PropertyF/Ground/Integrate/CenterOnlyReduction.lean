module
public import PropertyF.Ground.Integrate.FPConjugates
public import PropertyF.Ground.Integrate.OverlapReduction

/-! The final target follows from the centre and the overlap recurrence alone. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- The original category needs no spherical-structure premise: its FP
conjugate bounds follow from the self-dual fusion character. The actual
modular centre, finite-image transfer and overlap recurrence remain explicit
unproved premises of this reduction. -/
theorem target_of_center_and_overlap
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      ∃ (Z : BraidedFusionCategory.{v,max u v}) (p : Dimensions.PivotalStructure (C := Z.Obj)),
        p.IsSpherical ∧
        (∀ i, Modular.simpleDimension Z p i = (fpSimple Z i : ℂ)) ∧
        (Modular.categoricalS Z p).det ≠ 0 ∧
        globalDimension Z = (globalFPDimension C : ℂ) ^ 2 ∧
        (∀ y, (∀ x, Modular.categoricalS Z p x y =
          (fpSimple Z y : ℂ) * σ.symm (Modular.simpleDimension Z p x)) →
          ObjectPropertyF (simples Z y)) ∧
        (∀ y, ObjectPropertyF (simples Z y) → TwistedOverlapTrace Z p σ y)) :
    TargetStatement.{v,u} := by
  apply target_of_bounded_conjugates_and_witness
  · intro C _ _ σ
    exact positive_bounded_conjugates_of_fp C σ
  · intro C hPU hF σ a b _ _ _ hτ
    obtain ⟨b', hb', _, hb'eq⟩ := positive_bounded_conjugates_of_fp C σ.symm
    have hbEq : b' = b := Complex.ofReal_injective (hb'eq.symm.trans hτ)
    have hb : 0 < b := hbEq ▸ hb'
    obtain ⟨Z, q, hq, hqDim, hdet, hglobal, hZf, hOverlap⟩ := hCenter C hPU hF σ
    apply center_witness_of_categorical_modular_data Z q hq hqDim hdet
      (globalFPDimension C) b (lt_of_lt_of_le (by norm_num) (one_le_globalFPDimension C))
      hb hglobal σ hτ hZf
    intro y hyF d hσ hS
    exact rigidity_of_twisted_overlap Z q hqDim σ y hyF d hσ hS (hOverlap y hyF)

end PropertyF.Ground
