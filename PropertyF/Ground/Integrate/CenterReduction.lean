module
public import PropertyF.Ground.Integrate.Reduction
public import PropertyF.Ground.Integrate.ModularWitness

/-! Reduction of the frozen target to the canonical spherical structure and
concrete centre/finite-braid assertions. Every premise below is explicit; no
old assumption bundle is used. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- A positive spherical structure on the original category and an actual
modular centre with the specified finite-image and rigidity properties imply
the target. The existence assertions remain unproved categorical premises. -/
theorem target_of_canonical_spherical_and_center
    (hCanonical : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      ∃ p : Dimensions.PivotalStructure (C := C.Obj), p.IsSpherical ∧
        ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      ∃ (Z : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := Z.Obj)),
        p.IsSpherical ∧
        (∀ i, Modular.simpleDimension Z p i = (fpSimple Z i : ℂ)) ∧
        (Modular.categoricalS Z p).det ≠ 0 ∧
        globalDimension Z = (globalFPDimension C : ℂ) ^ 2 ∧
        (∀ y, (∀ x, Modular.categoricalS Z p x y =
          (fpSimple Z y : ℂ) * σ.symm (Modular.simpleDimension Z p x)) →
          ObjectPropertyF (simples Z y)) ∧
        (∀ y, ObjectPropertyF (simples Z y) → ∀ d : ℝ,
          σ (fpSimple Z y : ℂ) = (d : ℂ) →
          σ (Modular.categoricalS Z p y y) = (d : ℂ) * fpSimple Z y →
          fpSimple Z y = |d|)) :
    TargetStatement.{v,u} := by
  apply target_of_canonical_spherical_and_witness hCanonical
  intro C hPU hF σ a b _ _ _ hτ
  obtain ⟨p, hp, hdim⟩ := hCanonical C hPU
  have hdual := Dimensions.spherical_dimension_dual_of_positive C p hp
    (fpSimple C) hdim (fpSimple_pos C)
  obtain ⟨b', hb', _, hb'eq⟩ :=
    positive_bounded_conjugates_of_spherical C hPU p hp hdual σ.symm
  have hbEq : b' = b := Complex.ofReal_injective (hb'eq.symm.trans hτ)
  have hb : 0 < b := hbEq ▸ hb'
  obtain ⟨Z, q, hq, hqDim, hdet, hglobal, hZf, hRigid⟩ := hCenter C hPU hF σ
  exact center_witness_of_categorical_modular_data Z q hq hqDim hdet
    (globalFPDimension C) b (lt_of_lt_of_le (by norm_num) (one_le_globalFPDimension C))
    hb hglobal σ hτ hZf hRigid

end PropertyF.Ground
