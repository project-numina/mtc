module
public import PropertyF.Ground.Integrate.CenterReduction
public import PropertyF.Ground.Integrate.TwistedRigidity

/-! Final reduction with the remaining overlap identity stated categorically. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- Canonical spherical existence, centre data, finite-image transfer and the
actual overlap recurrence imply the frozen target. All four categorical
assertions remain explicit premises of this intermediate theorem. -/
theorem target_of_canonical_spherical_center_and_overlap
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
        (∀ y, ObjectPropertyF (simples Z y) → TwistedOverlapTrace Z p σ y)) :
    TargetStatement.{v,u} := by
  apply target_of_canonical_spherical_and_center hCanonical
  intro C hPU hF σ
  obtain ⟨Z, p, hp, hdim, hdet, hglobal, hZF, hOverlap⟩ := hCenter C hPU hF σ
  refine ⟨Z, p, hp, hdim, hdet, hglobal, hZF, ?_⟩
  intro y hyF d hσ hS
  exact rigidity_of_twisted_overlap Z p hdim σ y hyF d hσ hS (hOverlap y hyF)

end PropertyF.Ground
