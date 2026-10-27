module
public import PropertyF.Ground.Integrate.CenterReductionComplete
public import PropertyF.Ground.Integrate.CenterFiniteImage

/-! Expose the remaining centre inputs in the final reduction. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- The target follows from the actual centre and the three categorical
centralizer facts in the paper. These facts are explicit interim premises;
no old hypothesis structure appears in the dependency cone. -/
theorem target_of_center_centralizers
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      ∃ (Z : BraidedFusionCategory.{v,max u v}) (p : Dimensions.PivotalStructure (C := Z.Obj))
        (core generated : Set (Fin (rank Z))),
        p.IsSpherical ∧
        (∀ i, Modular.simpleDimension Z p i = (fpSimple Z i : ℂ)) ∧
        (Modular.categoricalS Z p).det ≠ 0 ∧
        globalDimension Z = (globalFPDimension C : ℂ) ^ 2 ∧
        (∀ x ∈ core, ∃ z : ℤ, Modular.simpleDimension Z p x = z) ∧
        (∀ y, (∀ x ∈ core, Modular.categoricalS Z p x y =
          Modular.simpleDimension Z p x * Modular.simpleDimension Z p y) → y ∈ generated) ∧
        (∀ y ∈ generated, ObjectPropertyF (simples Z y))) : TargetStatement.{v,u} := by
  apply target_of_modular_center
  intro C hPU hF σ
  obtain ⟨Z, p, core, generated, hp, hdim, hdet, hglobal, hIntegral, hDouble, hFinite⟩ :=
    hCenter C hPU hF σ
  refine ⟨Z, p, hp, hdim, hdet, hglobal, ?_⟩
  intro y hColumn
  apply propertyF_of_galois_column Z p σ.symm core generated hIntegral hDouble hFinite y
  intro x
  rw [hdim y]
  exact hColumn x

end PropertyF.Ground
