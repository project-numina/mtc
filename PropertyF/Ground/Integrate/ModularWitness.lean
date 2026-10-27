module
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.Construction
public import PropertyF.Ground.Fusion.Agreement

/-! Extract the numerical ingredients of the paper's witness from an actual
spherical category with positive FP dimensions and invertible S matrix. -/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators
namespace PropertyF.Ground
universe v u

/-- The actual Galois-unit label supplies the modular dimension identity, its
self-column, a dimension at least one, and a real conjugate. This is independent
of the centre-specific realization and finite-braid rigidity. -/
theorem exists_modular_witness (Z : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := Z.Obj)) (hp : p.IsSpherical)
    (hdim : ∀ i, Modular.simpleDimension Z p i = (fpSimple Z i : ℂ))
    (hdet : (Modular.categoricalS Z p).det ≠ 0)
    (δ : ℝ) (hglobal : globalDimension Z = (δ : ℂ) ^ 2)
    (σ : ℂ ≃+* ℂ) :
    ∃ (y : Fin (rank Z)) (f d : ℝ), 1 ≤ f ∧
      σ (f : ℂ) = (d : ℂ) ∧ y = dualIndex Z y ∧
      (∀ x, Modular.categoricalS Z p x y =
        (f : ℂ) * σ.symm (Modular.simpleDimension Z p x)) ∧
      σ.symm ((δ : ℂ) ^ 2) = (δ : ℂ) ^ 2 / (f : ℂ) ^ 2 ∧
      Modular.categoricalS Z p y y = (f : ℂ) * σ.symm (f : ℂ) := by
  have hreal : ∀ j, starRingEnd ℂ (Modular.simpleDimension Z p j) =
      Modular.simpleDimension Z p j := by
    intro j
    rw [hdim]
    simp
  obtain ⟨act, _, hcolumn, hself, hglobalAct⟩ :=
    Modular.categoricalS_galois_symmetry Z p hp hdet hreal
  let y := act σ.symm (unitIndex Z)
  let f := fpSimple Z y
  let χ : Fin (rank Z) → ℂ := fun i => (fpSimple Z i : ℂ)
  have hχ : χ (unitIndex Z) ≠ 0 := by simp [χ, fpSimple_unit]
  have hchar : ∀ i j, χ i * χ j = ∑ k, (fusionCoeff Z i j k : ℂ) * χ k := by
    intro i j
    dsimp [χ]
    exact_mod_cast fpSimple_mul Z i j
  have hdual : ∀ i, χ (dualIndex Z i) = χ i := by
    intro i
    simp [χ, fpSimple_dual]
  have hreal' : (((σ (f : ℂ)).re : ℝ) : ℂ) = σ (f : ℂ) := by
    apply Complex.conj_eq_iff_re.mp
    simpa only [← Complex.star_def] using selfDual_character_galois_real Z χ (unitIndex Z)
      hχ hchar hdual σ y
  refine ⟨y, f, (σ (f : ℂ)).re, one_le_fpSimple Z y, hreal'.symm, hself σ.symm, ?_, ?_, ?_⟩
  · intro x
    have h := hcolumn σ.symm x
    rw [hdim] at h
    exact h
  · have h := hglobalAct σ.symm
    rw [hglobal, hdim] at h
    exact h
  · have h := hcolumn σ.symm y
    rw [hdim] at h
    exact h

end PropertyF.Ground
