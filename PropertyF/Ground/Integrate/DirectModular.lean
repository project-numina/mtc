module
public import PropertyF.Ground.Integrate.CenterReductionComplete

/-! The non-degenerate special case needs no Drinfeld centre. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- A positive spherical modular category with property F is weakly integral.
This proves the non-degenerate special case directly, without constructing a
centre. Existence of the positive spherical structure is an explicit premise. -/
theorem weaklyIntegral_of_positive_modular_propertyF
    (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (hdet : (Modular.categoricalS C p).det ≠ 0)
    (hF : HasPropertyF C.Obj) : WeaklyIntegral (globalFPDimension C) := by
  apply weaklyIntegral_of_globalFPDimension_fixed C
  intro σ
  obtain ⟨a, _, hale, ha⟩ := positive_bounded_conjugates_of_fp C σ
  have hreal : ∀ j, starRingEnd ℂ (Modular.simpleDimension C p j) =
      Modular.simpleDimension C p j := by
    intro j
    rw [hdim]
    simp
  obtain ⟨act, _, hcolumn, hself, hglobalAct⟩ :=
    Modular.categoricalS_galois_symmetry C p hp hdet hreal
  let y := act σ.symm (unitIndex C)
  let f := fpSimple C y
  let χ : Fin (rank C) → ℂ := fun i => (fpSimple C i : ℂ)
  have hχ : χ (unitIndex C) ≠ 0 := by simp [χ, fpSimple_unit]
  have hchar : ∀ i j, χ i * χ j = ∑ k, (fusionCoeff C i j k : ℂ) * χ k := by
    intro i j
    dsimp [χ]
    exact_mod_cast fpSimple_mul C i j
  have hdual : ∀ i, χ (dualIndex C i) = χ i := by
    intro i
    simp [χ, fpSimple_dual]
  have hreal' : (((σ (f : ℂ)).re : ℝ) : ℂ) = σ (f : ℂ) := by
    apply Complex.conj_eq_iff_re.mp
    simpa only [← Complex.star_def] using selfDual_character_galois_real C χ (unitIndex C)
      hχ hchar hdual σ y
  let d := (σ (f : ℂ)).re
  have hσf : σ (f : ℂ) = (d : ℂ) := hreal'.symm
  have hS : Modular.categoricalS C p y y = (f : ℂ) * σ.symm (f : ℂ) := by
    have h := hcolumn σ.symm y
    rw [hdim] at h
    exact h
  have hf : 1 ≤ f := one_le_fpSimple C y
  have hrigid : f = |d| := by
    apply galois_rigidity C p hdim σ y (hF (simples C y)) d hσf
    exact galois_unit_self_entry σ hS hσf
  have hglobal : globalDimension C = (globalFPDimension C : ℂ) := by
    rw [Modular.categorical_global_eq_sum_squares C p hp]
    simp only [hdim, globalFPDimension]
    push_cast
    rfl
  have hG := hglobalAct σ.symm
  rw [hglobal, hdim] at hG
  have hG' := congrArg σ hG
  simp only [σ.apply_symm_apply, map_div₀, map_pow, ha] at hG'
  change (globalFPDimension C : ℂ) = (a : ℂ) / σ (f : ℂ) ^ 2 at hG'
  rw [hσf] at hG'
  have hdne : d ≠ 0 := by
    have : 1 ≤ |d| := hrigid ▸ hf
    exact abs_ne_zero.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one this))
  have hR : globalFPDimension C * d ^ 2 = a := by
    have h := (eq_div_iff (pow_ne_zero 2 (by exact_mod_cast hdne : (d : ℂ) ≠ 0))).mp hG'
    exact_mod_cast h
  have hδ : 0 < globalFPDimension C := lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)
  have hd : 1 ≤ d ^ 2 := by
    have := hrigid ▸ hf
    nlinarith [sq_abs d]
  have : a = globalFPDimension C := by nlinarith
  simpa [this] using ha

/-- A non-unit label with the transparent S-column forces degeneracy. This
explains why a subcategory with a nontrivial symmetric core cannot simply
replace the full modular category in the direct argument. -/
theorem categoricalS_det_eq_zero_of_transparent_column
    (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (y : Fin (rank C)) (hy : y ≠ unitIndex C)
    (hcolumn : ∀ x, Modular.categoricalS C p x y =
      Modular.simpleDimension C p x * Modular.simpleDimension C p y) :
    (Modular.categoricalS C p).det = 0 := by
  by_contra hdet
  apply hy
  apply Modular.categoricalS_character_injective C p hdet
  funext x
  dsimp only
  rw [hcolumn x, Modular.categoricalS_unit, Modular.simpleDimension_unit]
  simp [Modular.simpleDimension_ne_zero C p y]

end PropertyF.Ground
