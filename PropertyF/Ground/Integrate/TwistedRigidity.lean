module
public import PropertyF.Ground.Integrate.ScalarTwistModular
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Calculus.PositiveWeights
public import PropertyF.Ground.Fusion.Agreement

/-! Reduce the Galois-column rigidity assertion to categorical overlap coherence. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
open scoped BigOperators
namespace PropertyF.Ground
universe v u

/-- The actual overlap trace recurrence on the σ-twist of a chosen simple. -/
def TwistedOverlapTrace (Z : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := Z.Obj))
    (σ : ℂ ≃+* ℂ) (y : Fin (rank Z)) : Prop :=
  ∀ (u : braidAlgebra (show (ScalarTwist.category Z σ).Obj from simples Z y) 1) k,
      actualBraidTrace (ScalarTwist.category Z σ) (show (ScalarTwist.category Z σ).Obj from simples Z y) (ScalarTwist.pivotal Z σ p)
          (overlapIndex 1 k) (overlapProduct (show (ScalarTwist.category Z σ).Obj from simples Z y) 1 u k) *
        (Dimensions.groundUnitScalarEquiv (ScalarTwist.category Z σ)
          ((ScalarTwist.pivotal Z σ p).rightTrace (𝟙 (show (ScalarTwist.category Z σ).Obj from simples Z y)))) ^ k =
      actualBraidTrace (ScalarTwist.category Z σ) (show (ScalarTwist.category Z σ).Obj from simples Z y) (ScalarTwist.pivotal Z σ p) 1 u ^ (k + 1)

set_option backward.isDefEq.respectTransparency false in
/-- For a positive pivotal category, all the dimension and scalar-twist
premises of categorical rigidity follow from actual fusion data. The sole
remaining braid-calculus premise is the displayed overlap trace recurrence. -/
theorem rigidity_of_twisted_overlap (Z : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := Z.Obj))
    (hdim : ∀ i, Modular.simpleDimension Z p i = (fpSimple Z i : ℂ))
    (σ : ℂ ≃+* ℂ) (y : Fin (rank Z))
    (hF : ObjectPropertyF (simples Z y)) (d : ℝ)
    (hσ : σ (fpSimple Z y : ℂ) = (d : ℂ))
    (hS : σ (Modular.categoricalS Z p y y) = (d : ℂ) * fpSimple Z y)
    (hrec : TwistedOverlapTrace Z p σ y) :
    fpSimple Z y = |d| := by
  let D := ScalarTwist.category Z σ
  let q := ScalarTwist.pivotal Z σ p
  let X : D.Obj := simples Z y
  letI : Simple X := simples_simple Z y
  obtain ⟨e, he⟩ := ScalarTwist.labels Z σ p
  let original : Fin (rank D) → ℝ := fun i => fpSimple Z (e.symm i)
  let transformed : Fin (rank D) → ℝ := fun i => (σ (original i : ℂ)).re
  have hreal (i : Fin (rank Z)) : (((σ (fpSimple Z i : ℂ)).re : ℝ) : ℂ) = σ (fpSimple Z i : ℂ) := by
    let χ : Fin (rank Z) → ℂ := fun i => (fpSimple Z i : ℂ)
    have hχ : χ (unitIndex Z) ≠ 0 := by simp [χ, fpSimple_unit]
    have hchar : ∀ i j, χ i * χ j = ∑ k, (fusionCoeff Z i j k : ℂ) * χ k := by
      intro i j
      dsimp [χ]
      exact_mod_cast fpSimple_mul Z i j
    have hdual : ∀ i, χ (dualIndex Z i) = χ i := by intro i; simp [χ, fpSimple_dual]
    apply Complex.conj_eq_iff_re.mp
    simpa only [← Complex.star_def] using selfDual_character_galois_real Z χ (unitIndex Z)
      hχ hchar hdual σ i
  have hpos : ∀ i, 0 < original i := fun i => fpSimple_pos Z _
  have htrans : ∀ i, σ (original i : ℂ) = (transformed i : ℂ) := by
    intro i
    exact (hreal (e.symm i)).symm
  have hqdim : ∀ i, Dimensions.groundUnitScalarEquiv D (q.rightTrace (𝟙 (simples D i))) =
      (transformed i : ℂ) := by
    intro i
    rw [Dimensions.groundUnitScalarEquiv_apply]
    change Dimensions.pivotalDimension D q (simples D i) = _
    have h := (he (e.symm i)).2
    rw [e.apply_symm_apply] at h
    rw [h]
    unfold transformed original
    rw [hreal]
    congr 1
    unfold Dimensions.pivotalDimension Modular.simpleDimension at *
    rw [unitScalar_eq_equiv]
    exact hdim _
  have hd : d ≠ 0 := by
    intro hz
    have hn : σ (fpSimple Z y : ℂ) ≠ 0 := (map_ne_zero σ).2 (by exact_mod_cast (ne_of_gt (fpSimple_pos Z y)))
    apply hn
    rw [hσ, hz]
    simp
  have hXdim : Dimensions.groundUnitScalarEquiv D (q.rightTrace (𝟙 X)) = (d : ℂ) := by
    change Dimensions.groundUnitScalarEquiv (ScalarTwist.category Z σ)
      ((ScalarTwist.pivotal Z σ p).rightTrace (𝟙 (show (ScalarTwist.category Z σ).Obj from simples Z y))) = _
    rw [ScalarTwist.rightTrace_twist Z σ p]
    rw [Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv]
    change σ (Modular.simpleDimension Z p y) = _
    rw [hdim, hσ]
  have hXfp : fpDimension D X = fpSimple Z y := by
    rw [ScalarTwist.fpDimension_twist, fpDimension_simple]
  have hXS : Dimensions.groundUnitScalarEquiv D (q.rightTrace (selfMonodromy X).asHom) =
      (d : ℂ) * fpSimple Z y := by
    change Dimensions.groundUnitScalarEquiv (ScalarTwist.category Z σ)
      ((ScalarTwist.pivotal Z σ p).rightTrace (selfMonodromy (show (ScalarTwist.category Z σ).Obj from simples Z y)).asHom) = _
    rw [ScalarTwist.rightTrace_twist Z σ p]
    rw [Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv]
    change σ (Modular.categoricalS Z p y y) = _
    exact hS
  exact actual_rigidity_of_overlap_and_galois_dimensions D X q original transformed σ
    hpos htrans hqdim d (fpSimple Z y) hd (fpSimple_pos Z y) hXdim hXfp hXS hF hrec

end PropertyF.Ground
