module
public import PropertyF.Ground.Fusion.Agreement

/-! Frobenius–Perron dimension of an arbitrary object. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace PropertyF.Ground

variable (D : BraidedFusionCategory)
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The positive character evaluated on the simple multiplicities of an object. -/
def fpDimension (D : BraidedFusionCategory) (X : D.Obj) : ℝ :=
  ∑ i, (Module.finrank ℂ (simples D i ⟶ X) : ℝ) * fpSimple D i

theorem fpDimension_simple (j : Fin (rank D)) :
    fpDimension D (simples D j) = fpSimple D j := by
  classical
  simp [fpDimension, finrank_simples_hom]

theorem fpDimension_iso {X Y : D.Obj} (e : X ≅ Y) :
    fpDimension D X = fpDimension D Y := by
  unfold fpDimension
  apply Finset.sum_congr rfl
  intro i _
  rw [(CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq]

theorem fpDimension_nonneg (X : D.Obj) :
    0 ≤ fpDimension D X := by
  unfold fpDimension
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (fpSimple_pos D i).le)

theorem fpDimension_unit : fpDimension D (𝟙_ D.Obj) = 1 := by
  obtain ⟨e⟩ := unitIndex_iso D
  rw [← fpDimension_iso D e, fpDimension_simple, fpSimple_unit]

/-- A nonzero object has a nonzero simple multiplicity. -/
theorem exists_positive_multiplicity {X : D.Obj}
    (hX : ¬ IsZero X) : ∃ i, 0 < Module.finrank ℂ (simples D i ⟶ X) := by
  classical
  have hid : (𝟙 X : X ⟶ X) ≠ 0 := by simpa [IsZero.iff_id_eq_zero] using hX
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  let V : (Σ i, Fin (m i)) → D.Obj := fun p => simples D p.1
  have he : e.hom ≠ 0 := by
    intro h
    apply hid
    simpa using (congrArg (fun t => t ≫ e.inv) h)
  have hp : ∃ p, e.hom ≫ biproduct.π V p ≠ 0 := by
    by_contra h
    push Not at h
    apply he
    apply biproduct.hom_ext
    intro p
    simpa using h p
  obtain ⟨p, hp⟩ := hp
  let : FiniteDimensional ℂ (X ⟶ simples D p.1) := IsFusionCategory.hom_finite _ _
  refine ⟨p.1, ?_⟩
  rw [← finrank_to_simple_eq_from_simple D X p.1]
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hp⟩

/-- Every nonzero object has FP dimension at least one. -/
theorem one_le_fpDimension {X : D.Obj}
    (hX : ¬ IsZero X) : 1 ≤ fpDimension D X := by
  classical
  obtain ⟨i, hi⟩ := exists_positive_multiplicity D hX
  have hcoeff : (1 : ℝ) ≤ Module.finrank ℂ (simples D i ⟶ X) := by exact_mod_cast hi
  have hterm : (1 : ℝ) ≤
      (Module.finrank ℂ (simples D i ⟶ X) : ℝ) * fpSimple D i := by
    nlinarith [one_le_fpSimple D i]
  unfold fpDimension
  exact hterm.trans (Finset.single_le_sum
    (f := fun j => (Module.finrank ℂ (simples D j ⟶ X) : ℝ) * fpSimple D j)
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (fpSimple_pos D j).le) (Finset.mem_univ i))

/-- Hom multiplicities of a tensor product are the convolution of the
multiplicities of its factors with the fusion coefficients. -/
theorem tensor_multiplicity_expanded (X Y : D.Obj)
    (k : Fin (rank D)) :
    Module.finrank ℂ (simples D k ⟶ X ⊗ Y) =
      ∑ i, ∑ j, Module.finrank ℂ (simples D i ⟶ X) *
        Module.finrank ℂ (simples D j ⟶ Y) * fusionCoeff D i j k := by
  classical
  have he (j : Fin (rank D)) : Module.finrank ℂ (simples D k ⟶ X ⊗ simples D j) =
      ∑ i, Module.finrank ℂ (simples D i ⟶ X) * fusionCoeff D i j k := by
    rw [(CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (β_ X (simples D j))).finrank_eq,
      tensor_multiplicity]
    change (∑ i, Module.finrank ℂ (simples D i ⟶ X) * fusionCoeff D j i k) = _
    simp_rw [fusionCoeff_comm D j]
  rw [tensor_multiplicity]
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- FP dimension is multiplicative on tensor products. -/
theorem fpDimension_tensor (X Y : D.Obj) :
    fpDimension D (X ⊗ Y) = fpDimension D X * fpDimension D Y := by
  classical
  unfold fpDimension
  simp_rw [tensor_multiplicity_expanded, Nat.cast_sum, Nat.cast_mul]
  calc
    _ = ∑ i, ∑ j, (Module.finrank ℂ (simples D i ⟶ X) : ℝ) *
        (Module.finrank ℂ (simples D j ⟶ Y) : ℝ) *
        (∑ k, (fusionCoeff D i j k : ℝ) * fpSimple D k) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ i, ∑ j, (Module.finrank ℂ (simples D i ⟶ X) : ℝ) *
        (Module.finrank ℂ (simples D j ⟶ Y) : ℝ) *
        (fpSimple D i * fpSimple D j) := by
      simp_rw [← fpSimple_mul]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Multiplicity of a simple in a dual object equals the multiplicity of its
dual in the original object. -/
theorem dual_multiplicity (X : D.Obj) (i : Fin (rank D)) :
    Module.finrank ℂ (simples D i ⟶ ᘁX) =
      Module.finrank ℂ (simples D (dualIndex D i) ⟶ X) := by
  obtain ⟨e⟩ := dualIndex_iso D i
  calc
    _ = Module.finrank ℂ (simples D i ⟶ (ᘁX) ⊗ 𝟙_ D.Obj) :=
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (ρ_ (ᘁX : D.Obj)).symm).finrank_eq
    _ = Module.finrank ℂ (X ⊗ simples D i ⟶ 𝟙_ D.Obj) :=
      (tensorLeftHomLinearEquiv (simples D i) (ᘁX) X (𝟙_ D.Obj)).finrank_eq.symm
    _ = Module.finrank ℂ (simples D i ⊗ X ⟶ 𝟙_ D.Obj) :=
      (CategoryTheory.Linear.homCongr ℂ (β_ X (simples D i)) (Iso.refl _)).finrank_eq
    _ = Module.finrank ℂ (X ⟶ (ᘁ(simples D i)) ⊗ 𝟙_ D.Obj) :=
      (tensorLeftHomLinearEquiv X (ᘁ(simples D i)) (simples D i) (𝟙_ D.Obj)).finrank_eq
    _ = Module.finrank ℂ (X ⟶ ᘁ(simples D i)) :=
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (ρ_ (ᘁ(simples D i) : D.Obj))).finrank_eq
    _ = Module.finrank ℂ (X ⟶ simples D (dualIndex D i)) :=
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq
    _ = _ := finrank_to_simple_eq_from_simple D X _

/-- FP dimension is invariant under taking a left dual. -/
theorem fpDimension_leftDual (X : D.Obj) :
    fpDimension D (ᘁX) = fpDimension D X := by
  classical
  unfold fpDimension
  simp_rw [dual_multiplicity]
  calc
    _ = ∑ i, (Module.finrank ℂ (simples D (dualIndex D i) ⟶ X) : ℝ) *
        fpSimple D (dualIndex D i) := by simp_rw [fpSimple_dual]
    _ = _ := Equiv.sum_comp (dualEquiv D)
      (fun i => (Module.finrank ℂ (simples D i ⟶ X) : ℝ) * fpSimple D i)

/-- FP dimension is invariant under taking a right dual. -/
theorem fpDimension_rightDual (X : D.Obj) :
    fpDimension D (Xᘁ) = fpDimension D X := by
  let e : (ᘁX : D.Obj) ≅ Xᘁ :=
    leftDualIso inferInstance (BraidedCategory.exactPairing_swap X (Xᘁ))
  rw [← fpDimension_iso D e, fpDimension_leftDual]

end PropertyF.Ground
