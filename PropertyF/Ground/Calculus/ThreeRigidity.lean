module
public import PropertyF.BlockTrace
public import PropertyF.BraidAlgebra
public import PropertyF.Ground.Calculus.OverlapBound
public import PropertyF.Ground.Calculus.ThreeTrace

/-! The matrix saturation step of three-strand rigidity, without a model bundle. -/

open PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

/-- In explicit matrix blocks, a sharp trace bound and a saturating braid
force the squares of the two braid generators to coincide. The trace bound,
nonzero weights, and the trace value are explicit hypotheses, rather than a
hypothesis structure. -/
theorem braid_squares_equal_of_saturation (B : PropertyF.Blocks)
    (w : Fin B.count → ℝ) (a b : B.Algebraˣ) (d f : ℝ)
    (hf : 0 < f) (hw : ∀ r, w r ≠ 0)
    (ha : B.IsUnitary (a : B.Algebra)) (hb : B.IsUnitary (b : B.Algebra))
    (hbraid : a * b * a = b * a * b)
    (hbound : ∀ u : B.Algebra, B.IsUnitary u → ‖B.trace w u‖ ≤ |d| * f ^ 2)
    (htrace : B.trace w ((a ^ 2 * b ^ 2 : B.Algebraˣ) : B.Algebra) = (d : ℂ) * f ^ 2) :
    a ^ 2 = b ^ 2 := by
  have hunit : B.IsUnitary ((a ^ 2 * b ^ 2 : B.Algebraˣ) : B.Algebra) := by
    intro r
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Pi.mul_apply, Pi.pow_apply] using
      (Matrix.unitaryGroup (Fin (B.size r)) ℂ).mul_mem
        ((Matrix.unitaryGroup (Fin (B.size r)) ℂ).pow_mem (ha r) 2)
        ((Matrix.unitaryGroup (Fin (B.size r)) ℂ).pow_mem (hb r) 2)
  have hmass : B.mass w ≤ |d| * f ^ 2 := by
    have h := hbound (B.signElement w) (B.signElement_unitary w)
    rw [B.trace_signElement] at h
    have hm : 0 ≤ B.mass w :=
      Finset.sum_nonneg (fun r _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm] using h
  have hsaturate : ‖B.trace w ((a ^ 2 * b ^ 2 : B.Algebraˣ) : B.Algebra)‖ = B.mass w := by
    apply le_antisymm (B.norm_trace_le w hunit)
    rw [htrace]
    simpa [norm_pow, abs_of_pos hf] using hmass
  exact PropertyF.squares_eq_of_central_product a b hbraid
    (Units.ext (B.central_of_saturation w hw hunit hsaturate b))

end PropertyF.Ground.Calculus

/-! Apply the matrix saturation step to actual categorical braid blocks. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- The actual three-strand braid-image element has the categorical overlap
trace, independently of any choice of matrix blocks. -/
theorem actual_three_braid_trace (C : BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] (p : PivotalStructure (C := C.Obj)) :
    actualBraidTrace C X p 1 (groupInImage (braidEndRepresentation X 1)
      (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2)) =
      scalarTrace p (groundUnitScalarEquiv C) (selfMonodromy X) ^ 2 /
        pivotalDimension C p X := by
  simpa [actualBraidTrace, groupInImage_val, braidEndRepresentation,
    threeGeneratorLeft, threeGeneratorRight, imageGenerator, pivotalDimension, scalarTrace,
    ← groundUnitScalarEquiv_apply] using
    (three_braid_trace C X p (groundUnitScalarEquiv C))

/-- The modular self-entry identity makes the actual three-strand trace attain
the value used in the saturation argument. -/
theorem actual_three_braid_saturates (C : BraidedFusionCategory.{v,u})
    {X : C.Obj} [Simple X] (p : PivotalStructure (C := C.Obj))
    {d f : ℝ} (hd : d ≠ 0)
    (hdim : pivotalDimension C p X = (d : ℂ))
    (hS : scalarTrace p (groundUnitScalarEquiv C) (selfMonodromy X) =
      (d : ℂ) * f) :
    actualBraidTrace C X p 1 (groupInImage (braidEndRepresentation X 1)
      (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2)) = (d : ℂ) * f ^ 2 := by
  rw [actual_three_braid_trace C X p, hdim, hS]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp

set_option backward.isDefEq.respectTransparency false in
/-- Actual three-strand block generators have equal squares once their
categorical weighted trace has the sharp bound and saturates it at `a²b²`.
The remaining hypotheses are explicitly the trace weights and sharp bound. -/
theorem actual_braid_squares_equal_of_saturation
    (C : BraidedFusionCategory.{v,u}) {X : C.Obj}
    (p : PivotalStructure (C := C.Obj))
    {r : ℕ} {size : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] PropertyF.Blocks.Algebra ⟨_, size⟩)
    (he : IsUnitaryPresentation (braidEndRepresentation X 1) b)
    {w : Fin r → ℝ} (hw : ∀ i, w i ≠ 0) {d f : ℝ} (hf : 0 < f)
    (htrace : ∀ z : braidAlgebra X 1, actualBraidTrace C X p 1 z =
      (PropertyF.Blocks.mk r size).trace w (b z))
    (hbound : ∀ z : braidAlgebra X 1,
      (∀ i, b z i ∈ Matrix.unitaryGroup (Fin (size i)) ℂ) →
      ‖actualBraidTrace C X p 1 z‖ ≤ |d| * f ^ 2)
    (hvalue : actualBraidTrace C X p 1
      (groupInImage (braidEndRepresentation X 1)
        (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2)) = (d : ℂ) * f ^ 2) :
    tripleBlockLeft X b ^ 2 = tripleBlockRight X b ^ 2 := by
  let B : PropertyF.Blocks := ⟨r, size⟩
  let ρ : braidImage X 1 →* B.Algebra :=
    b.toMonoidHom.comp (groupInImage (braidEndRepresentation X 1))
  let a : B.Algebraˣ := ρ.toHomUnits (threeGeneratorLeft X)
  let c : B.Algebraˣ := ρ.toHomUnits (threeGeneratorRight X)
  have ha : B.IsUnitary (a : B.Algebra) := he _
  have hc : B.IsUnitary (c : B.Algebra) := he _
  have hbraid : a * c * a = c * a * c := by
    apply Units.ext
    exact three_braid_relation_map ρ
  have hbnd : ∀ z : B.Algebra, B.IsUnitary z → ‖B.trace w z‖ ≤ |d| * f ^ 2 := by
    intro z hz
    change ∀ i, z i ∈ Matrix.unitaryGroup (Fin (size i)) ℂ at hz
    have h := hbound (b.symm z) (by simpa only [b.apply_symm_apply] using hz)
    simpa [htrace, B] using h
  have hv : B.trace w ((a ^ 2 * c ^ 2 : B.Algebraˣ) : B.Algebra) = (d : ℂ) * f ^ 2 := by
    have h := htrace (groupInImage (braidEndRepresentation X 1)
      (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2))
    rw [hvalue] at h
    change B.trace w (b (groupInImage (braidEndRepresentation X 1) (threeGeneratorLeft X)) ^ 2 *
      b (groupInImage (braidEndRepresentation X 1) (threeGeneratorRight X)) ^ 2) = _
    rw [← map_pow, ← map_pow, ← map_mul]
    rw [map_mul, map_pow, map_pow] at h
    exact h.symm
  have h := braid_squares_equal_of_saturation B w a c d f hf hw ha hc hbraid hbnd hv
  have hh := congrArg (fun z : B.Algebraˣ => (z : B.Algebra)) h
  change b (groupInImage (braidEndRepresentation X 1) (threeGeneratorLeft X)) ^ 2 =
    b (groupInImage (braidEndRepresentation X 1) (threeGeneratorRight X)) ^ 2 at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
/-- Equal actual three-strand squares make the two adjacent copies of double
self-braiding equal in the conventional tensor-product parenthesization. -/
theorem local_monodromy_of_three_squares_equal
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear ℂ C] (X : C)
    (h : Aut.toEnd (braidGenerator X 1 0 ^ 2) = Aut.toEnd (braidGenerator X 1 1 ^ 2)) :
    insertRightIdentity (X ⊗ X) X (selfMonodromy X) =
      overlapFresh X X X (selfMonodromy X) := by
  have hh := congrArg (isoEndAlgEquiv (threePowerIso X)) h
  simp only [map_pow] at hh
  rw [threeGeneratorLeft_end_transport X, threeGeneratorRight_end_transport X] at hh
  apply (isoEndAlgEquiv (α_ X X X)).injective
  apply End.ext
  have hhom := congrArg End.asHom hh
  simpa [insertRightIdentity, overlapFresh, selfMonodromy, isoEndAlgEquiv,
    Iso.conj_apply_asHom, pow_two, End.mul_asHom, comp_whiskerRight,
    whiskerLeft_comp, Category.assoc] using hhom

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the actual block squares implies equality of the categorical
adjacent copies of double self-braiding. -/
theorem local_monodromy_of_block_squares_equal
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear ℂ C] {X : C} {r : ℕ} {size : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] PropertyF.Blocks.Algebra ⟨_, size⟩)
    (h : tripleBlockLeft X b ^ 2 = tripleBlockRight X b ^ 2) :
    insertRightIdentity (X ⊗ X) X (selfMonodromy X) =
      overlapFresh X X X (selfMonodromy X) := by
  apply local_monodromy_of_three_squares_equal X
  have hs : groupInImage (braidEndRepresentation X 1) (threeGeneratorLeft X ^ 2) =
      groupInImage (braidEndRepresentation X 1) (threeGeneratorRight X ^ 2) := by
    apply b.injective
    simpa [tripleBlockLeft, tripleBlockRight, map_pow] using h
  have hm := congrArg (fun z : braidAlgebra X 1 => (z : End (tensorPower X 3))) hs
  simpa [groupInImage_val, braidEndRepresentation, threeGeneratorLeft,
    threeGeneratorRight, imageGenerator] using hm

/-- If the same pair operator occurs on either adjacent pair, partial trace
forces that operator to be scalar. -/
theorem pair_operator_scalar_of_overlaps_equal
    (C : BraidedFusionCategory.{v,u}) {X : C.Obj} [Simple X]
    (p : PivotalStructure (C := C.Obj)) (u : End (X ⊗ X))
    {d f : ℝ} (hd : d ≠ 0)
    (hdim : pivotalDimension C p X = (d : ℂ))
    (htrace : scalarTrace p (groundUnitScalarEquiv C) u = (d : ℂ) * f)
    (heq : insertRightIdentity (X ⊗ X) X u = overlapFresh X X X u) :
    u = (f / d : ℂ) • (1 : End (X ⊗ X)) := by
  simp only [scalarTrace] at htrace
  simp only [pivotalDimension, ← groundUnitScalarEquiv_apply] at hdim
  have h := congrArg (rightPartialTrace p (X ⊗ X) X) heq
  rw [rightPartialTrace_insert p (groundUnitScalarEquiv C),
    overlapFresh, rightPartialTrace_whiskerLeft,
    rightPartialTrace_simple_ground C (X := X) (Y := X) p (groundUnitScalarEquiv C)] at h
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  simp only [scalarTrace, hdim, htrace] at h
  have h' : (d : ℂ) • u = (f : ℂ) • (1 : End (X ⊗ X)) := by
    have hdiv : (d : ℂ) * f / d = (f : ℂ) := by field_simp
    rw [hdiv] at h
    have hs : End.of (X ◁ ((f : ℂ) • (1 : End X)).asHom) =
        (f : ℂ) • (1 : End (X ⊗ X)) := by
      apply End.ext
      change X ◁ ((f : ℂ) • (𝟙 X)) = (f : ℂ) • (𝟙 (X ⊗ X))
      rw [MonoidalLinear.whiskerLeft_smul, whiskerLeft_id]
    rw [hs] at h
    exact h
  apply (smul_right_injective _ hd')
  change (d : ℂ) • u = (d : ℂ) • ((f / d : ℂ) • (1 : End (X ⊗ X)))
  rw [h', smul_smul]
  have hdiv : (d : ℂ) * (f / d) = (f : ℂ) := by field_simp
  rw [hdiv]

set_option backward.isDefEq.respectTransparency false in
/-- Finite categorical braid image gives finite order of the double
self-braiding on the ordinary tensor product. -/
theorem selfMonodromy_finite_order {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [BraidedCategory C] [Preadditive C] [Linear ℂ C]
    {X : C} (hfinite : ObjectPropertyF X) :
    ∃ n : ℕ, n ≠ 0 ∧ selfMonodromy X ^ n = 1 := by
  obtain ⟨n, hn, hpow⟩ := braid_square_finite_order hfinite
  have hgen : (isoEndAlgEquiv (twoPowerIso X)) (Aut.toEnd (braidGenerator X 0 0)) =
      End.of ((β_ X X).hom) := by
    apply End.ext
    exact twoGenerator_transport X
  have h := congrArg (fun z => (isoEndAlgEquiv (twoPowerIso X)) (Aut.toEnd z)) hpow
  simp only [map_pow, map_one, hgen] at h
  refine ⟨n, hn, ?_⟩
  have hs : (End.of ((β_ X X).hom) : End (X ⊗ X)) ^ 2 = selfMonodromy X := by
    apply End.ext
    simp [selfMonodromy, pow_two, End.mul_asHom]
  rw [← hs]
  exact h

/-- A scalar double self-braiding of finite order has unit-modulus scalar,
so the two real dimensions have equal absolute value. -/
theorem dimension_eq_abs_of_scalar_monodromy
    (C : BraidedFusionCategory.{v,u}) {X : C.Obj}
    (p : PivotalStructure (C := C.Obj))
    {d f : ℝ} (hd : d ≠ 0) (hf : 0 < f)
    (hdim : pivotalDimension C p X = (d : ℂ))
    (hfinite : ObjectPropertyF X)
    (hscalar : selfMonodromy X = (f / d : ℂ) • (1 : End (X ⊗ X))) : f = |d| := by
  simp only [pivotalDimension, ← groundUnitScalarEquiv_apply] at hdim
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hdim2 : groundUnitScalarEquiv C (p.rightTrace (𝟙 (X ⊗ X))) = (d : ℂ) ^ 2 := by
    have h := Dimensions.pivotalDimension_tensor C p X X
    simpa [Dimensions.pivotalDimension, ← groundUnitScalarEquiv_apply,
      hdim, pow_two] using h
  have hnonzero : (1 : End (X ⊗ X)) ≠ 0 := by
    intro h
    have ht := congrArg (fun z : End (X ⊗ X) =>
      groundUnitScalarEquiv C (p.rightTrace z.asHom)) h
    have hz : p.rightTrace (0 : X ⊗ X ⟶ X ⊗ X) = 0 := by
      simpa using p.rightTrace_smul (0 : ℂ) (𝟙 (X ⊗ X))
    have : (d : ℂ) ^ 2 = 0 := by
      simpa only [End.one_asHom, End.zero_asHom, hdim2, hz, map_zero] using ht
    exact (pow_ne_zero 2 hd') this
  obtain ⟨n, hn, hpow⟩ := selfMonodromy_finite_order hfinite
  apply PropertyF.fp_eq_abs_dim_of_finite_order hd hf
  refine ⟨n, hn, ?_⟩
  apply (smul_left_injective ℂ hnonzero)
  change ((f / d : ℂ) ^ n) • (1 : End (X ⊗ X)) = (1 : ℂ) • (1 : End (X ⊗ X))
  simpa [hscalar, smul_pow] using hpow

/-- Three-strand rigidity for a genuine braided pivotal fusion category,
reduced to explicit real, nonzero trace weights and the sharp unitary bound. -/
theorem actual_three_strand_rigidity_of_trace_bound
    (C : BraidedFusionCategory.{v,u}) {X : C.Obj} [Simple X]
    (p : PivotalStructure (C := C.Obj))
    {r : ℕ} {size : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] PropertyF.Blocks.Algebra ⟨_, size⟩)
    (he : IsUnitaryPresentation (braidEndRepresentation X 1) b)
    {w : Fin r → ℝ} (hw : ∀ i, w i ≠ 0)
    {d f : ℝ} (hd : d ≠ 0) (hf : 0 < f)
    (hdim : pivotalDimension C p X = (d : ℂ))
    (hS : scalarTrace p (groundUnitScalarEquiv C) (selfMonodromy X) =
      (d : ℂ) * f)
    (hfinite : ObjectPropertyF X)
    (htrace : ∀ z : braidAlgebra X 1, actualBraidTrace C X p 1 z =
      (PropertyF.Blocks.mk r size).trace w (b z))
    (hbound : ∀ z : braidAlgebra X 1,
      (∀ i, b z i ∈ Matrix.unitaryGroup (Fin (size i)) ℂ) →
      ‖actualBraidTrace C X p 1 z‖ ≤ |d| * f ^ 2) : f = |d| := by
  have hvalue := actual_three_braid_saturates C p hd hdim hS
  have hsq := actual_braid_squares_equal_of_saturation C p b he hw hf htrace hbound hvalue
  have hlocal := local_monodromy_of_block_squares_equal b hsq
  have hscalar := pair_operator_scalar_of_overlaps_equal C p (selfMonodromy X) hd hdim hS hlocal
  exact dimension_eq_abs_of_scalar_monodromy C p hd hf hdim hfinite hscalar

end PropertyF.Ground.Calculus
