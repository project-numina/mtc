module
public import MTC.CategoryTheory.BlockTrace
public import MTC.Braided.BraidAlgebra
public import MTC.Braided.Trace.OverlapBound
public import MTC.Braided.Trace.ThreeTrace

/-!
# Three-strand trace rigidity

Saturation of a unitary trace bound forces equality of braid squares. Partial trace
then identifies the monodromy scalar and its dimension consequences.
-/

open PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

/-- In explicit matrix blocks, a sharp trace bound and a saturating braid
force the squares of the two braid generators to coincide. The trace bound,
nonzero weights, and the trace value are explicit hypotheses, rather than a
hypothesis structure. -/
theorem braid_squares_equal_of_saturation (B : Blocks)
    (w : Fin B.count → ℝ) (a b : B.Algebraˣ) (d f : ℝ)
    (hf : 0 < f) (hw : ∀ r, w r ≠ 0)
    (ha : B.IsUnitary (a : B.Algebra)) (hb : B.IsUnitary (b : B.Algebra))
    (hbraid : a * b * a = b * a * b)
    (hbound : ∀ u : B.Algebra, B.IsUnitary u → ‖B.trace w u‖ ≤ |d| * f ^ 2)
    (htrace : B.trace w ((a ^ 2 * b ^ 2 : B.Algebraˣ) : B.Algebra) = (d : ℂ) * f ^ 2) :
    a ^ 2 = b ^ 2 :=
  let hunit : B.IsUnitary ((a ^ 2 * b ^ 2 : B.Algebraˣ) : B.Algebra) := by
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using
      (unitary B.Algebra).mul_mem ((unitary B.Algebra).pow_mem ha 2)
        ((unitary B.Algebra).pow_mem hb 2)
  squares_eq_of_central_product a b hbraid <| Units.ext <|
    B.central_of_saturation w hunit (le_antisymm (B.norm_trace_le w hunit) (by
      rw [htrace]
      simpa [norm_pow, abs_of_pos hf] using B.mass_le_of_unitary_trace_bound w hbound)) hw b

end PropertyF.Ground.Calculus

/-! Apply the matrix saturation step to actual categorical braid blocks. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

section LocalMonodromy

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]

omit [Preadditive C] [Linear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- Equal actual three-strand squares make the two adjacent copies of double
self-braiding equal in the conventional tensor-product parenthesization. -/
theorem local_monodromy_of_three_squares_equal (X : C)
    (h : Aut.toEnd (braidGenerator X 1 0 ^ 2) = Aut.toEnd (braidGenerator X 1 1 ^ 2)) :
    insertRightIdentity X (selfMonodromy X) = overlapFresh X (selfMonodromy X) :=
  (α_ X X X).conj.injective (End.ext (by
    have hh := congrArg (threePowerIso X).conj h
    simp only [map_pow] at hh
    rw [threeGeneratorLeft_end_transport X, threeGeneratorRight_end_transport X] at hh
    simpa [insertRightIdentity, overlapFresh, selfMonodromy, Iso.conj_apply_asHom, pow_two,
      End.mul_asHom, comp_whiskerRight, whiskerLeft_comp, Category.assoc] using congrArg End.asHom hh))

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the actual block squares implies equality of the categorical
adjacent copies of double self-braiding. -/
theorem local_monodromy_of_block_squares_equal {X : C} {r : ℕ} {size : Fin r → ℕ}
    (b : BraidBlockPresentation X 1 size)
    (h : tripleBlockLeft b ^ 2 = tripleBlockRight b ^ 2) :
    insertRightIdentity X (selfMonodromy X) = overlapFresh X (selfMonodromy X) :=
  local_monodromy_of_three_squares_equal X (by
    have hs : braidInImage (threeGeneratorLeft X ^ 2) =
        braidInImage (threeGeneratorRight X ^ 2) := b.injective (by
      simpa [tripleBlockLeft, tripleBlockRight, map_pow] using h)
    simpa [braidInImage_val, braidEndRepresentation, threeGeneratorLeft,
      threeGeneratorRight, imageGenerator] using
        congrArg (fun z : braidAlgebra X 1 => (z : End (tensorPower X 3))) hs)

omit [Preadditive C] [Linear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- Finite categorical braid image gives finite order of the double
self-braiding on the ordinary tensor product. -/
theorem selfMonodromy_isOfFinOrder {X : C} (hfinite : ObjectPropertyF X) :
    IsOfFinOrder (selfMonodromy X) := by
  let _ : Finite (braidImage X 0) := hfinite 0
  have h := ((twoPowerIso X).conj.toMonoidHom.comp
    (Aut.toEnd.comp (braidImage X 0).subtype)).isOfFinOrder
      (isOfFinOrder_of_finite (imageGenerator X 0 0))
  change IsOfFinOrder ((twoPowerIso X).conj (Aut.toEnd (braidGenerator X 0 0))) at h
  convert h.pow (n := 2) using 1
  apply End.ext
  simp [twoPowerIso, braidGenerator, tensorPower, selfMonodromy, Iso.conj_apply_asHom,
    pow_two, End.mul_asHom]

end LocalMonodromy

/-- If the same pair operator occurs on either adjacent pair, partial trace
forces that operator to be scalar. -/
theorem pair_operator_scalar_of_overlaps_equal {X : C.Obj} [Simple X]
    (u : End (X ⊗ X))
    {d f : ℝ} (hd : d ≠ 0)
    (hdim : pivotalDimension C p X = (d : ℂ))
    (htrace : scalarTrace p (Ground.unitScalarEquiv C) u = (d : ℂ) * f)
    (heq : insertRightIdentity X u = overlapFresh X u) :
    u = (f / d : ℂ) • (1 : End (X ⊗ X)) := by
  unfold scalarTrace at htrace
  unfold pivotalDimension at hdim
  rw [unitScalar_eq_equiv] at hdim
  have h := congrArg (rightPartialTrace p (X := X ⊗ X) (Y := X)) heq
  rw [rightPartialTrace_insert p (Ground.unitScalarEquiv C),
    overlapFresh, rightPartialTrace_whiskerLeft,
    rightPartialTrace_simple_ground C (X := X) (Y := X) p (Ground.unitScalarEquiv C)] at h
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [scalarTrace, hdim, htrace] at h
  have h' : (d : ℂ) • u = (f : ℂ) • (1 : End (X ⊗ X)) := by
    have hs : End.of (X ◁ ((f : ℂ) • (1 : End X)).asHom) =
        (f : ℂ) • (1 : End (X ⊗ X)) :=
      End.ext (by simp only [End.smul_asHom, End.one_asHom,
        MonoidalLinear.whiskerLeft_smul, whiskerLeft_id])
    simpa only [mul_div_cancel_left₀ _ hd', hs] using h
  apply (smul_right_injective _ hd')
  simpa only [smul_smul, mul_div_cancel₀ _ hd'] using h'

/-- An object with nonzero pivotal dimension has a nonzero identity endomorphism. -/
theorem end_one_ne_zero_of_pivotalDimension_ne_zero {X : C.Obj}
    (h : pivotalDimension C p X ≠ 0) :
    (1 : End X) ≠ 0 := fun hzero => h (by
  simp [pivotalDimension, unitScalar_eq_equiv, ← End.one_asHom, hzero,
    PivotalStructure.rightTrace, rightTraceWith, End.ext_iff])

/-- A scalar double self-braiding of finite order has unit-modulus scalar,
so the two real dimensions have equal absolute value. -/
theorem dimension_eq_abs_of_scalar_monodromy {X : C.Obj} {d f : ℝ} (hd : d ≠ 0) (hf : 0 < f)
    (hdim : pivotalDimension C p X = (d : ℂ)) (hfinite : ObjectPropertyF X)
    (hscalar : selfMonodromy X = (f / d : ℂ) • (1 : End (X ⊗ X))) : f = |d| :=
  let hnonzero : (1 : End (X ⊗ X)) ≠ 0 :=
    end_one_ne_zero_of_pivotalDimension_ne_zero C p (by
      rw [Dimensions.pivotalDimension_tensor, hdim]
      exact_mod_cast mul_ne_zero hd hd)
  let ⟨n, hn, hpow⟩ := (selfMonodromy_isOfFinOrder hfinite).exists_pow_eq_one
  fp_eq_abs_dim_of_finite_order hd hf ⟨n, hn.ne', smul_left_injective ℂ hnonzero (by
    change ((f / d : ℂ) ^ n) • (1 : End (X ⊗ X)) = (1 : ℂ) • (1 : End (X ⊗ X))
    simpa [hscalar, smul_pow] using hpow)⟩

section BlockRigidity

variable {X : C.Obj} {r : ℕ} {size : Fin r → ℕ}
  (b : BraidBlockPresentation X 1 size)
  (he : IsUnitaryBraidPresentation b) {w : Fin r → ℝ} (hw : ∀ i, w i ≠ 0)
  {d f : ℝ} (htrace : IsTracePresentation C p b w)
  (hbound : HasUnitaryTraceBound C p b (|d| * f ^ 2))
include he hw htrace hbound

set_option backward.isDefEq.respectTransparency false in
/-- Actual three-strand block generators have equal squares once their
categorical weighted trace has the sharp bound and saturates it at `a²b²`.
The remaining hypotheses are explicitly the trace weights and sharp bound. -/
theorem actual_braid_squares_equal_of_saturation (hf : 0 < f)
    (hvalue : actualBraidTrace C p (braidInImage
      (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2)) = (d : ℂ) * f ^ 2) :
    tripleBlockLeft b ^ 2 = tripleBlockRight b ^ 2 :=
  let B : Blocks := ⟨r, size⟩
  let ρ : braidImage X 1 →* B.Algebra :=
    b.toMonoidHom.comp (braidInImage (X := X) (n := 1))
  let a : B.Algebraˣ := ρ.toHomUnits (threeGeneratorLeft X)
  let c : B.Algebraˣ := ρ.toHomUnits (threeGeneratorRight X)
  congrArg (fun z : B.Algebraˣ => (z : B.Algebra))
    (braid_squares_equal_of_saturation B w a c d f hf hw (he _) (he _)
      (Units.ext (by simpa only [a, c, Units.val_mul, MonoidHom.coe_toHomUnits, map_mul] using
        (congrArg ρ (three_braid_image_relation X))))
      (fun z hz => by
        simpa [htrace, B] using hbound (b.symm z) (by simpa only [b.apply_symm_apply] using hz))
      (by simpa only [a, c, Units.val_mul, Units.val_pow_eq_pow_val,
        MonoidHom.coe_toHomUnits, ρ, MonoidHom.coe_comp, Function.comp_apply, map_mul, map_pow,
        htrace, B] using! hvalue))

/-- Three-strand rigidity for a genuine braided pivotal fusion category,
reduced to explicit real, nonzero trace weights and the sharp unitary bound. -/
theorem actual_three_strand_rigidity_of_trace_bound [Simple X]
    (hd : d ≠ 0) (hf : 0 < f) (hdim : pivotalDimension C p X = (d : ℂ))
    (hS : scalarTrace p (Ground.unitScalarEquiv C) (selfMonodromy X) = (d : ℂ) * f)
    (hfinite : ObjectPropertyF X) : f = |d| :=
  dimension_eq_abs_of_scalar_monodromy C p hd hf hdim hfinite
    (pair_operator_scalar_of_overlaps_equal C p (selfMonodromy X) hd hdim hS
      (local_monodromy_of_block_squares_equal b
        (actual_braid_squares_equal_of_saturation C p b he hw htrace hbound hf
          (by rw [actual_three_braid_trace C p X, hdim, hS, mul_pow,
            pow_two (d : ℂ), mul_assoc, mul_div_cancel_left₀ _ (by exact_mod_cast hd)]))))

end BlockRigidity

end PropertyF.Ground.Calculus
