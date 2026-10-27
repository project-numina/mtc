module
public import PropertyF.Ground.Calculus.GaloisOverlap
public import PropertyF.Ground.Calculus.ThreeRigidity

/-! Three-strand rigidity after semilinear scalar transport. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u

/-- Equal adjacent copies force any two-strand endomorphism to be scalar,
with its scalar given by its trace and the simple pivotal dimension. -/
theorem pair_operator_scalar_of_overlaps_equal_complex
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (u : End (X ⊗ X))
    (heq : insertRightIdentity (X ⊗ X) X u = overlapFresh X X X u) :
    u = (Dimensions.groundUnitScalarEquiv C (p.rightTrace u.asHom) /
      (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ 2) • (1 : End (X ⊗ X)) := by
  let δ := Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))
  let tr := Dimensions.groundUnitScalarEquiv C (p.rightTrace u.asHom)
  have hδ : δ ≠ 0 := by
    intro h
    apply Modular.pivotalTrace_simple_ne_zero C p X
    apply (Dimensions.groundUnitScalarEquiv C).injective
    simpa [δ] using h
  have h := congrArg (rightPartialTrace p (X ⊗ X) X) heq
  rw [rightPartialTrace_insert p (Dimensions.groundUnitScalarEquiv C),
    overlapFresh, rightPartialTrace_whiskerLeft,
    rightPartialTrace_simple_ground C X X p (Dimensions.groundUnitScalarEquiv C)] at h
  change δ • u = End.of (X ◁ ((tr / δ) • (1 : End X)).asHom) at h
  have hs : End.of (X ◁ ((tr / δ) • (1 : End X)).asHom) =
      (tr / δ) • (1 : End (X ⊗ X)) := by
    apply End.ext
    change X ◁ ((tr / δ) • (𝟙 X)) = (tr / δ) • (𝟙 (X ⊗ X))
    rw [MonoidalLinear.whiskerLeft_smul, whiskerLeft_id]
  rw [hs] at h
  apply (smul_right_injective _ hδ)
  change δ • u = δ • ((tr / δ ^ 2) • (1 : End (X ⊗ X)))
  rw [h, smul_smul]
  have : δ * (tr / δ ^ 2) = tr / δ := by field_simp
  rw [this]

/-- A scalar double self-braiding has finite scalar order when the actual
categorical braid image is finite. -/
theorem scalar_monodromy_has_finite_order
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (z : ℂ)
    (hfinite : ObjectPropertyF X)
    (hscalar : selfMonodromy X = z • (1 : End (X ⊗ X))) :
    ∃ n : ℕ, n ≠ 0 ∧ z ^ n = 1 := by
  let δ := Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))
  have hδ : δ ≠ 0 := by
    intro h
    apply Modular.pivotalTrace_simple_ne_zero C p X
    apply (Dimensions.groundUnitScalarEquiv C).injective
    simpa [δ] using h
  have hdim2 : Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 (X ⊗ X))) = δ ^ 2 := by
    have h := Dimensions.pivotalDimension_tensor C p X X
    simpa [Dimensions.pivotalDimension, ← Dimensions.groundUnitScalarEquiv_apply,
      δ, pow_two] using h
  have hnonzero : (1 : End (X ⊗ X)) ≠ 0 := by
    intro h
    have ht := congrArg (fun a : End (X ⊗ X) =>
      Dimensions.groundUnitScalarEquiv C (p.rightTrace a.asHom)) h
    have hz : p.rightTrace (0 : X ⊗ X ⟶ X ⊗ X) = 0 := by
      simpa using p.rightTrace_smul (0 : ℂ) (𝟙 (X ⊗ X))
    have : δ ^ 2 = 0 := by
      simpa only [End.one_asHom, End.zero_asHom, hdim2, hz, map_zero] using ht
    exact (pow_ne_zero 2 hδ) this
  obtain ⟨n, hn, hpow⟩ := selfMonodromy_finite_order C X hfinite
  refine ⟨n, hn, ?_⟩
  apply (smul_left_injective ℂ hnonzero)
  change (z ^ n) • (1 : End (X ⊗ X)) = (1 : ℂ) • (1 : End (X ⊗ X))
  simpa [hscalar, smul_pow] using hpow

/-- The actual three-strand braid is trace-saturating after applying a field
automorphism when its transported dimension and self-entry have the stated values. -/
theorem galois_three_braid_saturates
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ)
    (d f : ℝ) (hd : d ≠ 0)
    (hdim : σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) = (d : ℂ))
    (hS : σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (selfMonodromy X).asHom)) =
      (d : ℂ) * f) :
    galoisActualBraidTrace C X p σ 1 (groupInImage (braidEndRepresentation X 1)
      (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2)) = (d : ℂ) * f ^ 2 := by
  change σ (actualBraidTrace C X p 1 _) = _
  rw [actual_three_braid_trace C X p, map_div₀, map_pow, hdim, hS]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp

set_option backward.isDefEq.respectTransparency false in
/-- Semilinear transported block squares reflect equality of the actual
adjacent categorical double braids. -/
theorem local_monodromy_of_galois_block_squares_equal
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj)
    (r : ℕ) (size : Fin r → ℕ)
    (T : braidAlgebra X 1 ≃+* ∀ i, Matrix (Fin (size i)) (Fin (size i)) ℂ)
    (h : T (groupInImage (braidEndRepresentation X 1) (threeGeneratorLeft X)) ^ 2 =
      T (groupInImage (braidEndRepresentation X 1) (threeGeneratorRight X)) ^ 2) :
    insertRightIdentity (X ⊗ X) X (selfMonodromy X) =
      overlapFresh X X X (selfMonodromy X) := by
  apply local_monodromy_of_three_squares_equal C X
  have hs : groupInImage (braidEndRepresentation X 1) (threeGeneratorLeft X ^ 2) =
      groupInImage (braidEndRepresentation X 1) (threeGeneratorRight X ^ 2) := by
    apply T.injective
    simpa only [map_pow] using h
  have hm := congrArg (fun z : braidAlgebra X 1 => (z : End (tensorPower X 3))) hs
  simpa [groupInImage_val, braidEndRepresentation, threeGeneratorLeft,
    threeGeneratorRight, imageGenerator] using hm

set_option backward.isDefEq.respectTransparency false in
/-- Galois three-strand rigidity from the transported sharp trace bound and
nonzero real block weights; no conjugate category is assumed. -/
theorem galois_rigidity_of_sharp_trace_bound
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ)
    (r : ℕ) (size : Fin r → ℕ)
    (T : braidAlgebra X 1 ≃+* ∀ i, Matrix (Fin (size i)) (Fin (size i)) ℂ)
    (he : ∀ g i, T (groupInImage (braidEndRepresentation X 1) g) i ∈
      Matrix.unitaryGroup (Fin (size i)) ℂ)
    (w : Fin r → ℝ) (hw : ∀ i, w i ≠ 0)
    (d f : ℝ) (hd : d ≠ 0) (hf : 0 < f)
    (hdim : σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) = (d : ℂ))
    (hS : σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (selfMonodromy X).asHom)) =
      (d : ℂ) * f)
    (hfinite : ObjectPropertyF X)
    (htrace : ∀ a : braidAlgebra X 1, galoisActualBraidTrace C X p σ 1 a =
      (PropertyF.Blocks.mk r size).trace w (T a))
    (hbound : ∀ a : braidAlgebra X 1,
      (∀ i, T a i ∈ Matrix.unitaryGroup (Fin (size i)) ℂ) →
      ‖galoisActualBraidTrace C X p σ 1 a‖ ≤ |d| * f ^ 2) : f = |d| := by
  let B : PropertyF.Blocks := ⟨r, size⟩
  let ρ : braidImage X 1 →* B.Algebra :=
    T.toMonoidHom.comp (groupInImage (braidEndRepresentation X 1))
  let a : B.Algebraˣ := ρ.toHomUnits (threeGeneratorLeft X)
  let b : B.Algebraˣ := ρ.toHomUnits (threeGeneratorRight X)
  have ha : B.IsUnitary (a : B.Algebra) := he _
  have hb : B.IsUnitary (b : B.Algebra) := he _
  have hbraid : a * b * a = b * a * b := by
    apply Units.ext
    exact three_braid_relation_map X ρ
  have hbnd : ∀ z : B.Algebra, B.IsUnitary z → ‖B.trace w z‖ ≤ |d| * f ^ 2 := by
    intro z hz
    change ∀ i, z i ∈ Matrix.unitaryGroup (Fin (size i)) ℂ at hz
    have h := hbound (T.symm z) (by simpa only [T.apply_symm_apply] using hz)
    simpa [htrace, B] using h
  have hv : B.trace w ((a ^ 2 * b ^ 2 : B.Algebraˣ) : B.Algebra) = (d : ℂ) * f ^ 2 := by
    have h := htrace (groupInImage (braidEndRepresentation X 1)
      (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2))
    rw [galois_three_braid_saturates C X p σ d f hd hdim hS] at h
    change B.trace w (T (groupInImage (braidEndRepresentation X 1) (threeGeneratorLeft X)) ^ 2 *
      T (groupInImage (braidEndRepresentation X 1) (threeGeneratorRight X)) ^ 2) = _
    rw [← map_pow, ← map_pow, ← map_mul]
    rw [map_mul, map_pow, map_pow] at h
    exact h.symm
  have hsquares := braid_squares_equal_of_saturation B w a b d f hf hw ha hb hbraid hbnd hv
  have hblocks := congrArg (fun z : B.Algebraˣ => (z : B.Algebra)) hsquares
  change T (groupInImage (braidEndRepresentation X 1) (threeGeneratorLeft X)) ^ 2 =
    T (groupInImage (braidEndRepresentation X 1) (threeGeneratorRight X)) ^ 2 at hblocks
  have hlocal := local_monodromy_of_galois_block_squares_equal C X r size T hblocks
  let δ := Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))
  let tr := Dimensions.groundUnitScalarEquiv C (p.rightTrace (selfMonodromy X).asHom)
  let z : ℂ := tr / δ ^ 2
  have hscalar : selfMonodromy X = z • (1 : End (X ⊗ X)) :=
    pair_operator_scalar_of_overlaps_equal_complex C X p (selfMonodromy X) hlocal
  obtain ⟨n, hn, horder⟩ := scalar_monodromy_has_finite_order C X p z hfinite hscalar
  have hz : σ z = (f / d : ℂ) := by
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    simp only [z, tr, δ, map_div₀, map_pow, hS, hdim]
    field_simp
  have hh := congrArg σ horder
  simp only [map_pow, map_one, hz] at hh
  exact PropertyF.fp_eq_abs_dim_of_finite_order hd hf ⟨n, hn, hh⟩

/-- Galois three-strand rigidity for the original genuine category, reduced
to the single intrinsic overlap identity and real Galois simple dimensions.
All transported matrix blocks, weights, and sharp trace bounds are constructed. -/
theorem galois_rigidity_of_overlap_identity
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ)
    (original conjugate : Fin (Ground.rank C) → ℝ)
    (hpos : ∀ i, 0 < original i)
    (hdims : ∀ i, Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (𝟙 (Ground.simples C i))) = (original i : ℂ))
    (hreal : ∀ i, σ (original i : ℂ) = (conjugate i : ℂ))
    (d f : ℝ) (hd : d ≠ 0) (hf : 0 < f)
    (hdim : σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) = (d : ℂ))
    (hfp : Ground.fpDimension C X = f)
    (hS : σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (selfMonodromy X).asHom)) =
      (d : ℂ) * f)
    (hfinite : ObjectPropertyF X)
    (hrec : ∀ (u : braidAlgebra X 1) k,
      actualBraidTrace C X p (overlapIndex 1 k) (overlapProduct X 1 u k) *
        (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k =
          actualBraidTrace C X p 1 u ^ (k + 1)) : f = |d| := by
  classical
  choose r size T w hsize hw he hsmul htrace hbound using fun n =>
    exists_galois_real_braid_trace_bound C X n (hfinite n) p σ original conjugate hpos hdims hreal
  have hpower : ∀ n (a : braidAlgebra X n),
      (∀ i, T n a i ∈ Matrix.unitaryGroup (Fin (size n i)) ℂ) →
      ‖galoisActualBraidTrace C X p σ n a‖ ≤ Ground.fpDimension C X ^ (n + 2) := by
    intro n a ha
    exact hbound n a ha
  have htrace1 : ∀ a : braidAlgebra X 1, galoisActualBraidTrace C X p σ 1 a =
      (PropertyF.Blocks.mk (r 1) (size 1)).trace (w 1) (T 1 a) := htrace 1
  apply galois_rigidity_of_sharp_trace_bound C X p σ (r 1) (size 1) (T 1) (he 1)
    (w 1) (hw 1) d f hd hf hdim hS hfinite htrace1
  intro u hu
  have h := galois_sharp_trace_bound_of_overlap_identity C X p σ 1 r size T hsmul he hpower u hu (hrec u)
  simpa [hdim, hfp, Complex.norm_real, Real.norm_eq_abs] using h

end PropertyF.Ground.Calculus
