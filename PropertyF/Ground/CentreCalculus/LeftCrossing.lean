module
public import PropertyF.Ground.CentreCalculus.LeftPartialTrace
public import PropertyF.Ground.CentreCalculus.FirstCrossingTrace

/-! Reducing the local crossing trace to iterated left trace compatibility. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u

/-- Once left partial trace composes with total trace, Schur's lemma computes
the closed crossing as the pivotal twist scalar. -/
theorem leftPartialTrace_braiding_of_trace_compatibility
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (X : C.Obj) [Simple X]
    (ht : p.rightTrace (leftPartialTrace p X X (End.of (β_ X X).hom)).asHom =
      p.rightTrace (β_ X X).hom) :
    leftPartialTrace p X X (End.of (β_ X X).hom) =
      Dimensions.pivotalBraidedTwistScalar C p X • (1 : End X) := by
  letI : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  have hd : unitScalarEquiv C (p.rightTrace (𝟙 X)) ≠ 0 := by
    have h : Dimensions.pivotalDimension C p X ≠ 0 := by
      obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso C X
      rw [Dimensions.pivotalDimension_iso C p e]
      exact Dimensions.pivotalDimension_simple_ne_zero C p i
    simpa [Dimensions.pivotalDimension, unitScalar_eq_equiv] using h
  have hh := leftPartialTrace_simple_of_trace_compatibility X X p (unitScalarEquiv C)
    (End.of (β_ X X).hom) hd ht
  rw [← unitScalar_eq_equiv, Dimensions.pivotalTrace_selfBraiding] at hh
  have hdim : unitScalarEquiv C (p.rightTrace (𝟙 X)) = Dimensions.pivotalDimension C p X := by
    simp [Dimensions.pivotalDimension, unitScalar_eq_equiv]
  rw [hdim, mul_div_cancel_right₀ _ (by simpa [hdim] using hd)] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
/-- The closed first crossing with any spectator tensor factor is the same
scalar on the entire untraced factor. -/
theorem leftPartialTrace_firstGenerator_of_trace_compatibility
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (X : C.Obj) [Simple X] (n : ℕ)
    (ht : p.rightTrace (leftPartialTrace p X X (End.of (β_ X X).hom)).asHom =
      p.rightTrace (β_ X X).hom) :
    leftPartialTrace p X (tensorPower X (n + 1)) (Aut.toEnd (braidGenerator X n 0)) =
      Dimensions.pivotalBraidedTwistScalar C p X • 1 := by
  have hg : (Aut.toEnd (braidGenerator X n 0)) = End.of
      ((α_ X X (tensorPower X n)).inv ≫ ((β_ X X).hom ▷ tensorPower X n) ≫
        (α_ X X (tensorPower X n)).hom) := by
    apply End.ext
    change (braidGenerator X n ⟨0, by omega⟩).asIso.hom = _
    simp only [braidGenerator, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
      tensorHom_id]
  change leftPartialTrace p X (X ⊗ tensorPower X n) (Aut.toEnd (braidGenerator X n 0)) = _
  dsimp only [tensorPower] at hg ⊢
  rw [hg]
  have hw := leftPartialTrace_whiskerRight p X X (tensorPower X n) (End.of (β_ X X).hom)
  change leftPartialTrace p X (X ⊗ tensorPower X n) (End.of
      ((α_ X X (tensorPower X n)).inv ≫ (β_ X X).hom ▷ tensorPower X n ≫
        (α_ X X (tensorPower X n)).hom)) = _ at hw
  rw [hw, leftPartialTrace_braiding_of_trace_compatibility C p X ht]
  apply End.ext
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Fixed-head permutation actions are left tensor insertions in every degree. -/
theorem tensorPermutationAction_fixHead (C : BraidedFusionCategory.{v,u})
    (X : C.Obj) (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X)) :
    ∀ n (σ : Equiv.Perm (Fin n)),
      tensorPermutationAction X hX (n + 1) (fixHead n σ) =
        (tensorLeft X).mapEnd (tensorPower X n) (tensorPermutationAction X hX n σ) := by
  intro n
  cases n with
  | zero =>
    intro σ
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst σ
    simp [tensorPermutationAction, Functor.mapEnd]
    rfl
  | succ n =>
    cases n with
    | zero =>
      intro σ
      have hσ : σ = 1 := by
        ext x
        exact congrArg Fin.val ((Fin.eq_zero (σ x)).trans (Fin.eq_zero ((1 : Equiv.Perm (Fin 1)) x)).symm)
      subst σ
      simp [tensorPermutationAction, Functor.mapEnd]
      rfl
    | succ n =>
      intro σ
      change Aut.toEnd (permutationAction X hX (n + 1) (fixHead (n + 2) σ)) = _
      rw [permutationAction_fixHead]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- Left trace compatibility implies the local deletion law, with the actual
pivotal twist scalar as its factor. -/
theorem tensorPermutationTrace_adjacent_of_leftTrace
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (X : C.Obj) [Simple X] (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X))
    (htotal : ∀ Y (f : End (X ⊗ Y)),
      p.rightTrace (leftPartialTrace p X Y f).asHom = p.rightTrace f.asHom)
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    unitScalar C (p.rightTrace ((tensorPermutationAction X hX (n + 2))
      (Equiv.Perm.decomposeFin.symm (1, σ))).asHom) =
    Dimensions.pivotalBraidedTwistScalar C p X *
      unitScalar C (p.rightTrace ((tensorPermutationAction X hX (n + 1)) σ).asHom) := by
  let f := (tensorPermutationAction X hX (n + 1)) σ
  have hswap : tensorPermutationAction X hX (n + 2) (Equiv.swap 0 1) =
      Aut.toEnd (braidGenerator X n 0) := by
    convert tensorPermutationAction_swap X hX n 0 using 1 <;> congr 2
  let b : End (X ⊗ tensorPower X (n + 1)) := Aut.toEnd (braidGenerator X n 0)
  have hact : tensorPermutationAction X hX (n + 2)
      (Equiv.Perm.decomposeFin.symm (1, σ)) =
      b * insertLeftIdentity X (tensorPower X (n + 1)) f := by
    rw [decomposeFin_eq_swap_fixHead, map_mul, hswap, tensorPermutationAction_fixHead]
    change b * _ = b * _
    congr 1
  rw [hact, ← htotal _ _, leftPartialTrace_right]
  change unitScalar C (p.rightTrace ((leftPartialTrace p X (tensorPower X (n + 1)) b * f).asHom)) = _
  dsimp only [b]
  rw [
    leftPartialTrace_firstGenerator_of_trace_compatibility C p X n (htotal X (End.of (β_ X X).hom))]
  simp only [smul_mul_assoc, one_mul, End.smul_asHom, p.rightTrace_smul,
    unitScalar_eq_equiv, map_smul, smul_eq_mul, f]

/-- The symmetric integrality argument now needs only left iterated-trace
compatibility and the sign of the actual pivotal twist scalar. -/
theorem integral_of_leftTrace_and_twist_sign
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X : C.Obj) [Simple X] (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X))
    (htotal : ∀ Y (f : End (X ⊗ Y)),
      p.rightTrace (leftPartialTrace p X Y f).asHom = p.rightTrace f.asHom)
    (hsign : Dimensions.pivotalBraidedTwistScalar C p X = 1 ∨
      Dimensions.pivotalBraidedTwistScalar C p X = -1) :
    ∃ m : ℕ, fpDimension C X = m := by
  rcases hsign with h | h
  · apply integral_of_parity_adjacent_trace C p hdim X hX false
    intro n σ
    simpa [parityPermutationAction, h] using
      tensorPermutationTrace_adjacent_of_leftTrace C p X hX htotal n σ
  · apply integral_of_parity_adjacent_trace C p hdim X hX true
    intro n σ
    have hsign' : (Centre.permutationSign ℂ (n + 2)
        (Equiv.Perm.decomposeFin.symm (1, σ)) : ℂ) =
        -(Centre.permutationSign ℂ (n + 1) σ : ℂ) := by
      simpa using sign_decomposeFin (n + 1) 1 σ
    simp only [parityPermutationAction, Bool.true_eq, ↓reduceIte, Centre.twistAction,
      MonoidHom.coe_mk, OneHom.coe_mk, End.smul_asHom, p.rightTrace_smul,
      unitScalar_eq_equiv, map_smul, smul_eq_mul, hsign']
    rw [← unitScalar_eq_equiv, ← unitScalar_eq_equiv,
      tensorPermutationTrace_adjacent_of_leftTrace C p X hX htotal n σ, h]
    ring

end PropertyF.Ground.CentreCalculus
