module
public import PropertyF.Ground.CentreCalculus.ParityDeletion
public import PropertyF.Ground.CentreDimensions.PivotalTwist
public import PropertyF.Ground.Calculus.ThreeTrace

/-! The first nontrivial trace-deletion case and its twist scalar. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u

/-- The trace of the two-strand permutation is the actual twist scalar times
the dimension. This identifies the parity factor that occurs in deletion. -/
theorem twoStrand_permutation_trace (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X]
    (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X)) :
    unitScalar C (p.rightTrace ((tensorPermutationAction X hX 2)
      (Equiv.Perm.decomposeFin.symm (1, 1))).asHom) =
    Dimensions.pivotalBraidedTwistScalar C p X * Dimensions.pivotalDimension C p X := by
  have hswap : Equiv.Perm.decomposeFin.symm (1, (1 : Equiv.Perm (Fin 1))) =
      Equiv.swap (0 : Fin 2) 1 := by simp
  rw [hswap]
  have ha : tensorPermutationAction X hX 2 (Equiv.swap (0 : Fin 2) 1) =
      Aut.toEnd (braidGenerator X 0 0) := by
    simpa using tensorPermutationAction_swap X hX 0 0
  rw [ha]
  have hh := Calculus.rightTrace_iso_conj p (Calculus.twoPowerIso X)
    (Aut.toEnd (braidGenerator X 0 0))
  have ht : Calculus.isoEndAlgEquiv (Calculus.twoPowerIso X) (Aut.toEnd (braidGenerator X 0 0)) =
      End.of (β_ X X).hom := by
    apply End.ext
    exact Calculus.twoGenerator_transport X
  rw [ht] at hh
  rw [← hh]
  exact Dimensions.pivotalTrace_selfBraiding C p X

/-- Twisting by sign negates the two-strand trace. -/
theorem twoStrand_parity_trace (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X]
    (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X)) (odd : Bool) :
    unitScalar C (p.rightTrace ((parityPermutationAction C X hX odd 2)
      (Equiv.Perm.decomposeFin.symm (1, 1))).asHom) =
    (if odd then -Dimensions.pivotalBraidedTwistScalar C p X
      else Dimensions.pivotalBraidedTwistScalar C p X) * Dimensions.pivotalDimension C p X := by
  cases odd with
  | false => exact twoStrand_permutation_trace C p X hX
  | true =>
    have hs : (Centre.permutationSign ℂ 2
        (Equiv.Perm.decomposeFin.symm (1, (1 : Equiv.Perm (Fin 1)))) : ℂ) = -1 := by
      simpa [Centre.permutationSign] using sign_decomposeFin 1 1 (1 : Equiv.Perm (Fin 1))
    simp only [parityPermutationAction, Bool.true_eq, ↓reduceIte, Centre.twistAction,
      MonoidHom.coe_mk, OneHom.coe_mk, End.smul_asHom, p.rightTrace_smul,
      unitScalar_eq_equiv, map_smul, smul_eq_mul, hs]
    rw [← unitScalar_eq_equiv, twoStrand_permutation_trace C p X hX]
    ring

/-- If the twist is a sign, one parity choice satisfies the adjacent deletion
identity in its two-strand base case. -/
theorem exists_parity_twoStrand_deletion (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X]
    (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X))
    (hsign : Dimensions.pivotalBraidedTwistScalar C p X = 1 ∨
      Dimensions.pivotalBraidedTwistScalar C p X = -1) :
    ∃ odd : Bool, ∀ σ : Equiv.Perm (Fin 1),
      unitScalar C (p.rightTrace ((parityPermutationAction C X hX odd 2)
        (Equiv.Perm.decomposeFin.symm (1, σ))).asHom) =
      unitScalar C (p.rightTrace ((parityPermutationAction C X hX odd 1) σ).asHom) := by
  have hone : ∀ σ : Equiv.Perm (Fin 1), σ = 1 := by
    intro σ
    ext x
    exact congrArg Fin.val ((Fin.eq_zero (σ x)).trans (Fin.eq_zero ((1 : Equiv.Perm (Fin 1)) x)).symm)
  rcases hsign with h | h
  · refine ⟨false, ?_⟩
    intro σ
    rw [hone σ, twoStrand_parity_trace, h]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, parityPermutationAction,
      tensorPermutationAction, MonoidHom.one_apply, End.one_asHom]
    change Dimensions.pivotalDimension C p X = Dimensions.pivotalDimension C p (X ⊗ 𝟙_ C.Obj)
    exact (Dimensions.pivotalDimension_iso C p (ρ_ X)).symm
  · refine ⟨true, ?_⟩
    intro σ
    rw [hone σ, twoStrand_parity_trace, h]
    simp only [Bool.true_eq, ↓reduceIte, neg_neg, one_mul, map_one, End.one_asHom]
    change Dimensions.pivotalDimension C p X = Dimensions.pivotalDimension C p (X ⊗ 𝟙_ C.Obj)
    exact (Dimensions.pivotalDimension_iso C p (ρ_ X)).symm

end PropertyF.Ground.CentreCalculus
