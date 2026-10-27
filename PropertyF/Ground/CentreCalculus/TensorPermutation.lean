module
public import PropertyF.Ground.CentreCalculus.TypeAPresentation
public import PropertyF.Ground.CentreCalculus.ProjectorReduction

/-! Permutation actions and split projectors for every tensor power. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The actual self-transparent permutation action, including the trivial
zero- and one-strand cases, as endomorphisms. -/
def tensorPermutationAction (X : C)
    (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X)) :
    ∀ n : ℕ, Equiv.Perm (Fin n) →* End (tensorPower X n)
  | 0 => 1
  | 1 => 1
  | n + 2 => Aut.toEnd.comp (permutationAction X hX n)

/-- Every adjacent transposition acts by the actual categorical crossing. -/
theorem tensorPermutationAction_swap (X : C)
    (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X))
    (n : ℕ) (i : Fin (n + 1)) :
    tensorPermutationAction X hX (n + 2) (Equiv.swap i.castSucc i.succ) =
      Aut.toEnd (braidGenerator X n i) := by
  simp only [tensorPermutationAction, MonoidHom.comp_apply, permutationAction_swap]

/-- Actual alternating projectors on every self-transparent tensor power
split into genuine objects. -/
theorem selfTransparent_alternatingProjector_trace (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X : C.Obj)
    (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X)) (n : ℕ) :
    letI := permutationCardInvertible n
    ∃ Y : C.Obj,
      p.rightTrace ((Centre.alternatingProjector (k := ℂ) n
        (tensorPermutationAction X hX n)).asHom) = p.rightTrace (𝟙 Y) := by
  letI := permutationCardInvertible n
  exact Centre.alternatingProjector_trace (tensorPower X n) n (tensorPermutationAction X hX n) p

end PropertyF.Ground.CentreCalculus
