module
public import PropertyF.Ground.CentreModular.VafaHexagon
public import PropertyF.Ground.CentreModular.VafaFunctor

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u

/-- For a fixed first strand, double braiding is a natural automorphism of
the actual tensor-left functor. -/
def monodromyNaturalIso (C : BraidedFusionCategory.{v,u}) (Z : C.Obj) :
    tensorLeft Z ≅ tensorLeft Z :=
  NatIso.ofComponents (fun W => monodromyIso C Z W) (by
    intro X Y f
    change (Z ◁ f) ≫ ((β_ Z Y).hom ≫ (β_ Y Z).hom) =
      ((β_ Z X).hom ≫ (β_ X Z).hom) ≫ (Z ◁ f)
    simp only [← id_tensorHom, Category.assoc]
    rw [braiding_naturality_assoc, braiding_naturality])

/-- FP determinant of a mixed monodromy expands over simple summands of
the second strand. -/
theorem fpDeterminant_monodromy_decomposition (C : BraidedFusionCategory.{v,u})
    (Z W : C.Obj) :
    fpDeterminant C (Z ⊗ W) (monodromyIso C Z W) = ∑ i,
      (Module.finrank ℂ (simples C i ⟶ W) : ℝ) •
        fpDeterminant C (Z ⊗ simples C i) (monodromyIso C Z (simples C i)) := by
  exact fpDeterminant_functor_natural_decomposition C (tensorLeft Z) (monodromyNaturalIso C Z) W

/-- Under simple twist balancing, the FP determinant of every simple mixed
monodromy vanishes. -/
theorem fpDeterminant_simple_monodromy_eq_zero (C : BraidedFusionCategory.{v,u})
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (t : Fin (rank C) → ℂˣ)
    (hbalance : ∀ i j, η.app (simples C i ⊗ simples C j) =
      scalarIso C (simples C i ⊗ simples C j) (t i * t j) ≪≫
        monodromyIso C (simples C i) (simples C j))
    (z i : Fin (rank C)) :
    fpDeterminant C (simples C z ⊗ simples C i)
      (monodromyIso C (simples C z) (simples C i)) = 0 := by
  let B : Fin (rank C) → Fin (rank C) → vafaUnitSpace := fun i z =>
    fpDeterminant C (simples C z ⊗ simples C i)
      (monodromyIso C (simples C z) (simples C i))
  have hhex : ∀ i j z, (∑ k, (fusionCoeff C i j k : ℝ) • B k z) =
      fpSimple C j • B i z + fpSimple C i • B j z := by
    intro i j z
    have h := fpDeterminant_monodromy_hexagon C η t hbalance z i j
    rw [fpDeterminant_monodromy_decomposition] at h
    change (∑ k, (fusionCoeff C i j k : ℝ) • B k z) = _ at h
    simpa [B, add_comm] using h
  exact regular_fusion_derivation_vanishes C vafaUnitSpace B hhex i z

/-- Under an actual natural twist and its simple balancing equation,
the simple twist scalars have finite order. -/
theorem natural_scalars_finite_of_simple_balancing
    (C : BraidedFusionCategory.{v,u}) (η : 𝟭 C.Obj ≅ 𝟭 C.Obj)
    (t : Fin (rank C) → ℂˣ)
    (ht : ∀ i, (η.app (simples C i)).hom = (t i : ℂ) • 𝟙 (simples C i))
    (hbalance : ∀ i j, η.app (simples C i ⊗ simples C j) =
      scalarIso C (simples C i ⊗ simples C j) (t i * t j) ≪≫
        monodromyIso C (simples C i) (simples C j)) :
    ∀ i, IsOfFinOrder (t i) := by
  apply natural_scalars_finite_of_monodromy_determinant C η t ht hbalance
  intro i j
  exact fpDeterminant_simple_monodromy_eq_zero C η t hbalance i j

end PropertyF.Ground.CentreModular
