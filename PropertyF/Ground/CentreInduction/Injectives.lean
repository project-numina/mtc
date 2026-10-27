module
public import PropertyF.Ground.CentreInduction.FiniteSimples
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
open CategoryTheory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

/-- Every object of a finite semisimple base is injective. -/
theorem base_injective (X : C.Obj) : Injective X := object_injective C X

/-- Induction sends every base object to an injective centre object. -/
theorem induction_injective (X : C.Obj) : Injective ((induction C).obj X) := by
  letI : (induction C).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (actualAdjunction C)
  letI : Injective X := object_injective C X
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Every centre object embeds into its induced underlying object. -/
theorem induction_unit_mono (Z : CategoryTheory.Center C.Obj) :
    Mono ((actualAdjunction C).unit.app Z) := by
  let F := CategoryTheory.Center.forget C.Obj
  let u := (actualAdjunction C).unit.app Z
  have h : (F.map u) ≫ (underlyingCounit C).app Z.1 = 𝟙 Z.1 := unitCandidate_counit C Z
  letI : IsSplitMono (F.map u) := IsSplitMono.mk'
    { retraction := (underlyingCounit C).app Z.1
      id := h }
  exact F.mono_of_mono_map inferInstance

/-- Every centre object embeds into an explicitly induced injective object. -/
theorem center_enough_injectives : EnoughInjectives (CategoryTheory.Center C.Obj) where
  presentation Z := by
    exact ⟨{ J := (induction C).obj Z.1
             injective := induction_injective C Z.1
             f := (actualAdjunction C).unit.app Z
             mono := induction_unit_mono C Z }⟩

end PropertyF.Ground.CentreInduction
