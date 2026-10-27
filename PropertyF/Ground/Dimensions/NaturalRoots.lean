module
public import PropertyF.Ground.Dimensions.SimpleScalars
public import Mathlib.CategoryTheory.Whiskering

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Scalar comparing the chosen simple fourth-dual square root to the
braided double-dual component. -/
def fourthDualRootScalar (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) : ℂ := by
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  exact Classical.choose (isomorphisms_differ_by_scalar C
    (Ground.doubleDualIso C (Ground.simples C i)) (fourthDualSimpleRoot C i))

theorem fourthDualRootScalar_spec (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) : fourthDualRootScalar C i ≠ 0 ∧
    (fourthDualSimpleRoot C i).hom = fourthDualRootScalar C i •
      (Ground.doubleDualIso C (Ground.simples C i)).hom := by
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  exact Classical.choose_spec (isomorphisms_differ_by_scalar C
    (Ground.doubleDualIso C (Ground.simples C i)) (fourthDualSimpleRoot C i))

/-- The chosen simple square roots extend to a natural isomorphism from the
identity to the double-dual functor. It is not asserted to be monoidal. -/
def fourthDualRootNaturalIso (C : Ground.BraidedFusionCategory.{v,u}) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj :=
  simpleScalarNaturalIso C (fourthDualRootScalar C) (fun i => (fourthDualRootScalar_spec C i).1) ≪≫
    drinfeldNaturalIso C

/-- The natural extension has exactly the chosen simple components. -/
theorem fourthDualRootNaturalIso_app_simple (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) :
    (fourthDualRootNaturalIso C).app (Ground.simples C i) = fourthDualSimpleRoot C i := by
  apply Iso.ext
  simp only [fourthDualRootNaturalIso, NatIso.trans_app, Iso.trans_hom,
    simpleScalarNaturalIso_app_simple]
  change (fourthDualRootScalar C i • 𝟙 (Ground.simples C i)) ≫
    (Ground.doubleDualIso C (Ground.simples C i)).hom = _
  simpa using (fourthDualRootScalar_spec C i).2.symm

/-- Natural transformations from the identity are determined by their
components on the simple representatives. -/
theorem natTrans_eq_of_simple_components (C : Ground.BraidedFusionCategory.{v,u})
    (F : C.Obj ⥤ C.Obj) (α β : 𝟭 C.Obj ⟶ F)
    (h : ∀ i, α.app (Ground.simples C i) = β.app (Ground.simples C i)) : α = β := by
  apply NatTrans.ext
  funext X
  classical
  obtain ⟨m, ⟨e⟩⟩ := Ground.simples_decompose C X
  let V : (Σ i, Fin (m i)) → C.Obj := fun a => Ground.simples C a.1
  have hs : α.app (⨁ V) = β.app (⨁ V) := by
    apply biproduct.hom_ext'
    intro a
    have hα := α.naturality (biproduct.ι V a)
    have hβ := β.naturality (biproduct.ι V a)
    simp only [Functor.id_map] at hα hβ
    rw [hα, hβ, h a.1]
  apply (cancel_mono (F.map e.hom)).1
  have hα := α.naturality e.hom
  have hβ := β.naturality e.hom
  simp only [Functor.id_map] at hα hβ
  rw [← hα, ← hβ, hs]

/-- The natural double-dual root, squared using the double-dual functor. -/
def fourthDualRootNaturalSquare (C : Ground.BraidedFusionCategory.{v,u}) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj ⋙ doubleDualFunctor C.Obj :=
  fourthDualRootNaturalIso C ≪≫
    Functor.isoWhiskerRight (fourthDualRootNaturalIso C) (doubleDualFunctor C.Obj)

/-- The natural double-dual root squares to the natural braided fourth-dual
isomorphism on every object. Monoidal compatibility remains a separate issue. -/
theorem fourthDualRootNaturalSquare_eq (C : Ground.BraidedFusionCategory.{v,u}) :
    fourthDualRootNaturalSquare C = fourthDualNaturalIso C := by
  apply Iso.ext
  apply natTrans_eq_of_simple_components C
  intro i
  change ((fourthDualRootNaturalIso C).app (Ground.simples C i)).hom ≫
    ((((fourthDualRootNaturalIso C).app (Ground.simples C i)).homᘁ)ᘁ) =
      (fourthDualIso C (Ground.simples C i)).hom
  rw [fourthDualRootNaturalIso_app_simple]
  exact congrArg Iso.hom (fourthDualSimpleRoot_sq C i)

end PropertyF.Ground.Dimensions
