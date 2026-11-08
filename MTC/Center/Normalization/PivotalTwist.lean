module
public import MTC.CategoryTheory.Dimensions.TensorExtension

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # Pivotal twists from fusion-compatible scalar labels

A multiplicative assignment of nonzero scalars to simple objects defines an
actual pivotal twist. This is the categorical step used by universal-grading
characters; it does not construct the universal grading.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.Center.Normalization
universe v u
variable {C : BraidedFusionCategory.{v,u}}
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false

/-- A pivotal structure as a natural isomorphism to the double-dual functor. -/
def pivotalNaturalIso (p : PivotalStructure (C := C.Obj)) : 𝟭 C.Obj ≅ doubleDualFunctor C.Obj :=
  NatIso.ofComponents p.iso (fun f ↦ p.naturality f)

/-- Twist the pivotal natural isomorphism by a scalar assignment on simples. -/
def scalarTwistedNaturalIso (p : PivotalStructure (C := C.Obj))
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0) : 𝟭 C.Obj ≅ doubleDualFunctor C.Obj :=
  simpleScalarNaturalIso C c hc ≪≫ pivotalNaturalIso p

/-- The twisted component on a simple is the given scalar times the old one. -/
theorem scalarTwistedNaturalIso_app_simple (p : PivotalStructure (C := C.Obj))
    {c : Fin (rank C) → ℂ} (hc : ∀ i, c i ≠ 0) (i : Fin (rank C)) :
    ((scalarTwistedNaturalIso p c hc).app (simples C i)).hom = c i • (p.iso (simples C i)).hom := by
  change ((simpleScalarNaturalIso C c hc).app (simples C i)).hom ≫ _ = _
  rw [simpleScalarNaturalIso_app_simple]
  simp [pivotalNaturalIso]

/-- The twist has the old dimension multiplied by the prescribed scalar. -/
theorem scalarTwistedNaturalIso_dimension (p : PivotalStructure (C := C.Obj))
    {c : Fin (rank C) → ℂ} (hc : ∀ i, c i ≠ 0) (i : Fin (rank C)) :
    unitScalar C (rightQuantumTrace ((scalarTwistedNaturalIso p c hc).app (simples C i))) =
      c i * pivotalDimension C p (simples C i) := by
  simpa only [pivotalDimension, rightTrace_id, unitScalar_eq_equiv, map_smul, smul_eq_mul] using
    congrArg (unitScalarEquiv C) (rightQuantumTrace_smul_hom (scalarTwistedNaturalIso_app_simple p hc i))

/-- Multiplicative scalars have the correct tensor comparison on simples. -/
theorem scalarTwistedNaturalIso_tensor_simples (p : PivotalStructure (C := C.Obj))
    {c : Fin (rank C) → ℂ} (hc : ∀ i, c i ≠ 0)
    (hmul : ∀ i j k, 0 < fusionCoeff C i j k → c k = c i * c j)
    (i j : Fin (rank C)) :
    ((scalarTwistedNaturalIso p c hc).app (simples C i ⊗ simples C j)).hom =
      (((scalarTwistedNaturalIso p c hc).app (simples C i)).hom ⊗ₘ
        ((scalarTwistedNaturalIso p c hc).app (simples C j)).hom) ≫
        (doubleDualTensorIso (simples C i) (simples C j)).hom := by
  let X := simples C i ⊗ simples C j
  let a := scalarTwistedNaturalIso p c hc
  apply biproduct_decomposition_hom_ext (simpleDecomposition C X)
  rintro ⟨k, t⟩
  let f := simpleInclusion C X k t
  have hpos : 0 < fusionCoeff C i j k := by
    change 0 < simpleMultiplicity C k X
    exact Nat.zero_le _ |>.trans_lt t.isLt
  have hn := a.hom.naturality f
  change f ≫ (a.app X).hom = (a.app (simples C k)).hom ≫ ((fᘁ)ᘁ) at hn
  have hp := p.naturality f
  rw [scalarTwistedNaturalIso_app_simple p hc, scalarTwistedNaturalIso_app_simple p hc]
  have hscale : (c i • (p.iso (simples C i)).hom) ⊗ₘ (c j • (p.iso (simples C j)).hom) =
      (c i * c j) • ((p.iso (simples C i)).hom ⊗ₘ (p.iso (simples C j)).hom) := by
    simp [tensorHom_def, smul_smul, mul_comm]
  rw [hscale]
  simp only [Linear.smul_comp, Linear.comp_smul]
  change f ≫ (a.app X).hom = (c i * c j) • (f ≫ ((p.iso (simples C i)).hom ⊗ₘ
    (p.iso (simples C j)).hom) ≫ (doubleDualTensorIso _ _).hom)
  rw [← p.tensor, hn, scalarTwistedNaturalIso_app_simple p hc, Linear.smul_comp, ← hp, hmul i j k hpos]

/-- A fusion-compatible scalar assignment twists an actual pivotal structure. -/
def scalarPivotalTwist (p : PivotalStructure (C := C.Obj))
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hunit : c (unitIndex C) = 1)
    (hmul : ∀ i j k, 0 < fusionCoeff C i j k → c k = c i * c j) :
    PivotalStructure (C := C.Obj) where
  iso X := (scalarTwistedNaturalIso p c hc).app X
  naturality f := (scalarTwistedNaturalIso p c hc).hom.naturality f
  tensor X Y := doubleDualTensor_extension C (scalarTwistedNaturalIso p c hc)
    (scalarTwistedNaturalIso_tensor_simples p hc hmul) X Y
  unit := naturalDoubleDual_unit_eq_of_trace_one <| (unitIndex_iso C).elim fun e ↦ by
    rw [← rightQuantumTrace_iso
      (j := (scalarTwistedNaturalIso p c hc).app (simples C (unitIndex C)))
      (k := (scalarTwistedNaturalIso p c hc).app (𝟙_ C.Obj)) e
      (by simpa [doubleDualFunctor] using (scalarTwistedNaturalIso p c hc).hom.naturality e.hom),
      scalarTwistedNaturalIso_dimension, hunit, pivotalDimension_unitIndex, mul_one]

/-- The actual pivotal twist multiplies simple dimensions by the given scalars. -/
theorem scalarPivotalTwist_dimension (p : PivotalStructure (C := C.Obj))
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (hunit : c (unitIndex C) = 1)
    (hmul : ∀ i j k, 0 < fusionCoeff C i j k → c k = c i * c j) (i : Fin (rank C)) :
    pivotalDimension C (scalarPivotalTwist p c hc hunit hmul) (simples C i) =
      c i * pivotalDimension C p (simples C i) := by
  simpa only [pivotalDimension, rightTrace_id, scalarPivotalTwist] using
    scalarTwistedNaturalIso_dimension p hc i

end MTC.Center.Normalization
end
