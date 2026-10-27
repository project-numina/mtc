module
public import PropertyF.Ground.Dimensions.Drinfeld
public import PropertyF.Ground.Dimensions.Norm
public import PropertyF.Ground.Fusion.Simples
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Right-dual mates are complex-linear in the morphism. -/
theorem rightAdjointMate_smul {X Y : C} (c : ℂ) (f : X ⟶ Y) :
    (c • f)ᘁ = c • (fᘁ) := by
  simp [rightAdjointMate]

/-- Rescaling an isomorphism by a nonzero scalar preserves invertibility. -/
def scaleIso {X Y : C} (e : X ≅ Y) (c : ℂ) (hc : c ≠ 0) : X ≅ Y where
  hom := c • e.hom
  inv := c⁻¹ • e.inv
  hom_inv_id := by simp [smul_smul, hc]
  inv_hom_id := by simp [smul_smul, hc]

end PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Dimensions
universe v u

/-- On a simple object, any two isomorphisms to a fixed target differ by a
nonzero scalar. -/
theorem isomorphisms_differ_by_scalar (C : Ground.BraidedFusionCategory.{v,u})
    {X Y : C.Obj} [Simple X] (e f : X ≅ Y) :
    ∃ c : ℂ, c ≠ 0 ∧ f.hom = c • e.hom := by
  let : FiniteDimensional ℂ (X ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ (f.hom ≫ e.inv)
  have hhom : f.hom = c • e.hom := by
    calc
      f.hom = (f.hom ≫ e.inv) ≫ e.hom := by simp
      _ = c • e.hom := by rw [← hc]; simp
  have hc0 : c ≠ 0 := by
    intro h
    have hh : f.hom = 0 := by simp [h, hhom]
    have hid : 𝟙 X = 0 := by simpa using congrArg (fun g => g ≫ f.inv) hh
    exact id_nonzero X hid
  exact ⟨c, hc0, hhom⟩

/-- For every simple object, any prescribed fourth-dual isomorphism has a
square root through the double dual. No monoidality or naturality is assumed. -/
theorem exists_fourthDual_square_root (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] (g : X ≅ ((((Xᘁ)ᘁ)ᘁ)ᘁ)) :
    ∃ a : X ≅ ((Xᘁ)ᘁ), a ≪≫ rightDualIsoMap (rightDualIsoMap a) = g := by
  let e := Ground.doubleDualIso C X
  let e2 := e ≪≫ rightDualIsoMap (rightDualIsoMap e)
  obtain ⟨c, hc0, hc⟩ := isomorphisms_differ_by_scalar C e2 g
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by decide)
  have hz0 : z ≠ 0 := by
    intro h
    apply hc0
    simpa [h] using hz.symm
  refine ⟨scaleIso e z hz0, ?_⟩
  apply Iso.ext
  change (z • e.hom) ≫ (((z • e.hom)ᘁ)ᘁ) = g.hom
  rw [rightAdjointMate_smul, rightAdjointMate_smul, Linear.smul_comp, Linear.comp_smul, smul_smul]
  rw [← pow_two, hz]
  change c • e2.hom = g.hom
  exact hc.symm

/-- A chosen square root of the natural braided fourth-dual map on each
simple representative. -/
def fourthDualSimpleRoot (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    Ground.simples C i ≅ ((Ground.simples C i)ᘁ)ᘁ := by
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  exact Classical.choose (exists_fourthDual_square_root C (Ground.simples C i)
    (fourthDualIso C (Ground.simples C i)))

/-- The chosen simple component squares to the natural fourth-dual component. -/
theorem fourthDualSimpleRoot_sq (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    fourthDualSimpleRoot C i ≪≫ rightDualIsoMap (rightDualIsoMap (fourthDualSimpleRoot C i)) =
      fourthDualIso C (Ground.simples C i) := by
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  exact Classical.choose_spec (exists_fourthDual_square_root C (Ground.simples C i)
    (fourthDualIso C (Ground.simples C i)))

end PropertyF.Ground.Dimensions
