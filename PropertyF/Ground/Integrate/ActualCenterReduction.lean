module
public import PropertyF.Ground.Integrate.CenterProductBridge
public import PropertyF.Ground.Integrate.CenterBundle

/-! State the remaining inputs on Mathlib’s actual Drinfeld centre. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- The target follows from explicit rigidity, fusion, modularity, dimension
and centralizer assertions about the actual centre. Those assertions remain
unproved premises of this reduction. -/
theorem target_of_actual_center
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      ∃ (hR : RigidCategory (CategoryTheory.Center C.Obj)),
        letI := hR
        ∃ (hFusion : IsFusionCategory (CategoryTheory.Center C.Obj)),
          letI := hFusion
          let Z := Integrate.bundledCenter C
          ∃ (p : Dimensions.PivotalStructure (C := Z.Obj))
            (core generated : Set (Fin (rank Z))),
            p.IsSpherical ∧
            (∀ i, Modular.simpleDimension Z p i = (fpSimple Z i : ℂ)) ∧
            (Modular.categoricalS Z p).det ≠ 0 ∧
            globalDimension Z = (globalFPDimension C : ℂ) ^ 2 ∧
            (∀ x ∈ core, ∃ z : ℤ, Modular.simpleDimension Z p x = z) ∧
            (∀ y, (∀ x ∈ core, Modular.categoricalS Z p x y =
              Modular.simpleDimension Z p x * Modular.simpleDimension Z p y) → y ∈ generated) ∧
            (∀ y ∈ generated, Centre.ProductRetract (simples Z y))) : TargetStatement.{v,u} := by
  apply target_of_center_product_retracts
  intro C hPU hF σ
  obtain ⟨hR, hFusion, p, core, generated, hp, hdim, hdet, hglobal, hIntegral, hDouble, hProduct⟩ :=
    hCenter C hPU hF σ
  letI := hR
  letI := hFusion
  have hB : (𝟭 (CategoryTheory.Center C.Obj)).Braided := inferInstance
  have hfaithful : (𝟭 (CategoryTheory.Center C.Obj)).Faithful := inferInstance
  exact ⟨Integrate.bundledCenter C, p, 𝟭 (CategoryTheory.Center C.Obj), ⟨hB⟩, hfaithful,
    core, generated, hp, hdim, hdet, hglobal, hIntegral, hDouble, hProduct⟩

end PropertyF.Ground
