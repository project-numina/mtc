module
public import PropertyF.Ground.Integrate.ActualCenterReduction
public import PropertyF.Ground.CentreCabling.ProductGenerated

/-! Wire the actual generated-centre closure into the target reduction. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- The product-retract identification is now a theorem: the remaining
centralizer input may be stated as membership in the tensor/sum/retract
closure of the two actual centre embeddings. The centre construction,
modularity, dimensions, integrality and double-centralizer implication remain
explicit premises. -/
theorem target_of_actual_center_generated
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj →
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
            (∀ y ∈ generated, Centre.ProductTensorClosure (simples Z y))) : TargetStatement.{v,u} := by
  apply target_of_actual_center
  intro C hPU hF
  obtain ⟨hR, hFusion, p, core, generated, hp, hdim, hdet, hglobal, hIntegral, hDouble, hProduct⟩ :=
    hCenter C hPU hF
  letI := hR
  letI := hFusion
  refine ⟨hR, hFusion, p, core, generated, hp, hdim, hdet, hglobal, hIntegral, hDouble, ?_⟩
  intro y hy
  exact (Centre.productRetract_iff_tensorClosure _).mpr (hProduct y hy)

end PropertyF.Ground
