module
public import PropertyF.Ground.Integrate.CenterSquareReduction

/-! A numerical core avoids identifying S-centrality with monodromy. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- The S-centralizer of the actual product-retract simples. -/
def numericalProductCore (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj)) :
    Set (Fin (rank (Integrate.bundledCenter C))) :=
  {y | ∀ a ∈ CentreCabling.productLabels C,
    Modular.categoricalS (Integrate.bundledCenter C) p a y =
      Modular.simpleDimension (Integrate.bundledCenter C) p a *
        Modular.simpleDimension (Integrate.bundledCenter C) p y}

/-- Actual-core integrality and the restricted finite-monodromy condition
imply numerical-core integrality. Thus the numerical route is no stronger
than the earlier pair of premises. -/
theorem numericalProductCore_integral_of_image_monodromy
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ))
    (hintegral : ∀ y ∈ CentreCabling.symmetricCore C,
      ∃ z : ℤ, Modular.simpleDimension (Integrate.bundledCenter C) p y = z)
    (hfinite : ∀ y, (∀ a ∈ CentreCabling.imageLabels C,
      Modular.categoricalS (Integrate.bundledCenter C) p a y =
        Modular.simpleDimension (Integrate.bundledCenter C) p a *
          Modular.simpleDimension (Integrate.bundledCenter C) p y) →
      ∀ a ∈ CentreCabling.imageLabels C, IsOfFinOrder (End.of (Modular.doubleBraiding
        (simples (Integrate.bundledCenter C) a) (simples (Integrate.bundledCenter C) y)))) :
    ∀ y ∈ numericalProductCore C p,
      ∃ z : ℤ, Modular.simpleDimension (Integrate.bundledCenter C) p y = z := by
  intro y hy
  apply hintegral y
  apply CentreCabling.numericalImageCentralizer_subset_symmetricCore C p hdim hfinite y
  intro a ha
  exact hy a (CentreCabling.imageLabels_subset_productLabels C ha)

/-- A direct integrality theorem for the numerical product core would remove
both actual-core identification and mixed-monodromy finite-order arguments.
The integrality and centre-structure premises are not asserted here. -/
theorem target_of_integral_numerical_center_core
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj →
      ∃ (hR : RigidCategory (CategoryTheory.Center C.Obj)),
        letI := hR
        ∃ (hFusion : IsFusionCategory (CategoryTheory.Center C.Obj)),
          letI := hFusion
          let Z := Integrate.bundledCenter C
          ∃ (p : Dimensions.PivotalStructure (C := Z.Obj)),
            p.IsSpherical ∧
            (∀ i, Modular.simpleDimension Z p i = (fpSimple Z i : ℂ)) ∧
            (Modular.categoricalS Z p).det ≠ 0 ∧
            (∀ y ∈ numericalProductCore C p,
              ∃ z : ℤ, Modular.simpleDimension Z p y = z)) : TargetStatement.{v,u} := by
  apply target_of_actual_center
  intro C hPU hF
  obtain ⟨hR, hFusion, p, hp, hdim, hdet, hintegral⟩ := hCenter C hPU hF
  letI := hR
  letI := hFusion
  refine ⟨hR, hFusion, p, numericalProductCore C p,
    (↑(CentreCabling.productLabels C) : Set _), hp, hdim, hdet,
    center_globalDimension_square_of_actual_induction C p hp hdim, hintegral, ?_, ?_⟩
  · intro y hy
    exact (CentreCabling.mem_productLabels C y).mpr
      (CentreCabling.productLabels_doubleCentralizer C p hp hdet hdim
        (numericalProductCore C p) (fun _ h => h) y hy)
  · intro y hy
    exact (CentreCabling.mem_productLabels C y).mp hy

end PropertyF.Ground
