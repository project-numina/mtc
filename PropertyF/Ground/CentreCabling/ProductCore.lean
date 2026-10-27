module
public import PropertyF.Ground.CentreCabling.CentralityClosure
public import PropertyF.Ground.CentreCabling.TraceSaturation
public import PropertyF.Ground.CentreCabling.ProductGenerated
public import PropertyF.Ground.CentreCabling.RegularSupport
public import PropertyF.Ground.Fusion.UnitPower

/-!
# Product labels and the symmetric core

The product-retract labels are closed under tensor constituents and duals.
Their numerical double centralizer is related to the actual symmetric core
using finite-order monodromy and trace saturation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCabling
universe v u
variable (C : Ground.BraidedFusionCategory.{v,u})
  [RigidCategory (CategoryTheory.Center C.Obj)]
  [IsFusionCategory (CategoryTheory.Center C.Obj)]

/-- The actual centre simple labels which are retracts of product images. -/
def productLabels : Finset (Fin (rank (Integrate.bundledCenter C))) := by
  classical
  exact Finset.univ.filter (fun i => Centre.ProductRetract (simples (Integrate.bundledCenter C) i))

theorem mem_productLabels (i : Fin (rank (Integrate.bundledCenter C))) :
    i ∈ productLabels C ↔ Centre.ProductRetract (simples (Integrate.bundledCenter C) i) := by
  classical
  simp [productLabels]

theorem unit_mem_productLabels : unitIndex (Integrate.bundledCenter C) ∈ productLabels C := by
  rw [mem_productLabels]
  obtain ⟨e⟩ := unitIndex_iso (Integrate.bundledCenter C)
  exact Centre.productRetract_of_retract (Retract.ofIso e) Centre.unit_productRetract

theorem dual_mem_productLabels (i : Fin (rank (Integrate.bundledCenter C)))
    (hi : i ∈ productLabels C) : dualIndex (Integrate.bundledCenter C) i ∈ productLabels C := by
  rw [mem_productLabels] at hi ⊢
  let Z := Integrate.bundledCenter C
  let X : CategoryTheory.Center C.Obj := simples Z i
  have hr := Centre.productRetract_rightDual C hi
  let e : (ᘁX) ≅ (Xᘁ) := leftDualIso HasLeftDual.exact
    (BraidedCategory.exactPairing_swap X (Xᘁ))
  obtain ⟨e'⟩ := dualIndex_iso Z i
  exact Centre.productRetract_of_retract (Retract.ofIso (e'.symm ≪≫ e)) hr

theorem constituent_mem_productLabels
    (i j k : Fin (rank (Integrate.bundledCenter C)))
    (hi : i ∈ productLabels C) (hj : j ∈ productLabels C)
    (hk : 0 < fusionCoeff (Integrate.bundledCenter C) i j k) : k ∈ productLabels C := by
  rw [mem_productLabels] at hi hj ⊢
  obtain ⟨r⟩ := Ground.fusionCoeff_retract (Integrate.bundledCenter C) i j k hk
  exact Centre.productRetract_of_retract r (Centre.productRetract_tensor hi hj)

/-- The centre's product-retract labels satisfy the numerical double-centralizer
inclusion whenever the chosen core contains their numerical centralizer. -/
theorem productLabels_doubleCentralizer
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hp : p.IsSpherical) (hdet : (Modular.categoricalS (Integrate.bundledCenter C) p).det ≠ 0)
    (hdim : ∀ j, Modular.simpleDimension (Integrate.bundledCenter C) p j =
      (fpSimple (Integrate.bundledCenter C) j : ℂ))
    (core : Set (Fin (rank (Integrate.bundledCenter C))))
    (hcore : ∀ y, (∀ a ∈ productLabels C,
      Modular.categoricalS (Integrate.bundledCenter C) p a y =
        Modular.simpleDimension (Integrate.bundledCenter C) p a *
          Modular.simpleDimension (Integrate.bundledCenter C) p y) → y ∈ core) :
    ∀ x, (∀ y ∈ core, Modular.categoricalS (Integrate.bundledCenter C) p y x =
      Modular.simpleDimension (Integrate.bundledCenter C) p y *
        Modular.simpleDimension (Integrate.bundledCenter C) p x) →
      Centre.ProductRetract (simples (Integrate.bundledCenter C) x) := by
  intro x hx
  apply (mem_productLabels C x).mp
  exact doubleCentralizer_of_fusion_closed (Integrate.bundledCenter C) p hp hdet hdim
    (productLabels C) core (unit_mem_productLabels C) (dual_mem_productLabels C)
    (fun i hi j hj k hk => constituent_mem_productLabels C i j k hi hj hk) hcore x hx


/-- Actual centre labels centralizing both canonical images. -/
def symmetricCore : Set (Fin (rank (Integrate.bundledCenter C))) :=
  {y | (∀ X : C.Obj, Centre.Centralizes (simples (Integrate.bundledCenter C) y)
      ((CategoryTheory.Center.ofBraided C.Obj).obj X)) ∧
    (∀ X : C.Obj, Centre.Centralizes (simples (Integrate.bundledCenter C) y)
      ((Centre.negative C.Obj).obj X))}

end PropertyF.Ground.CentreCabling
