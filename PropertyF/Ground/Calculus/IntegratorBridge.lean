module
public import PropertyF.Ground.Integrate.OverlapReduction
public import PropertyF.Ground.Calculus.TensorPowerCoherence

/-! Connect the proved overlap recurrence to the frozen integration interface. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u

/-- The integration interface's scalar-twisted overlap recurrence is a theorem
for every actual pivotal braided fusion category. -/
theorem twistedOverlapTrace_constructed (Z : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := Z.Obj))
    (σ : ℂ ≃+* ℂ) (y : Fin (Ground.rank Z)) :
    Ground.TwistedOverlapTrace Z p σ y := by
  let D := Ground.ScalarTwist.category Z σ
  let X : D.Obj := Ground.simples Z y
  let _ : Simple X := Ground.simples_simple Z y
  exact fun u k => overlap_trace_power D X (Ground.ScalarTwist.pivotal Z σ p) 1 u k

/-- The integrator's categorical Galois rigidity conclusion follows without
an overlap recurrence premise. -/
theorem positive_galois_rigidity (Z : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := Z.Obj))
    (hdim : ∀ i, Ground.Modular.simpleDimension Z p i = (Ground.fpSimple Z i : ℂ))
    (σ : ℂ ≃+* ℂ) (y : Fin (Ground.rank Z))
    (hF : ObjectPropertyF (Ground.simples Z y)) (d : ℝ)
    (hσ : σ (Ground.fpSimple Z y : ℂ) = (d : ℂ))
    (hS : σ (Ground.Modular.categoricalS Z p y y) = (d : ℂ) * Ground.fpSimple Z y) :
    Ground.fpSimple Z y = |d| :=
  Ground.rigidity_of_twisted_overlap Z p hdim σ y hF d hσ hS
    (twistedOverlapTrace_constructed Z p σ y)

/-- With the categorical overlap theorem supplied, the frozen target reduces
to spherical-structure existence and the actual centre/finite-image results. -/
theorem target_of_spherical_existence_and_center
    (hSpherical : ∀ (C : Ground.BraidedFusionCategory.{v,u}), Ground.PseudoUnitary C →
      ∃ p : Dimensions.PivotalStructure (C := C.Obj), p.IsSpherical)
    (hCenter : ∀ (C : Ground.BraidedFusionCategory.{v,u}), Ground.PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      ∃ (Z : Ground.BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := Z.Obj)),
        p.IsSpherical ∧
        (∀ i, Ground.Modular.simpleDimension Z p i = (Ground.fpSimple Z i : ℂ)) ∧
        (Ground.Modular.categoricalS Z p).det ≠ 0 ∧
        Ground.globalDimension Z = (Ground.globalFPDimension C : ℂ) ^ 2 ∧
        (∀ y, (∀ x, Ground.Modular.categoricalS Z p x y =
          (Ground.fpSimple Z y : ℂ) * σ.symm (Ground.Modular.simpleDimension Z p x)) →
          ObjectPropertyF (Ground.simples Z y))) : Ground.TargetStatement.{v,u} := by
  apply Ground.target_of_spherical_existence_center_and_overlap hSpherical
  intro C hPU hF σ
  obtain ⟨Z, p, hp, hdim, hdet, hglobal, hFtransfer⟩ := hCenter C hPU hF σ
  exact ⟨Z, p, hp, hdim, hdet, hglobal, hFtransfer,
    fun y _ => twistedOverlapTrace_constructed Z p σ y⟩

end PropertyF.Ground.Calculus
