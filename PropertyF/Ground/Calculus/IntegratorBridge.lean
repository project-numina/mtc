module
public import PropertyF.Ground.Integrate.TwistedRigidity
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

end PropertyF.Ground.Calculus
