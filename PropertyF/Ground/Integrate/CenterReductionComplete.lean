module
public import PropertyF.Ground.Integrate.CenterOnlyReduction
public import PropertyF.Ground.Calculus.TensorPowerCoherence

/-! Discharge overlap coherence and reduce the target to its modular centre. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- The actual scalar-twisted overlap recurrence holds for every simple. -/
theorem twistedOverlapTrace_proved (Z : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := Z.Obj)) (σ : ℂ ≃+* ℂ)
    (y : Fin (rank Z)) : TwistedOverlapTrace Z p σ y := by
  let D := ScalarTwist.category Z σ
  let X : D.Obj := simples Z y
  letI : Simple X := simples_simple Z y
  intro u k
  exact Calculus.overlap_trace_power D X (ScalarTwist.pivotal Z σ p) 1 u k

/-- The target follows from an actual positive spherical modular centre with
the global dimension and selected finite-braid-image properties. All of
these centre facts remain explicit premises. -/
theorem target_of_modular_center
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      ∃ (Z : BraidedFusionCategory.{v,max u v}) (p : Dimensions.PivotalStructure (C := Z.Obj)),
        p.IsSpherical ∧
        (∀ i, Modular.simpleDimension Z p i = (fpSimple Z i : ℂ)) ∧
        (Modular.categoricalS Z p).det ≠ 0 ∧
        globalDimension Z = (globalFPDimension C : ℂ) ^ 2 ∧
        (∀ y, (∀ x, Modular.categoricalS Z p x y =
          (fpSimple Z y : ℂ) * σ.symm (Modular.simpleDimension Z p x)) →
          ObjectPropertyF (simples Z y))) : TargetStatement.{v,u} := by
  apply target_of_center_and_overlap
  intro C hPU hF σ
  obtain ⟨Z, p, hp, hdim, hdet, hglobal, hfinite⟩ := hCenter C hPU hF σ
  exact ⟨Z, p, hp, hdim, hdet, hglobal, hfinite, fun y _ => twistedOverlapTrace_proved Z p σ y⟩

end PropertyF.Ground
