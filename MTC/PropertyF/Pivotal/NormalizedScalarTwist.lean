module
public import MTC.PropertyF.Pivotal.GaloisDimensionTransport

/-! # Transport of transparent-object normalization to scalar twists -/

@[expose] public noncomputable section
open CategoryTheory MTC.Fusion MTC.Braided MTC.Modular MTC.CategoryTheory.Dimensions
open MTC.PropertyF.Reduction
namespace MTC.PropertyF.Pivotal
universe v u
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
variable (σ : ℂ ≃+* ℂ)
local notation "Cσ" => ScalarTwist.category C σ
local notation "pσ" => ScalarTwist.pivotal C σ p

/-- If transparent simple FP dimensions are integers, a pivotal structure
normalized on transparent simples remains normalized on every scalar twist. -/
theorem normalized_transparent_scalarTwist
    (hnorm : ∀ i, MTC.Center.Transparent (simples C i) →
      simpleDimension C p i = (fpSimple C i : ℂ))
    (hint : ∀ i, MTC.Center.Transparent (simples C i) →
      ∃ n : ℕ, fpSimple C i = (n : ℝ))
    (j : Fin (rank Cσ)) (hj : MTC.Center.Transparent (simples Cσ j)) :
    simpleDimension Cσ pσ j = (fpSimple Cσ j : ℂ) := by
  letI : Simple (simples Cσ j) := simples_simple Cσ j
  obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso C (simples Cσ j)
  have hi : MTC.Center.Transparent (simples C i) := transparent_of_iso C e.symm hj
  obtain ⟨n, hn⟩ := hint i hi
  have hd : pivotalDimension Cσ pσ (simples Cσ j) =
      σ (pivotalDimension C p (simples C i)) := by
    rw [pivotalDimension_iso pσ e]
    exact ScalarTwist.pivotalDimension_twist C σ p _
  have hf : fpSimple Cσ j = fpSimple C i := by
    calc
      fpSimple Cσ j = fpDimension Cσ (simples Cσ j) := (fpDimension_simple j).symm
      _ = fpDimension C (simples Cσ j) := ScalarTwist.fpDimension_twist C σ _
      _ = fpDimension C (simples C i) := fpDimension_iso e
      _ = fpSimple C i := fpDimension_simple i
  have hdim : pivotalDimension C p (simples C i) = (fpSimple C i : ℂ) := hnorm i hi
  change pivotalDimension Cσ pσ (simples Cσ j) = _
  rw [hd, hdim, hf, hn]
  simp

end MTC.PropertyF.Pivotal
end
