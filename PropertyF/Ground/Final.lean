module
public import PropertyF.Ground.Integrate.DrinfeldComplete
public import PropertyF.Ground.CentreInduction.DrinfeldTheorem

/-! The unconditional frozen target for genuine braided fusion categories. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- A braided fusion category with property F and a pseudo-unitary Galois
conjugate has integral global Frobenius–Perron dimension. -/
theorem target : TargetStatement.{v,u} := by
  apply target_of_pseudoUnitary_pivotal_existence
  intro C hpu _
  obtain ⟨p, _, _⟩ := CentreInduction.positive_spherical_of_pseudoUnitary C hpu
  exact ⟨p⟩

end PropertyF.Ground
