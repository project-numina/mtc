module
public import MTC.PropertyF.Pivotal.GlobalCriterionConsequences
public import MTC.PropertyF.Pivotal.NondegeneracyRelative

/-! # The pivotal property-F theorems

The numerical-to-actual centrality theorem is proved for arbitrary pivotal
structures by the restricted categorical Haar slide. It closes both
manuscript main statements without sphericality or positivity assumptions
beyond those stated in each target.
-/

@[expose] public noncomputable section
open CategoryTheory MTC.Fusion MTC.Modular MTC.Braided MTC.CategoryTheory.Dimensions
open MTC.Center.Braid
namespace MTC.PropertyF.Pivotal
universe v u

/-- The manuscript's full nondegenerate pivotal theorem. -/
theorem nondegenerateMainStatement_proved : NondegenerateMainStatement.{v,u} :=
  nondegenerateStatement_of_relative_fusion_criterion
    (fun D p A hA y hs a ha => relative_fusionSubring_numerical_centrality D p A hA y hs a ha)

/-- The manuscript's full degenerate pivotal theorem under its stated
positivity hypothesis on the transparent adjoint simples. -/
theorem degenerateMainStatement_proved : DegenerateMainStatement.{v,u} :=
  degenerateStatement_of_relative_fusion_criterion
    (fun D p A hA y hs a ha => relative_fusionSubring_numerical_centrality D p A hA y hs a ha)

end MTC.PropertyF.Pivotal
end
