module
public import MTC.PropertyF.Pivotal.ClosureFinalReduction
public import MTC.Braided.Cabling.PureSumPrefix

/-! # Closure and objectwise consequences -/

@[expose] public noncomputable section
open MTC.Braided MTC.Braided.Cabling
namespace MTC.PropertyF.Pivotal
universe v u

/-- The manuscript's closure lemma for the actual generated tensor category. -/
theorem closureStatement_proved : ClosureStatement.{v,u} :=
  closureStatement_of_positive_state_crossing_cabling
    (fun _ X n r s hs i => coloredPower_positive_mem X n r s hs i)

/-- The manuscript's eventual infinite braid-image corollary. -/
theorem objectwiseStatement_proved : ObjectwiseStatement.{v,u} :=
  objectwiseStatement_of_closure closureStatement_proved

end MTC.PropertyF.Pivotal
end
