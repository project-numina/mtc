module
public import PropertyF.Ground.Integrate.Reduction

/-! Reserved for the final `PropertyF.Ground.target : TargetStatement` theorem.
The statement remains in `Target.lean`; keeping the proof downstream avoids a
module cycle with the integration results. No theorem is asserted until both
premises of the reduction have been proved. -/
