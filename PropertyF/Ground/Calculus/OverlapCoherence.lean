module
public import PropertyF.Ground.Calculus.StrandCoherence
public import PropertyF.Ground.Calculus.ThreeTrace

/-! The exact tensor-power coherence needed for the overlap trace step. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Identify the previous tensor power as a prefix followed by its final
strand, then append the new tail. -/
def overlapPowerIso (X : C) (t k : ℕ) :
    (tensorPower X (overlapIndex t k + 1) ⊗ X) ⊗ tensorPower X (t + 1) ≅
      tensorPower X (overlapIndex t (k + 1) + 2) :=
  (appendIso X (overlapIndex t k + 1) ⊗ᵢ Iso.refl (tensorPower X (t + 1))) ≪≫
    insertRightPowerIso X (overlapIndex t k) (t + 1)

/-- The previous overlap operator expressed with its last strand explicit. -/
def previousOverlapLocal (X : C) (t k : ℕ) (u : braidAlgebra X t) :
    End (tensorPower X (overlapIndex t k + 1) ⊗ X) :=
  (isoEndAlgEquiv (appendIso X (overlapIndex t k + 1)).symm)
    (overlapProduct X t u k : End (tensorPower X (overlapIndex t k + 2)))

set_option backward.isDefEq.respectTransparency false in
/-- Under the overlap isomorphism the previous braid is exactly the local
endomorphism with identity on the new tail. -/
theorem overlapLeft_local (X : C) (t k : ℕ) (v : braidAlgebra X (overlapIndex t k)) :
    (isoEndAlgEquiv (overlapPowerIso X t k).symm)
      (overlapLeft X t k v : End (tensorPower X (overlapIndex t (k + 1) + 2))) =
    insertRightIdentity (tensorPower X (overlapIndex t k + 1) ⊗ X) (tensorPower X (t + 1))
      ((isoEndAlgEquiv (appendIso X (overlapIndex t k + 1)).symm)
        (v : End (tensorPower X (overlapIndex t k + 2)))) := by
  apply End.ext
  change (overlapPowerIso X t k).hom ≫
    ((addRightBraidAlgebraIter X (overlapIndex t k) (t + 1) v :
      braidAlgebra X (overlapIndex t k + (t + 1))) :
      End (tensorPower X ((overlapIndex t k + (t + 1)) + 2))).asHom ≫
    (overlapPowerIso X t k).inv =
      ((appendIso X (overlapIndex t k + 1)).hom ≫
        (v : End (tensorPower X (overlapIndex t k + 2))).asHom ≫
        (appendIso X (overlapIndex t k + 1)).inv) ▷ tensorPower X (t + 1)
  rw [addRightBraidAlgebraIter_asHom]
  simp [overlapPowerIso, tensorIso_hom, tensorIso_inv, tensorHom_id,
    comp_whiskerRight, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Identifying the actual product with the local graphical overlap implies
the precise one-step trace recurrence. -/
theorem overlap_trace_step_of_coherence (D : Ground.BraidedFusionCategory.{v,u})
    (X : D.Obj) [Simple X] (p : Dimensions.PivotalStructure (C := D.Obj))
    (t k : ℕ) (u : braidAlgebra X t)
    (hcoh : (isoEndAlgEquiv (overlapPowerIso X t k).symm)
        (overlapProduct X t u (k + 1) : End (tensorPower X (overlapIndex t (k + 1) + 2))) =
      overlapEndProduct (tensorPower X (overlapIndex t k + 1)) X (tensorPower X (t + 1))
        (previousOverlapLocal X t k u) (u : End (tensorPower X (t + 2)))) :
    actualBraidTrace D X p (overlapIndex t (k + 1)) (overlapProduct X t u (k + 1)) *
        Dimensions.groundUnitScalarEquiv D (p.rightTrace (𝟙 X)) =
      actualBraidTrace D X p (overlapIndex t k) (overlapProduct X t u k) *
        actualBraidTrace D X p t u := by
  have hh := congrArg
    (fun z => Dimensions.groundUnitScalarEquiv D (p.rightTrace z.asHom)) hcoh
  simp only [rightTrace_iso_conj] at hh
  rw [pivotalTrace_overlap D _ X _ p (Dimensions.groundUnitScalarEquiv D)] at hh
  simp only [previousOverlapLocal, rightTrace_iso_conj] at hh
  have hδ : Dimensions.groundUnitScalarEquiv D (p.rightTrace (𝟙 X)) ≠ 0 := by
    intro h
    apply Modular.pivotalTrace_simple_ne_zero D p X
    apply (Dimensions.groundUnitScalarEquiv D).injective
    simpa using h
  change actualBraidTrace D X p _ _ = actualBraidTrace D X p _ _ *
    (actualBraidTrace D X p t u / _) at hh
  rw [hh]
  field_simp

end PropertyF.Ground.Calculus
