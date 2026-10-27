module
public import PropertyF.Ground.CentreInduction.ActualFusion
public import PropertyF.Ground.Modular.SAdditivity
public import PropertyF.Ground.CentreModular.KirbyCriterion

/-! Express the centre Kirby colour through its actual induction functor. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Expand an arbitrary Hopf link in actual simple-object multiplicities. -/
theorem SEntry_simple_decomposition (D : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj)) (X : D.Obj) (k : Fin (rank D)) :
    unitScalarEquiv D (Modular.SEntry p X (simples D k)) =
      ∑ j, (Module.finrank ℂ (simples D j ⟶ X) : ℂ) * Modular.categoricalS D p j k := by
  let m : Fin (rank D) → ℕ := fun j => Module.finrank ℂ (simples D j ⟶ X)
  let V : (Σ j, Fin (m j)) → D.Obj := fun t => simples D t.1
  obtain ⟨e⟩ := exists_canonical_decomposition D X
  have he : Modular.SEntry p X (simples D k) = Modular.SEntry p (⨁ V) (simples D k) :=
    Modular.SEntry_iso_left p e _
  rw [he, Modular.SEntry_biproduct_left]
  simp [Fintype.sum_sigma, V, m, Modular.categoricalS, nsmul_eq_mul]

/-- The FP-weighted centre Kirby colour equals the FP-weighted family of
actual induced base simples, as tested by every Hopf link. -/
theorem center_kirby_sum_eq_induced (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (k : Fin (rank (Integrate.bundledCenter C))) :
    (∑ j, (fpSimple (Integrate.bundledCenter C) j : ℂ) *
      Modular.categoricalS (Integrate.bundledCenter C) pZ j k) =
    ∑ i, (fpSimple C i : ℂ) * unitScalarEquiv (Integrate.bundledCenter C)
      (Modular.SEntry pZ ((CentreInduction.induction C).obj (simples C i))
        (simples (Integrate.bundledCenter C) k)) := by
  classical
  let Z := Integrate.bundledCenter C
  have hbase (j : Fin (rank Z)) :
      ∑ i, (Module.finrank ℂ ((simples Z j).1 ⟶ simples C i) : ℝ) * fpSimple C i =
        fpSimple Z j := by
    calc
      _ = fpDimension C (simples Z j).1 := by
        unfold fpDimension
        apply Finset.sum_congr rfl
        intro i _
        rw [finrank_to_simple_eq_from_simple C]
      _ = fpDimension Z (simples Z j) := Integrate.center_forget_fpDimension C _
      _ = _ := fpDimension_simple Z j
  have hmult (i : Fin (rank C)) (j : Fin (rank Z)) :
      Module.finrank ℂ (simples Z j ⟶ (CentreInduction.induction C).obj (simples C i)) =
        Module.finrank ℂ ((simples Z j).1 ⟶ simples C i) :=
    (CentreInduction.homLinearEquivOfAdjunction (CategoryTheory.Center.forget C.Obj)
      (CentreInduction.induction C) (CentreInduction.actualAdjunction C)
      (simples Z j) (simples C i)).finrank_eq
  have hentry (i : Fin (rank C)) :
      unitScalarEquiv Z (Modular.SEntry pZ ((CentreInduction.induction C).obj (simples C i))
        (simples Z k)) = ∑ j, (Module.finrank ℂ ((simples Z j).1 ⟶ simples C i) : ℂ) *
          Modular.categoricalS Z pZ j k := by
    rw [SEntry_simple_decomposition Z pZ]
    simp_rw [hmult]
  change (∑ j, (fpSimple Z j : ℂ) * Modular.categoricalS Z pZ j k) =
    ∑ i, (fpSimple C i : ℂ) * unitScalarEquiv Z
      (Modular.SEntry pZ ((CentreInduction.induction C).obj (simples C i)) (simples Z k))
  simp_rw [hentry, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have hc : (∑ i, (fpSimple C i : ℂ) *
      (Module.finrank ℂ ((simples Z j).1 ⟶ simples C i) : ℂ)) = (fpSimple Z j : ℂ) := by
    have hh := congrArg (fun x : ℝ => (x : ℂ)) (hbase j)
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc]

/-- The centre S matrix is invertible if the explicitly induced Kirby loop
vanishes on non-unit simples. The loop evaluation is an open premise. -/
theorem center_S_invertible_of_induced_loop_vanishing
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hdim : ∀ j, Modular.simpleDimension (Integrate.bundledCenter C) pZ j =
      (fpSimple (Integrate.bundledCenter C) j : ℂ))
    (hloop : ∀ k, k ≠ unitIndex (Integrate.bundledCenter C) →
      (∑ i, (fpSimple C i : ℂ) * unitScalarEquiv (Integrate.bundledCenter C)
        (Modular.SEntry pZ ((CentreInduction.induction C).obj (simples C i))
          (simples (Integrate.bundledCenter C) k))) = 0) :
    (Modular.categoricalS (Integrate.bundledCenter C) pZ).det ≠ 0 := by
  apply categoricalS_det_ne_zero_of_kirby_vanishes_off_unit (Integrate.bundledCenter C) pZ hdim
  intro k hk
  simp_rw [hdim, Modular.categoricalS_symmetric (Integrate.bundledCenter C) pZ k]
  rw [center_kirby_sum_eq_induced C pZ k]
  exact hloop k hk

end PropertyF.Ground.CentreModular
