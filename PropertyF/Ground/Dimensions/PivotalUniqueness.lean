module
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Fusion.Agreement

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Pivotal structures with equal dimensions on simple objects have the same
components there. Simple dimension nonvanishing is essential for cancellation. -/
theorem pivotal_components_eq_on_simples (C : Ground.BraidedFusionCategory.{v,u})
    (p q : PivotalStructure (C := C.Obj))
    (hd : ∀ i, pivotalDimension C p (Ground.simples C i) =
      pivotalDimension C q (Ground.simples C i)) (i : Fin (Ground.rank C)) :
    (p.iso (Ground.simples C i)).hom = (q.iso (Ground.simples C i)).hom := by
  let X := Ground.simples C i
  let : Simple X := Ground.simples_simple C i
  let : FiniteDimensional ℂ (X ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  obtain ⟨c, hc0, hc, _⟩ := doubleDualIso_scalar (p.iso X) (q.iso X)
  have ht : q.rightTrace (𝟙 X) = c • p.rightTrace (𝟙 X) := by
    apply End.homEquiv.injective
    simp [PivotalStructure.rightTrace, hc, tensorHom_def]
  have hv : c * pivotalDimension C p X = pivotalDimension C p X := by
    have h := (hd i).symm
    unfold pivotalDimension at h ⊢
    rw [ht] at h
    simp only [← groundUnitScalarEquiv_apply, map_smul, smul_eq_mul] at h ⊢
    exact h
  have hn : pivotalDimension C p X ≠ 0 := pivotalDimension_simple_ne_zero C p i
  have hc1 : c = 1 := by
    apply (mul_right_cancel₀ hn)
    simpa using hv
  rw [hc, hc1, one_smul]

/-- A pivotal structure is determined by its dimensions on simple objects.
In particular there is at most one pivotal structure with prescribed positive
simple dimensions. -/
theorem pivotalStructure_unique_of_simple_dimensions (C : Ground.BraidedFusionCategory.{v,u})
    (p q : PivotalStructure (C := C.Obj))
    (hd : ∀ i, pivotalDimension C p (Ground.simples C i) =
      pivotalDimension C q (Ground.simples C i)) : p = q := by
  have hsimple := pivotal_components_eq_on_simples C p q hd
  have hall (X : C.Obj) : (p.iso X).hom = (q.iso X).hom := by
    classical
    obtain ⟨m, ⟨e⟩⟩ := Ground.simples_decompose C X
    let V : (Σ i, Fin (m i)) → C.Obj := fun a => Ground.simples C a.1
    have hs : (p.iso (⨁ V)).hom = (q.iso (⨁ V)).hom := by
      apply biproduct.hom_ext'
      intro a
      rw [p.naturality (biproduct.ι V a), q.naturality (biproduct.ι V a), hsimple a.1]
    let ee := rightDualIsoMap (rightDualIsoMap e)
    apply (cancel_mono ee.hom).1
    change (p.iso X).hom ≫ (e.homᘁ)ᘁ = (q.iso X).hom ≫ (e.homᘁ)ᘁ
    rw [← p.naturality e.hom, ← q.naturality e.hom, hs]
  have heq : p.iso = q.iso := by
    funext X
    exact Iso.ext (hall X)
  cases p with
  | mk pi pn pt pu =>
    cases q with
    | mk qi qn qt qu =>
      dsimp only at heq
      cases heq
      rfl

/-- Every positive pivotal dimension character is the Frobenius–Perron
character. This does not require pseudo-unitarity or sphericality. -/
theorem positive_pivotalDimension_eq_fpSimple (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) : ∀ i, d i = Ground.fpSimple C i := by
  have hunit : d (Ground.unitIndex C) = 1 := by
    apply Complex.ofReal_injective
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [← hreal, pivotalDimension_iso C p e, pivotalDimension_unit]
    norm_num
  have hchar : ∀ i j, d i * d j = ∑ k, (Ground.fusionCoeff C i j k : ℝ) * d k := by
    intro i j
    have h := pivotalDimension_character C p i j
    simp only [hreal] at h
    exact_mod_cast h
  have h := Ground.positive_character_unique C d (Ground.fpCharacter C) hpos
    (Ground.fpCharacter_pos C) hunit (Ground.fpCharacter_unit C) hchar (Ground.fpCharacter_mul C)
  intro i
  rw [Ground.fpSimple_eq_fpCharacter, ← h]

/-- There is at most one pivotal structure whose simple dimensions are
positive real numbers, and its dimensions are the FP dimensions. -/
theorem positive_pivotalStructure_unique (C : Ground.BraidedFusionCategory.{v,u})
    (p q : PivotalStructure (C := C.Obj)) (d e : Fin (Ground.rank C) → ℝ)
    (hd : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (he : ∀ i, pivotalDimension C q (Ground.simples C i) = (e i : ℂ))
    (hdpos : ∀ i, 0 < d i) (hepos : ∀ i, 0 < e i) : p = q := by
  apply pivotalStructure_unique_of_simple_dimensions C p q
  intro i
  rw [hd, he, positive_pivotalDimension_eq_fpSimple C p d hd hdpos i,
    positive_pivotalDimension_eq_fpSimple C q e he hepos i]

end PropertyF.Ground.Dimensions
