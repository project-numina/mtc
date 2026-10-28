module
public import PropertyF.Main
public import PropertyF.Ground.Final
public import PropertyF.Ground.Fusion.ObjectDimension
public import PropertyF.Ground.Integrate.ConjugateBound
public import PropertyF.Ground.Integrate.Arithmetic
public import PropertyF.Ground.Integrate.StrandInclusion

@[expose] public noncomputable section
namespace PropertyF
universe v u

/-- Zero- and one-strand images are finite as well. -/
theorem braidImageAll_finite {C : BraidedFusionCategory.{v,u}} {X : C.Obj}
    (hX : ObjectPropertyF X) : ∀ n, Finite (braidImageAll X n)
  | 0 => inferInstanceAs (Finite ↥(⊥ : Subgroup (CategoryTheory.Aut (tensorPower X 0))))
  | 1 => inferInstanceAs (Finite ↥(⊥ : Subgroup (CategoryTheory.Aut (tensorPower X 1))))
  | n + 2 => hX n

/-- The finite-product and finite-index argument in Lemma 4.2. In particular,
no finiteness conclusion is assumed by `CablingWitness`. -/
theorem CablingWitness.finite_image {C : BraidedFusionCategory.{v,u}}
    {X Y : C.Obj} {n : ℕ} (W : CablingWitness C X Y n) (hX : ObjectPropertyF X) :
    Finite (braidImage Y n) := by
  have : ∀ r : Fin W.blockCount, Finite (braidImageAll X (∑ i, W.lengths r i)) :=
    fun r => braidImageAll_finite hX _
  have hpure : Finite W.pureImage := Finite.of_surjective W.restriction W.restriction_surjective
  exact (Subgroup.finite_iff_finite_and_finiteIndex W.pureImage).mpr ⟨hpure, inferInstance⟩

/-- Lemma 4.2 (closure), relative to the standard cabling diagram for actual
categorical braid images. Nonnegative powers cover the zero object too. -/
theorem propertyF_closure {C : BraidedFusionCategory.{v,u}} {X : C.Obj}
    (I : GeneratedInputs C X) (hX : ObjectPropertyF X) :
    ∀ Y, GeneratedBy X Y → ObjectPropertyF Y := by
  intro Y hY n
  obtain ⟨W⟩ := I.cabling Y hY n
  exact W.finite_image hX

/-- Property F on the bundled generated fusion category. -/
theorem generated_category_propertyF {C : BraidedFusionCategory.{v,u}} {X : C.Obj}
    (I : GeneratedInputs C X) (hX : ObjectPropertyF X) : HasPropertyF I.category.Obj := by
  intro Y n
  have := propertyF_closure I hX (I.inclusion.obj Y) (I.inclusion_generated Y) n
  obtain ⟨e⟩ := I.image_equivalence Y n
  exact Finite.of_equiv (braidImage (I.inclusion.obj Y) n) e.toEquiv.symm

/-- Corollary 4.3. The index `n` denotes `n+2` strands, as in `braidImage`.
Thus this is infinitude for every sufficiently large number of strands. -/
theorem eventually_infinite_braidImage (H : StandardInputs.{v,u})
    {C : BraidedFusionCategory.{v,u}} {X : C.Obj} (I : GeneratedInputs C X)
    (hX : CategoryTheory.Simple X) (hPU : HasPseudoUnitaryGaloisConjugate I.category)
    (hnonintegral : ¬ ∃ z : ℤ, C.fusion.fpDimension X ^ 2 = z) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Infinite (braidImage X n) := by
  have hnotall : ¬ ObjectPropertyF X := by
    intro hAll
    have hweak := propertyF_implies_weaklyIntegral H I.category hPU
      (generated_category_propertyF I hAll)
    exact hnonintegral (I.simple_square_integral hX hweak)
  obtain ⟨N, hN⟩ : ∃ N, ¬ Finite (braidImage X N) := by
    simpa only [ObjectPropertyF, not_forall] using hnotall
  refine ⟨N, ?_⟩
  intro n hn
  apply not_finite_iff_infinite.mp
  intro hfinite
  obtain ⟨e⟩ := I.strand_inclusion hX N n hn
  exact hN (Finite.of_injective e e.injective)

end PropertyF
