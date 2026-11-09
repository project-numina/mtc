module
public import MTC.PropertyF.Pivotal.AdjointObjects
public import MTC.PropertyF.Pivotal.Galois

/-! # Fusion-label support on actual objects -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
open MTC.Fusion MTC.Center.Braid MTC.Center.Normalization
namespace MTC.PropertyF.Pivotal
universe v u
set_option linter.style.haveILetI false
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts IsFusionCategory.hom_finite

/-- All simple constituents of an actual object belong to a given set. -/
def SupportedOn (A : Finset (Fin (rank C))) (X : C.Obj) : Prop :=
  ∀ i, 0 < simpleMultiplicity C i X → i ∈ A

theorem supportedOn_iso {A : Finset (Fin (rank C))} {X Y : C.Obj}
    (e : X ≅ Y) (h : SupportedOn C A Y) : SupportedOn C A X := by
  intro i hi
  apply h i
  simpa only [simpleMultiplicity] using
    ((CategoryTheory.Linear.homCongr ℂ (Iso.refl (simples C i)) e).finrank_eq ▸ hi)

theorem supportedOn_unit {A : Finset (Fin (rank C))} (hA : IsFusionSubring C A) :
    SupportedOn C A (𝟙_ C.Obj) := by
  intro i hi
  have hm : simpleMultiplicity C i (𝟙_ C.Obj) = if i = unitIndex C then 1 else 0 := by
    simpa [simpleMultiplicity] using
      ((CategoryTheory.Linear.homCongr ℂ (Iso.refl (simples C i)) (unitIndex_iso C).some.symm).finrank_eq.trans
        (finrank_simples_hom C i (unitIndex C)))
  rw [hm] at hi
  split_ifs at hi with he
  · simpa [he] using hA.unit
  · simp at hi

theorem supportedOn_tensor {A : Finset (Fin (rank C))} (hA : IsFusionSubring C A)
    {X Y : C.Obj} (hX : SupportedOn C A X) (hY : SupportedOn C A Y) :
    SupportedOn C A (X ⊗ Y) := by
  intro k hk
  rw [tensor_multiplicity_expanded] at hk
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hk
  obtain ⟨j, _, hj⟩ := Finset.sum_pos_iff.mp hi
  have hm := Nat.pos_of_mul_pos_right hj
  exact hA.fusion i (hX i (Nat.pos_of_mul_pos_right hm))
    j (hY j (Nat.pos_of_mul_pos_left hm)) k (Nat.pos_of_mul_pos_left hj)

theorem supportedOn_dual {A : Finset (Fin (rank C))} (hA : IsFusionSubring C A)
    {X : C.Obj} (hX : SupportedOn C A X) : SupportedOn C A (ᘁX) := by
  intro i hi
  rw [dual_multiplicity] at hi
  have h := hA.dual (dualIndex C i) (hX _ hi)
  rw [dualIndex_involutive C i] at h
  exact h

/-- Support passes to actual categorical retracts. -/
theorem supportedOn_retract {A : Finset (Fin (rank C))} {X Y : C.Obj}
    (r : Retract X Y) (hY : SupportedOn C A Y) : SupportedOn C A X := by
  intro i hi
  apply hY i
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hi
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨f ≫ r.i, ?_⟩
  intro hz
  apply hf
  have h := congrArg (fun g ↦ g ≫ r.r) hz
  simpa only [Category.assoc, r.retract, Category.comp_id, zero_comp] using h

/-- Support is closed under finite biproducts. -/
theorem supportedOn_sum {A : Finset (Fin (rank C))} {n : ℕ}
    (V : Fin n → C.Obj) (hV : ∀ j, SupportedOn C A (V j)) :
    SupportedOn C A (⨁ V) := by
  intro i hi
  change 0 < Module.finrank ℂ (simples C i ⟶ ⨁ V) at hi
  rw [finrank_hom_biproduct] at hi
  obtain ⟨j, _, hj⟩ := Finset.sum_pos_iff.mp hi
  exact hV j i hj

/-- The left dual transports an isomorphism in the opposite direction. -/
def leftDualIsoOfIso {X Y : C.Obj} (e : X ≅ Y) : (ᘁX) ≅ (ᘁY) where
  hom := ᘁ(e.inv)
  inv := ᘁ(e.hom)
  hom_inv_id := by rw [← comp_leftAdjointMate, Iso.hom_inv_id, leftAdjointMate_id]
  inv_hom_id := by rw [← comp_leftAdjointMate, Iso.inv_hom_id, leftAdjointMate_id]

/-- Every actual simple adjoint generator is supported on any fusion
subring containing the adjoint seeds. -/
theorem supportedOn_seed {A : Finset (Fin (rank C))}
    (hseed : ∀ i, AdjointSeed C i → i ∈ A) (S : C.Obj) [Simple S] :
    SupportedOn C A (S ⊗ (ᘁS)) := by
  obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso C S
  let E : S ⊗ (ᘁS) ≅ simples C i ⊗ simples C (dualIndex C i) :=
    e ⊗ᵢ (leftDualIsoOfIso C e ≪≫ (dualIndex_iso i).some)
  intro k hk
  apply hseed k
  refine ⟨i, ?_⟩
  change 0 < Module.finrank ℂ (simples C k ⟶ S ⊗ (ᘁS)) at hk
  change 0 < Module.finrank ℂ (simples C k ⟶ simples C i ⊗ simples C (dualIndex C i))
  rw [← (CategoryTheory.Linear.homCongr ℂ (Iso.refl (simples C k)) E).finrank_eq]
  exact hk

/-- An object in the actual adjoint closure is supported on every fusion
subring containing the adjoint seeds. -/
theorem supportedOn_of_adjointGenerated {A : Finset (Fin (rank C))}
    (hA : IsFusionSubring C A) (hseed : ∀ i, AdjointSeed C i → i ∈ A)
    {X : C.Obj} (hX : AdjointGenerated C X) : SupportedOn C A X := by
  induction hX with
  | unit => exact supportedOn_unit C hA
  | seed S => exact supportedOn_seed C hseed S
  | tensor _ _ ihX ihY => exact supportedOn_tensor C hA ihX ihY
  | dual _ ih => exact supportedOn_dual C hA ih
  | sum V _ ih => exact supportedOn_sum C V ih
  | retract _ r ih => exact supportedOn_retract C r ih

/-- Actual simple objects in the categorical adjoint closure have exactly the
fusion-generated adjoint labels. -/
theorem adjointGenerated_simple_iff (i : Fin (rank C)) :
    AdjointGenerated C (simples C i) ↔ IsAdjointLabel C i := by
  constructor
  · intro h A hA hseed
    have hs := supportedOn_of_adjointGenerated C hA hseed h
    apply hs i
    simp [simpleMultiplicity, finrank_simples_hom]
  · exact adjointLabel_generated C

/-- The label-level positivity condition is equivalent to positivity on
actual transparent simple objects in the categorical adjoint closure. -/
theorem positiveOnTransparentAdjoint_iff_categorical
    (p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := C.Obj)) :
    PositiveOnTransparentAdjoint C p ↔
      ∀ (X : C.Obj) [Simple X], MTC.Center.Transparent X →
        AdjointGenerated C X → ∃ r : ℝ, 0 < r ∧
          MTC.CategoryTheory.Dimensions.pivotalDimension C p X = (r : ℂ) := by
  constructor
  · intro hp X _ ht hg
    obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso C X
    have ht' : MTC.Center.Transparent (simples C i) := transparent_of_iso C e.symm ht
    have hg' : AdjointGenerated C (simples C i) := .retract hg (Retract.ofIso e.symm)
    obtain ⟨r, hr, hd⟩ := hp i ht' ((adjointGenerated_simple_iff C i).1 hg')
    exact ⟨r, hr, (MTC.CategoryTheory.Dimensions.pivotalDimension_iso p e).trans hd⟩
  · exact positiveOnTransparentAdjoint_of_categorical C p

end MTC.PropertyF.Pivotal
end
