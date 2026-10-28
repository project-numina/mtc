module
public import PropertyF.Definitions
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.CategoryTheory.Conj
public import Mathlib.Algebra.Group.Subgroup.Map

/-! The permutation of a braid word and its finite-index pure image.
The free group represents words in adjacent crossings. Its permutation kernel
is the inverse image of the usual pure braid group; this construction does not
require imposing the braid relations to establish finite index. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Words in the adjacent generators on `n+2` strands. -/
abbrev BraidWords (n : ℕ) := FreeGroup (Fin (n + 1))

/-- The permutation induced by a word of crossings. -/
def strandPermutation (n : ℕ) : BraidWords n →* Equiv.Perm (Fin (n + 2)) :=
  FreeGroup.lift (fun i => Equiv.swap i.castSucc i.succ)

/-- Words whose permutation of strands is the identity. -/
def pureWords (n : ℕ) : Subgroup (BraidWords n) := (strandPermutation n).ker

instance pureWords_finiteIndex (n : ℕ) : (pureWords n).FiniteIndex := by
  unfold pureWords
  infer_instance

/-- Evaluate a word in the actual categorical braid generators. -/
def braidWordAction (X : C) (n : ℕ) : BraidWords n →* braidImage X n :=
  (FreeGroup.lift (braidGenerator X n)).codRestrict (braidImage X n) (by
    intro w
    change (FreeGroup.lift (braidGenerator X n)) w ∈ Subgroup.closure (Set.range (braidGenerator X n))
    rw [← FreeGroup.range_lift_eq_closure]
    exact ⟨w, rfl⟩)

/-- Every element of the categorical braid image is represented by a word. -/
theorem braidWordAction_surjective (X : C) (n : ℕ) :
    Function.Surjective (braidWordAction X n) := by
  intro a
  have ha : a.val ∈ (FreeGroup.lift (braidGenerator X n)).range := by
    rw [FreeGroup.range_lift_eq_closure]
    exact a.property
  obtain ⟨w, hw⟩ := ha
  exact ⟨w, Subtype.ext hw⟩

/-- The image of pure words in the categorical braid image. -/
def pureBraidImage (X : C) (n : ℕ) : Subgroup (braidImage X n) :=
  (pureWords n).map (braidWordAction X n)

/-- The pure image has finite index even if the categorical representation
has a kernel: it is the image of a finite-index subgroup under a surjection. -/
instance pureBraidImage_finiteIndex (X : C) (n : ℕ) :
    (pureBraidImage X n).FiniteIndex := by
  unfold pureBraidImage
  exact Subgroup.FiniteIndex.map_of_surjective (pureWords n) (braidWordAction_surjective X n)

end PropertyF

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The morphism obtained by tensoring n copies of a morphism. -/
def tensorPowerMap {X Y : C} (f : X ⟶ Y) : ∀ n, tensorPower X n ⟶ tensorPower Y n
  | 0 => 𝟙 _
  | n + 1 => f ⊗ₘ tensorPowerMap f n

omit [BraidedCategory C] in
@[simp] theorem tensorPowerMap_id (X : C) : ∀ n, tensorPowerMap (𝟙 X) n = 𝟙 _
  | 0 => rfl
  | n + 1 => by simp [tensorPowerMap, tensorPowerMap_id X n, tensorPower]

omit [BraidedCategory C] in
@[simp] theorem tensorPowerMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ n, tensorPowerMap (f ≫ g) n = tensorPowerMap f n ≫ tensorPowerMap g n
  | 0 => by simp [tensorPowerMap, tensorPower]
  | n + 1 => by
      simp only [tensorPowerMap, tensorPowerMap_comp f g n]
      change (f ≫ g) ⊗ₘ (tensorPowerMap f n ≫ tensorPowerMap g n) =
        (f ⊗ₘ tensorPowerMap f n) ≫ (g ⊗ₘ tensorPowerMap g n)
      exact (tensorHom_comp_tensorHom _ _ _ _).symm


/-- Naturality of the first adjacent braiding. -/
lemma braid_first_map {X Y A B : C} (f : X ⟶ Y) (g : A ⟶ B) :
    ((α_ X X A).symm ≪≫ ((β_ X X) ⊗ᵢ Iso.refl A) ≪≫ α_ X X A).hom ≫
        (f ⊗ₘ (f ⊗ₘ g)) =
      (f ⊗ₘ (f ⊗ₘ g)) ≫
        ((α_ Y Y B).symm ≪≫ ((β_ Y Y) ⊗ᵢ Iso.refl B) ≪≫ α_ Y Y B).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
  rw [← associator_naturality, associator_inv_naturality_assoc]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    braiding_naturality]

/-- Each adjacent braid generator is natural in arbitrary morphisms. -/
theorem braidGenerator_map_natural {X Y : C} (f : X ⟶ Y) (n : ℕ)
    (i : Fin (n + 1)) :
    (braidGenerator X n i).asIso.hom ≫ tensorPowerMap f (n + 2) =
      tensorPowerMap f (n + 2) ≫ (braidGenerator Y n i).asIso.hom := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact braid_first_map f (tensorPowerMap f 0)
  | succ n ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => exact braid_first_map f (tensorPowerMap f (n + 1))
    | succ i =>
      change (𝟙 X ⊗ₘ (braidGenerator X n ⟨i, Nat.lt_of_succ_lt_succ hi⟩).asIso.hom) ≫
          (f ⊗ₘ tensorPowerMap f (n + 2)) =
        (f ⊗ₘ tensorPowerMap f (n + 2)) ≫
          (𝟙 Y ⊗ₘ (braidGenerator Y n ⟨i, Nat.lt_of_succ_lt_succ hi⟩).asIso.hom)
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, ih]

/-- Braiding words are natural in any morphism, not only in isomorphisms. -/
theorem braidWord_map_natural {X Y : C} (f : X ⟶ Y) (n : ℕ) (w : BraidWords n) :
    ((braidWordAction X n w).val).asIso.hom ≫ tensorPowerMap f (n + 2) =
      tensorPowerMap f (n + 2) ≫ ((braidWordAction Y n w).val).asIso.hom := by
  induction w using FreeGroup.induction_on with
  | one => simp [braidWordAction]
  | of i => simpa [braidWordAction] using braidGenerator_map_natural f n i
  | inv_of i ih =>
    simp only [map_inv, Subgroup.coe_inv, Aut.inv_asIso] at *
    apply (cancel_epi ((braidWordAction X n (FreeGroup.of i)).val).asIso.hom).mp
    apply (cancel_mono ((braidWordAction Y n (FreeGroup.of i)).val).asIso.hom).mp
    simpa [Category.assoc] using ih.symm
  | mul x y ihx ihy =>
    simp only [map_mul, Subgroup.coe_mul, Aut.mul_asIso, Iso.trans_hom, Category.assoc]
    rw [ihx, ← Category.assoc, ihy, Category.assoc]
/-- Any braid word acting trivially on an object also acts trivially on its
retract, by naturality of the tensor-power inclusion. -/
theorem braidWordAction_ker_le_of_retract {X Y : C} (r : Retract X Y) (n : ℕ) :
    (braidWordAction Y n).ker ≤ (braidWordAction X n).ker := by
  intro w hw
  change braidWordAction Y n w = 1 at hw
  change braidWordAction X n w = 1
  apply Subtype.ext
  apply Aut.ext
  apply Iso.ext
  have nat := braidWord_map_natural r.i n w
  rw [hw] at nat
  have hi : Mono (tensorPowerMap r.i (n + 2)) := by
    let _ : IsSplitMono (tensorPowerMap r.i (n + 2)) := ⟨⟨{retraction := tensorPowerMap r.r (n + 2), id := by rw [← tensorPowerMap_comp, r.retract, tensorPowerMap_id]}⟩⟩
    infer_instance
  apply (cancel_mono (tensorPowerMap r.i (n + 2))).mp
  simpa using nat

/-- Restriction to a retract induces a surjective homomorphism of braid images. -/
def braidImageRetractMap {X Y : C} (r : Retract X Y) (n : ℕ) :
    braidImage Y n →* braidImage X n := by
  let f := braidWordAction Y n
  let g := braidWordAction X n
  let q := f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective
    ⟨g, by simpa using braidWordAction_ker_le_of_retract r n⟩
  have hs := braidWordAction_surjective Y n
  let embed : braidImage Y n →* f.range :=
    (MonoidHom.id _).codRestrict f.range (fun y => hs y)
  exact q.comp embed

/-- The restriction map hits every braid word on the retract. -/
theorem braidImageRetractMap_surjective {X Y : C} (r : Retract X Y) (n : ℕ) :
    Function.Surjective (braidImageRetractMap r n) := by
  intro a
  obtain ⟨w, rfl⟩ := braidWordAction_surjective X n a
  refine ⟨braidWordAction Y n w, ?_⟩
  change ((braidWordAction Y n).rangeRestrict.liftOfSurjective
    (braidWordAction Y n).rangeRestrict_surjective
    ⟨braidWordAction X n, by simpa using braidWordAction_ker_le_of_retract r n⟩)
      ((braidWordAction Y n).rangeRestrict w) = braidWordAction X n w
  simp
/-- Property F passes from an object to any retract. -/
theorem objectPropertyF_of_retract {X Y : C} (r : Retract X Y)
    (hY : ObjectPropertyF Y) : ObjectPropertyF X := by
  intro n
  let _ : Finite (braidImage Y n) := hY n
  exact Finite.of_surjective (braidImageRetractMap r n) (braidImageRetractMap_surjective r n)

end PropertyF
