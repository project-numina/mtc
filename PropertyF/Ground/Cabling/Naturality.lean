module
public import PropertyF.Definitions
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.CategoryTheory.Conj
public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Braid words and naturality

The categorical action of braid words is natural in the underlying object.
-/

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

variable (X : C) (n : ℕ)

/-- Evaluate a word in the actual categorical braid generators. -/
def braidWordAction : BraidWords n →* braidImage X n :=
  (FreeGroup.lift (braidGenerator X n)).codRestrict (braidImage X n) (by
    intro w
    change (FreeGroup.lift (braidGenerator X n)) w ∈ Subgroup.closure (Set.range (braidGenerator X n))
    rw [← FreeGroup.range_lift_eq_closure]
    exact ⟨w, rfl⟩)

/-- Every element of the categorical braid image is represented by a word. -/
theorem braidWordAction_surjective :
    Function.Surjective (braidWordAction X n) :=
  (Set.surjective_codRestrict _).2 (by
    simp only [← MonoidHom.coe_range, FreeGroup.range_lift_eq_closure, braidImage])

end PropertyF

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The morphism obtained by tensoring n copies of a morphism. -/
def tensorPowerMap {X Y : C} (f : X ⟶ Y) : ∀ n, tensorPower X n ⟶ tensorPower Y n
  | 0 => 𝟙 _
  | n + 1 => f ⊗ₘ tensorPowerMap f n

/-- Tensor powers preserve identity morphisms. -/
@[simp] theorem tensorPowerMap_id (X : C) : ∀ n, tensorPowerMap (𝟙 X) n = 𝟙 _
  | 0 => rfl
  | n + 1 => by simp [tensorPowerMap, tensorPowerMap_id X n, tensorPower]

/-- Tensor powers preserve composition of morphisms. -/
@[simp] theorem tensorPowerMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ n, tensorPowerMap (f ≫ g) n = tensorPowerMap f n ≫ tensorPowerMap g n
  | 0 => by simp [tensorPowerMap, tensorPower]
  | n + 1 => (congrArg (fun h => (f ≫ g) ⊗ₘ h) (tensorPowerMap_comp f g n)).trans
      (tensorHom_comp_tensorHom f (tensorPowerMap f n) g (tensorPowerMap g n)).symm


/-- Tensor powers carry a retract to a retract. -/
private abbrev tensorPowerMap_retract {X Y : C} (r : Retract X Y) (n : ℕ) :
    Retract (tensorPower X n) (tensorPower Y n) where
  i := tensorPowerMap r.i n
  r := tensorPowerMap r.r n
  retract := by rw [← tensorPowerMap_comp, r.retract, tensorPowerMap_id]

omit [MonoidalCategory C] in
/-- A morphism intertwining generators also intertwines every free-group word. -/
private theorem freeGroup_natural {X Y : C} {ι : Type*} (a : ι → Aut X) (b : ι → Aut Y)
    (f : X ⟶ Y) (h : ∀ i, (a i).asIso.hom ≫ f = f ≫ (b i).asIso.hom)
    (w : FreeGroup ι) :
    (FreeGroup.lift a w).asIso.hom ≫ f = f ≫ (FreeGroup.lift b w).asIso.hom := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i => simpa using h i
  | inv_of i ih =>
    simp only [map_inv, Aut.inv_asIso] at *
    apply (cancel_epi (FreeGroup.lift a (FreeGroup.of i)).asIso.hom).mp
    apply (cancel_mono (FreeGroup.lift b (FreeGroup.of i)).asIso.hom).mp
    simpa [Category.assoc] using ih.symm
  | mul x y ihx ihy =>
    simp only [map_mul, Aut.mul_asIso, Iso.trans_hom, Category.assoc]
    rw [ihx, ← Category.assoc, ihy, Category.assoc]

variable [BraidedCategory C]

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

section BraidNaturality

variable {X Y : C} (f : X ⟶ Y) (n : ℕ)

/-- Each adjacent braid generator is natural in arbitrary morphisms. -/
theorem braidGenerator_map_natural (i : Fin (n + 1)) :
    (braidGenerator X n i).asIso.hom ≫ tensorPowerMap f (n + 2) =
      tensorPowerMap f (n + 2) ≫ (braidGenerator Y n i).asIso.hom := by
  induction n with
  | zero => exact (Fin.eq_zero i).symm ▸ braid_first_map f (tensorPowerMap f 0)
  | succ n ih =>
    refine Fin.cases (braid_first_map f (tensorPowerMap f (n + 1))) (fun j => ?_) i
    change (𝟙 X ⊗ₘ (braidGenerator X n j).asIso.hom) ≫
        (f ⊗ₘ tensorPowerMap f (n + 2)) =
      (f ⊗ₘ tensorPowerMap f (n + 2)) ≫
        (𝟙 Y ⊗ₘ (braidGenerator Y n j).asIso.hom)
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, ih]

/-- Braiding words are natural in any morphism, not only in isomorphisms. -/
theorem braidWord_map_natural (w : BraidWords n) :
    ((braidWordAction X n w).val).asIso.hom ≫ tensorPowerMap f (n + 2) =
      tensorPowerMap f (n + 2) ≫ ((braidWordAction Y n w).val).asIso.hom :=
  freeGroup_natural (braidGenerator X n) (braidGenerator Y n) (tensorPowerMap f (n + 2))
    (braidGenerator_map_natural f n) w

end BraidNaturality

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
  let : IsSplitMono (tensorPowerMap r.i (n + 2)) := (tensorPowerMap_retract r (n + 2)).instIsSplitMonoI
  exact (cancel_mono (tensorPowerMap r.i (n + 2))).mp (by simpa using nat)

/-- Restriction to a retract induces a surjective homomorphism of braid images. -/
def braidImageRetractMap {X Y : C} (r : Retract X Y) (n : ℕ) :
    braidImage Y n →* braidImage X n :=
  (braidWordAction Y n).liftOfSurjective (braidWordAction_surjective Y n)
    ⟨braidWordAction X n, braidWordAction_ker_le_of_retract r n⟩

/-- Property F passes from an object to any retract. -/
theorem objectPropertyF_of_retract {X Y : C} (r : Retract X Y)
    (hY : ObjectPropertyF Y) : ObjectPropertyF X := fun n ↦
  letI := hY n
  Finite.of_surjective (braidImageRetractMap r n) <| Function.Surjective.of_comp
    (g := braidWordAction Y n) (by
      simpa [braidImageRetractMap, Function.comp_def] using braidWordAction_surjective X n)

end PropertyF
