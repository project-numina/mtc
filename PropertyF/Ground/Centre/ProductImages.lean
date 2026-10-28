module
public import PropertyF.Definitions
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import PropertyF.Ground.Centre.Product
public import PropertyF.Ground.Modular.BraidFunctor
public import PropertyF.Ground.Cabling.Naturality

/-! Reversing the braiding inverts each actual adjacent braid generator. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Reversing the braiding inverts the first adjacent generator. -/
theorem reverse_braidGenerator_zero (X : C) (n : ℕ) :
    @braidGenerator C _ _ (CategoryTheory.reverseBraiding C) X n 0 =
      (braidGenerator X n 0)⁻¹ := by
  cases n <;> apply CategoryTheory.Aut.ext <;> apply Iso.ext <;>
    change ((α_ X X (tensorPower X _)).symm ≪≫
      ((β_ X X).symm ⊗ᵢ Iso.refl (tensorPower X _)) ≪≫ α_ X X (tensorPower X _)).hom =
      ((α_ X X (tensorPower X _)).symm ≪≫
        ((β_ X X) ⊗ᵢ Iso.refl (tensorPower X _)) ≪≫ α_ X X (tensorPower X _)).inv
  all_goals simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, Category.assoc]

/-- A reversed braid generator is inverted when the index is shifted. -/
theorem reverse_braidGenerator_succ (X : C) (n : ℕ) (i : Fin (n + 1))
    (h : @braidGenerator C _ _ (CategoryTheory.reverseBraiding C) X n i =
      (braidGenerator X n i)⁻¹) :
    @braidGenerator C _ _ (CategoryTheory.reverseBraiding C) X (n + 1) i.succ =
      (braidGenerator X (n + 1) i.succ)⁻¹ := by
  obtain ⟨i, hi⟩ := i
  change @braidGenerator C _ _ (CategoryTheory.reverseBraiding C) X (n + 1)
      ⟨i + 1, Nat.succ_lt_succ hi⟩ =
    (braidGenerator X (n + 1) ⟨i + 1, Nat.succ_lt_succ hi⟩)⁻¹
  apply CategoryTheory.Aut.ext
  apply Iso.ext
  simp only [braidGenerator, h]
  simp only [Aut.inv_asIso, Iso.symm_hom, tensorIso_hom, Iso.refl_hom]
  change 𝟙 X ⊗ₘ (braidGenerator X n ⟨i, hi⟩).asIso.inv =
    (Iso.refl X ⊗ᵢ (braidGenerator X n ⟨i, hi⟩).asIso).inv
  rw [tensorIso_inv, Iso.refl_inv]

theorem reverse_braidGenerator (X : C) : ∀ (n : ℕ) (i : Fin (n + 1)),
    @braidGenerator C _ _ (CategoryTheory.reverseBraiding C) X n i =
      (braidGenerator X n i)⁻¹ := by
  intro n
  induction n with
  | zero =>
    intro i
    fin_cases i
    exact reverse_braidGenerator_zero X 0
  | succ n ih =>
    intro i
    exact Fin.cases (reverse_braidGenerator_zero X (n + 1))
      (fun j ↦ reverse_braidGenerator_succ X n j (ih j)) i

end PropertyF.Ground.Centre

/-! Braid images in the ordinary product with mixed braiding. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [bc : BraidedCategory C]
/-- The product category uses the ordinary braiding on the first factor and its reverse on the second. -/
local instance mixedBraidingCategory : BraidedCategory (C × C) := mixedBraiding

instance fstMonoidal : (CategoryTheory.Prod.fst C C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso := fun _ _ => Iso.refl _ }

instance sndMonoidal : (CategoryTheory.Prod.snd C C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso := fun _ _ => Iso.refl _ }

/-- The first projection preserves the mixed braiding. -/
instance fstBraided : (CategoryTheory.Prod.fst C C).Braided where
  braided X Y := by
    change 𝟙 _ ≫ (β_ X.1 Y.1).hom = (β_ X.1 Y.1).hom ≫ 𝟙 _
    simp

/-- The second projection preserves the reversed braiding. -/
@[instance_reducible]
def sndBraided : @Functor.Braided (C × C) _ _ (mixedBraiding (C := C))
    C _ _ (CategoryTheory.reverseBraiding C) (CategoryTheory.Prod.snd C C) := by
  let mix := mixedBraiding (C := C)
  letI : BraidedCategory C := CategoryTheory.reverseBraiding C
  letI : BraidedCategory (C × C) := mix
  refine { braided := ?_ }
  intro X Y
  change 𝟙 _ ≫ (@BraidedCategory.braiding C _ _ bc Y.2 X.2).inv =
    (@BraidedCategory.braiding C _ _ bc Y.2 X.2).inv ≫ 𝟙 _
  simp

/-- First projection of the braid automorphism after tensor-power comparison. -/
def fstBraidMap (X Y : C) (n : ℕ) :
    Aut (tensorPower (X,Y) (n+2)) →* Aut (tensorPower X (n+2)) :=
  Modular.braidAutMap (CategoryTheory.Prod.fst C C) (X,Y) n

/-- Second projection, using the reversed braiding. -/
def sndBraidMap (X Y : C) (n : ℕ) :
    Aut (tensorPower (X,Y) (n+2)) →* Aut (tensorPower Y (n+2)) :=
  @Modular.braidAutMap (C × C) _ _ (mixedBraiding (C := C)) C _ _
    (CategoryTheory.reverseBraiding C) (CategoryTheory.Prod.snd C C) sndBraided (X,Y) n

theorem fstBraidMap_generator (X Y : C) (n : ℕ) (i : Fin (n+1)) :
    fstBraidMap X Y n (braidGenerator (X,Y) n i) = braidGenerator X n i :=
  Modular.braidAutMap_generator (CategoryTheory.Prod.fst C C) (X,Y) n i

theorem sndBraidMap_generator (X Y : C) (n : ℕ) (i : Fin (n+1)) :
    sndBraidMap X Y n (braidGenerator (X,Y) n i) = (braidGenerator Y n i)⁻¹ := by
  rw [← reverse_braidGenerator]
  exact @Modular.braidAutMap_generator (C × C) _ _ (mixedBraiding (C := C)) C _ _
    (CategoryTheory.reverseBraiding C) (CategoryTheory.Prod.snd C C) sndBraided (X,Y) n i

/-- The two projected automorphisms jointly detect an automorphism of a tensor power. -/
theorem projections_jointly_injective (X Y : C) (n : ℕ) :
    Function.Injective (fun a : Aut (tensorPower (X,Y) (n+2)) =>
      (fstBraidMap X Y n a, sndBraidMap X Y n a)) := by
  intro a b h
  let p := Modular.tensorPowerComparison (CategoryTheory.Prod.fst C C) (X,Y) (n+2)
  let q := @Modular.tensorPowerComparison (C × C) _ _ (mixedBraiding (C := C)) C _ _
    (CategoryTheory.reverseBraiding C) (CategoryTheory.Prod.snd C C) sndBraided (X,Y) (n+2)
  apply Aut.ext
  apply Iso.ext
  apply Prod.ext
  · exact congrArg (fun z => z.asIso.hom) (p.symm.conjAut.injective (congrArg Prod.fst h))
  · exact congrArg (fun z => z.asIso.hom) (q.symm.conjAut.injective (congrArg Prod.snd h))

/-- The projected first component of a product braid lies in the first image. -/
theorem fstBraidMap_mem (X Y : C) (n : ℕ) :
    braidImage (X,Y) n ≤ (braidImage X n).comap (fstBraidMap X Y n) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change fstBraidMap X Y n (braidGenerator (X,Y) n i) ∈ braidImage X n
  rw [fstBraidMap_generator]
  exact Subgroup.subset_closure ⟨i, rfl⟩

/-- The projected second component lies in the original, unreversed image. -/
theorem sndBraidMap_mem (X Y : C) (n : ℕ) :
    braidImage (X,Y) n ≤ (braidImage Y n).comap (sndBraidMap X Y n) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change sndBraidMap X Y n (braidGenerator (X,Y) n i) ∈ braidImage Y n
  rw [sndBraidMap_generator]
  exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, rfl⟩)

/-- The actual product braid image maps into the product of the two factor images. -/
def productBraidMap (X Y : C) (n : ℕ) :
    braidImage (X,Y) n →* (braidImage X n × braidImage Y n) where
  toFun a := (⟨fstBraidMap X Y n a, fstBraidMap_mem X Y n a.property⟩,
    ⟨sndBraidMap X Y n a, sndBraidMap_mem X Y n a.property⟩)
  map_one' := by ext <;> simp
  map_mul' := by intro a b; ext <;> simp

/-- The product braid image is a subgroup of the product of its two factor images. -/
theorem productBraidMap_injective (X Y : C) (n : ℕ) :
    Function.Injective (productBraidMap X Y n) := by
  intro a b hab
  apply Subtype.ext
  apply projections_jointly_injective X Y n
  exact Prod.ext (congrArg (fun x : braidImage X n × braidImage Y n => x.1.val) hab)
    (congrArg (fun x : braidImage X n × braidImage Y n => x.2.val) hab)

/-- Finite factor images imply a finite mixed-product braid image. -/
theorem product_braidImage_finite (X Y : C) (n : ℕ)
    [Finite (braidImage X n)] [Finite (braidImage Y n)] :
    Finite (braidImage (X,Y) n) :=
  Finite.of_injective (productBraidMap X Y n) (productBraidMap_injective X Y n)

/-- Tensoring the positive and negative images preserves finite braid images. -/
theorem productFunctor_objectPropertyF (X Y : C)
    (hX : ObjectPropertyF X) (hY : ObjectPropertyF Y) :
    ObjectPropertyF (productFunctor.obj (X,Y)) := by
  let _ : (productFunctor (C := C)).Braided := productBraided
  apply Modular.objectPropertyF_functor (productFunctor (C := C)) (X,Y)
  intro n
  let _ := hX n
  let _ := hY n
  exact product_braidImage_finite X Y n

/-- Property F transfers to every retract of a product-functor image. -/
theorem productFunctor_retract_objectPropertyF (X Y : C) (Z : CategoryTheory.Center C)
    (r : CategoryTheory.Retract Z (productFunctor.obj (X,Y)))
    (hX : ObjectPropertyF X) (hY : ObjectPropertyF Y) : ObjectPropertyF Z :=
  objectPropertyF_of_retract r (productFunctor_objectPropertyF X Y hX hY)

end PropertyF.Ground.Centre
