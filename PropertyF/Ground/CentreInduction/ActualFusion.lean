module
public import PropertyF.Ground.CentreInduction.SecondTriangle
public import PropertyF.Ground.CentreInduction.Representatives
public import PropertyF.Ground.CentreBundle.Fusion
public import PropertyF.Ground.Fusion.SpectralIntegral
public import PropertyF.Ground.Integrate.CenterBundle
public import Mathlib.CategoryTheory.Adjunction.Additive

section
/-! Centrality of the induction unit and the centre-forgetful adjunction. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.ExactPairing
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})
local notation "𝒵" => Center C.Obj
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable {T S R : D}

set_option backward.isDefEq.respectTransparency false in
/-- Resolving a fusion strand commutes with coevaluation. -/
theorem fusion_coevaluation [HasRightDual R] [HasRightDual S] (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    𝟙 T ⊗≫ (η_ R (Rᘁ) ▷ T) ⊗≫ (g ⊗ₘ closeFusionMap T S f) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ) =
      𝟙 T ⊗≫ (T ◁ η_ S (Sᘁ)) ⊗≫ ((f ≫ g) ▷ (Sᘁ)) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ) := by
  have hr : (𝟙 T ⊗≫ (T ◁ η_ S (Sᘁ)) ⊗≫ ((f ≫ g) ▷ (Sᘁ)) ⊗≫
      𝟙 ((T ⊗ S) ⊗ Sᘁ)) = (tensorRightHomEquiv T S (Sᘁ) (T ⊗ S)) (f ≫ g) := by
    simp [tensorRightHomEquiv, monoidalComp]
  rw [hr]
  apply (tensorRightHomEquiv T S (Sᘁ) (T ⊗ S)).symm.injective
  rw [Equiv.symm_apply_apply]
  dsimp only [tensorRightHomEquiv, Equiv.symm, Equiv.coe_fn_mk]
  set q := closeFusionMap T S f
  calc
    _ = 𝟙 _ ⊗≫ (η_ R (Rᘁ) ▷ (T ⊗ S)) ⊗≫ (R ◁ (q ▷ S)) ⊗≫
      ((g ▷ ((Sᘁ : D) ⊗ S)) ≫ ((T ⊗ S) ◁ ε_ S (Sᘁ))) ⊗≫ 𝟙 _ := by
        rw [tensorHom_def']
        monoidal
    _ = 𝟙 _ ⊗≫ ((η_ R (Rᘁ) ▷ (T ⊗ S)) ≫ (((R ⊗ Rᘁ) : D) ◁ f)) ⊗≫
      (R ◁ ε_ R (Rᘁ)) ⊗≫ g := by
      rw [← whisker_exchange]
      simp [monoidalComp, Category.assoc, q]
      rw [← whiskerLeft_comp_assoc, closeFusionMap_evaluation]
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      simp [monoidalComp]

set_option backward.isDefEq.respectTransparency false in
/-- A unit component followed by a crossing block reduces to a fusion endomorphism. -/
theorem unit_block [HasRightDual R] [HasRightDual S] (Z : Center D) (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    (unitComponentAt Z R ▷ T) ≫ crossingBlock Z.1 T S g f =
      𝟙 _ ⊗≫ (Z.1 ◁ (𝟙 T ⊗≫ T ◁ η_ S (Sᘁ) ⊗≫ (f ≫ g) ▷ Sᘁ ⊗≫
        𝟙 ((T ⊗ S) ⊗ Sᘁ))) ⊗≫ ((Z.2.β (T ⊗ S)).hom ▷ Sᘁ) ⊗≫ 𝟙 _ := by
  let q := closeFusionMap T S f
  dsimp only [unitComponentAt, crossingBlock, mixedCrossing]
  calc
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (η_ R (Rᘁ) ▷ T)) ⊗≫
      (((Z.2.β R).hom ≫ (g ▷ Z.1)) ▷ ((Rᘁ : D) ⊗ T)) ⊗≫
      ((T ⊗ S) ◁ (Z.1 ◁ q)) ⊗≫ 𝟙 _ := by
        rw [tensorHom_def, comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (η_ R (Rᘁ) ▷ T)) ⊗≫
      ((Z.1 ◁ g) ▷ ((Rᘁ : D) ⊗ T)) ⊗≫
      (((Z.2.β (T ⊗ S)).hom ▷ ((Rᘁ : D) ⊗ T)) ≫ (((T ⊗ S) ⊗ Z.1) ◁ q)) ⊗≫ 𝟙 _ := by
        rw [← Z.2.naturality g]
        monoidal
    _ = _ := by
      rw [← whisker_exchange, ← fusion_coevaluation g f]
      rw [tensorHom_def]
      monoidal

variable {k : Type*} [CommSemiring k] [Preadditive D] [Linear k D]
  [MonoidalPreadditive D] [MonoidalLinear k D]
variable (Z : Center D) (T S : D)

set_option backward.isDefEq.respectTransparency false in
/-- The unit-block diagram depends linearly on its fusion endomorphism. -/
def unitBlockLinear [HasRightDual S] :
    (T ⊗ S ⟶ T ⊗ S) →ₗ[k] (Z.1 ⊗ T ⟶ T ⊗ ((S ⊗ Z.1) ⊗ Sᘁ)) where
  toFun h := 𝟙 _ ⊗≫ (Z.1 ◁ (𝟙 T ⊗≫ T ◁ η_ S (Sᘁ) ⊗≫ h ▷ Sᘁ ⊗≫
    𝟙 ((T ⊗ S) ⊗ Sᘁ))) ⊗≫ ((Z.2.β (T ⊗ S)).hom ▷ Sᘁ) ⊗≫ 𝟙 _
  map_add' := by
    intro x y
    simp [monoidalComp, MonoidalPreadditive.add_whiskerRight,
      MonoidalPreadditive.whiskerLeft_add, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' := by
    intro c x
    simp [monoidalComp, MonoidalLinear.smul_whiskerRight,
      MonoidalLinear.whiskerLeft_smul, Linear.comp_smul, Linear.smul_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The identity fusion endomorphism yields the centre intertwining diagram. -/
theorem unitBlockLinear_id [HasRightDual S] :
    unitBlockLinear (k := k) Z T S (𝟙 (T ⊗ S)) =
      (Z.2.β T).hom ≫ (T ◁ unitComponentAt Z S) := by
  simp only [unitBlockLinear, unitComponentAt, LinearMap.coe_mk, AddHom.coe_mk, Z.2.monoidal]
  convert congrArg (fun (t : (Z.1 ⊗ T) ⊗ 𝟙_ D ⟶ (T ⊗ Z.1) ⊗ (S ⊗ Sᘁ)) =>
    𝟙 (Z.1 ⊗ T) ⊗≫ t ⊗≫ (T ◁ ((Z.2.β S).hom ▷ Sᘁ)) ⊗≫
      𝟙 (T ⊗ ((S ⊗ Z.1) ⊗ Sᘁ)))
    (whisker_exchange (Z.2.β T).hom (η_ S (Sᘁ))) using 1 <;> monoidal

variable (Z : Center C.Obj) (T : C.Obj)

set_option backward.isDefEq.respectTransparency false in
/-- Fusion completeness gives the unit intertwining equation on a summand. -/
theorem unit_sum (j : Fin (rank C)) :
  (∑ p : Σ i : Fin (rank C), crossingIndex C T i j,
    (unitComponent C Z p.1 ▷ T) ≫ crossingSummand C Z.1 T p.1 j p.2) =
      (Z.2.β T).hom ≫ (T ◁ unitComponent C Z j) := by
  erw [← unitBlockLinear_id (k := ℂ) Z T (simples C j), ← crossing_completeness C T j, map_sum]
  simp only [unitComponent, crossingSummand, unit_block, unitBlockLinear, LinearMap.coe_mk, AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in
/-- The proposed induction unit is a morphism in the actual Drinfeld centre. -/
theorem unitCandidate_central :
    (unitCandidate C Z ▷ T) ≫ crossingCandidate C Z.1 T =
      (Z.2.β T).hom ≫ (T ◁ unitCandidate C Z) :=
  let V := inductionSummand C Z.1
  leftDistributor_ext_right (f := V) fun j => by
    simp only [Category.assoc, ← whiskerLeft_comp,
      show unitCandidate C Z ≫ biproduct.π V j = unitComponent C Z j from biproduct.lift_π _ _]
    simpa only [V, unitCandidate, biproduct.lift_eq, sum_whiskerRight, Preadditive.sum_comp,
      comp_whiskerRight, Category.assoc, crossingCandidate_matrix, Preadditive.comp_sum,
      Fintype.sum_sigma, crossingSummand] using unit_sum C Z T j

set_option backward.isDefEq.respectTransparency false in
/-- The forgetful functor is left adjoint to the actual centre induction functor. -/
def actualAdjunction : Center.forget C.Obj ⊣ induction C where
  unit := {
    app Z := ⟨unitCandidate C Z, unitCandidate_central C Z⟩
    naturality {X Y} f := by
      apply Center.ext
      change f.f ≫ unitCandidate C Y = unitCandidate C X ≫ (underlyingFunctor C).map f.f
      refine biproduct.hom_ext _ _ fun i => ?_
      simpa only [underlyingFunctor, unitCandidate, unitComponent, Category.assoc, biproduct.lift_π,
        biproduct.lift_π_assoc, biproduct.map_π] using unitComponentAt_natural (S := simples C i) f }
  counit := underlyingCounit C
  left_triangle_components Z := unitCandidate_counit C Z
  right_triangle_components X := by
    apply Center.ext
    change unitCandidate C ((induction C).obj X) ≫
      (underlyingFunctor C).map ((underlyingCounit C).app X) = 𝟙 (underlying C X)
    refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
    simpa [underlying, Category.assoc] using secondTriangle_entry C X i j

end PropertyF.Ground.CentreInduction

end
end

/-! A linear adjunction supplies the multiplicities needed for the FP-square calculation. -/

@[expose] public noncomputable section
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreInduction
universe v u v' u'

/-- The reverse Hom equivalence of an adjunction is linear when its left
adjoint is linear. -/
def homLinearEquivOfAdjunction {k : Type*} [CommSemiring k] {A : Type u} {B : Type u'}
    [Category.{v} A] [Category.{v'} B] [Preadditive A] [Preadditive B]
    [Linear k A] [Linear k B] (F : A ⥤ B) (G : B ⥤ A)
    [F.Additive] [F.Linear k] (adj : F ⊣ G) (X : A) (Y : B) :
    (X ⟶ G.obj Y) ≃ₗ[k] (F.obj X ⟶ Y) := by
  refine { (adj.homAddEquiv X Y).symm with map_smul' := ?_ }
  intro r f
  change (adj.homEquiv X Y).symm (r • f) = r • (adj.homEquiv X Y).symm f
  simp [Adjunction.homEquiv_counit, Functor.map_smul, Linear.smul_comp]

end PropertyF.Ground.CentreInduction

end

/-! Centre fusion and FP dimension using the constructed induction adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u

variable (C : BraidedFusionCategory.{v,u})
local notation "Sᶜ" => simples C
local notation "𝒵ᶠ" => Integrate.bundledCenter C
local notation "𝒵" => Center C.Obj
local instance (i : Fin (rank C)) : Simple (Sᶜ i) := simples_simple C i

/-- FP dimension is the weighted sum of Hom dimensions to simple objects. -/
theorem fpDimension_eq_sum_to_simple (X : C.Obj) :
    fpDimension C X = ∑ i, (Module.finrank ℂ (X ⟶ Sᶜ i) : ℝ) * fpSimple C i :=
  Finset.sum_congr rfl fun i _ =>
    congrArg (fun n : ℕ => (n : ℝ) * fpSimple C i)
      (finrank_to_simple_eq_from_simple X (Sᶜ i)).symm

/-- The induction adjunction preserves the dimensions of corresponding Hom spaces. -/
theorem finrank_hom_induction (Z : 𝒵) (X : C.Obj) :
    Module.finrank ℂ (Z ⟶ (induction C).obj X) = Module.finrank ℂ (Z.1 ⟶ X) :=
  (homLinearEquivOfAdjunction (k := ℂ) (Center.forget C.Obj)
    (induction C) (actualAdjunction C) Z X).finrank_eq

/-- The FP dimension of a centre object is the weighted Hom sum of its underlying object. -/
theorem center_fpDimension_eq_sum_to_simple [RigidCategory 𝒵] [IsFusionCategory 𝒵] (Z : 𝒵) :
    fpDimension 𝒵ᶠ Z = ∑ i, (Module.finrank ℂ (Z.1 ⟶ Sᶜ i) : ℝ) * fpSimple C i :=
  (Integrate.center_forget_fpDimension C Z).symm.trans (fpDimension_eq_sum_to_simple C Z.1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The centre's global FP dimension is the weighted sum of its induced simples. -/
theorem globalFPDimension_eq_induction_sum [RigidCategory 𝒵] [IsFusionCategory 𝒵] :
    globalFPDimension 𝒵ᶠ =
      ∑ i, fpSimple C i * fpDimension 𝒵ᶠ ((induction C).obj (Sᶜ i)) := by
  symm
  simp_rw [fpDimension, finrank_hom_induction C, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_comm (fpSimple C _), mul_comm _ (fpSimple 𝒵ᶠ _), mul_assoc,
    ← Finset.mul_sum, ← center_fpDimension_eq_sum_to_simple C, fpDimension_simple]
  simp [globalFPDimension, pow_two]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If the actual centre has a fusion structure, its global FP dimension is the square
of the base global FP dimension. -/
theorem globalFPDimension_square_of_actual_induction [RigidCategory 𝒵] [IsFusionCategory 𝒵] :
    globalFPDimension 𝒵ᶠ = (globalFPDimension C) ^ 2 := by
  simp_rw [globalFPDimension_eq_induction_sum C, ← Integrate.center_forget_fpDimension C]
  simp [induction, fpDimension_underlying, fpDimension_simple, globalFPDimension, pow_two,
    Finset.mul_sum, mul_left_comm]

end PropertyF.Ground.CentreInduction
