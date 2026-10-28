module
public import PropertyF.Ground.CentreInduction.SecondTriangle
public import PropertyF.Ground.CentreInduction.Representatives
public import PropertyF.Ground.CentreBundle.Fusion
public import PropertyF.Ground.Fusion.SpectralIntegral

section
/-! Centrality of the induction unit and the centre-forgetful adjunction. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.ExactPairing
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]

set_option backward.isDefEq.respectTransparency false in
/-- Resolving a fusion strand commutes with coevaluation. -/
theorem fusion_coevaluation {T S R : D} (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    𝟙 T ⊗≫ (η_ R (Rᘁ) ▷ T) ⊗≫ (g ⊗ₘ closeFusionMap T S R f) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ) =
      𝟙 T ⊗≫ (T ◁ η_ S (Sᘁ)) ⊗≫ ((f ≫ g) ▷ (Sᘁ)) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ) := by
  have hr : (𝟙 T ⊗≫ (T ◁ η_ S (Sᘁ)) ⊗≫ ((f ≫ g) ▷ (Sᘁ)) ⊗≫
      𝟙 ((T ⊗ S) ⊗ Sᘁ)) = (tensorRightHomEquiv T S (Sᘁ) (T ⊗ S)) (f ≫ g) := by
    dsimp [tensorRightHomEquiv]
    monoidal
  rw [hr]
  apply (tensorRightHomEquiv T S (Sᘁ) (T ⊗ S)).symm.injective
  simp only [Equiv.symm_apply_apply]
  change ((𝟙 T ⊗≫ (η_ R (Rᘁ) ▷ T) ⊗≫ (g ⊗ₘ closeFusionMap T S R f) ⊗≫
    𝟙 ((T ⊗ S) ⊗ Sᘁ)) ▷ S) ≫ (α_ (T ⊗ S) (Sᘁ) S).hom ≫
      ((T ⊗ S) ◁ ε_ S (Sᘁ)) ≫ (ρ_ (T ⊗ S)).hom = f ≫ g
  let q := closeFusionMap T S R f
  have hq := closeFusionMap_evaluation f
  change q ▷ S ≫ ε_ S (Sᘁ) = 𝟙 _ ⊗≫ ((Rᘁ : D) ◁ f) ⊗≫ ε_ R (Rᘁ) at hq
  change ((𝟙 T ⊗≫ (η_ R (Rᘁ) ▷ T) ⊗≫ (g ⊗ₘ q) ⊗≫
    𝟙 ((T ⊗ S) ⊗ Sᘁ)) ▷ S) ≫ (α_ (T ⊗ S) (Sᘁ) S).hom ≫
      ((T ⊗ S) ◁ ε_ S (Sᘁ)) ≫ (ρ_ (T ⊗ S)).hom = f ≫ g
  clear_value q
  calc
    _ = 𝟙 _ ⊗≫ (η_ R (Rᘁ) ▷ (T ⊗ S)) ⊗≫ (R ◁ (q ▷ S)) ⊗≫
      ((g ▷ ((Sᘁ : D) ⊗ S)) ≫ ((T ⊗ S) ◁ ε_ S (Sᘁ))) ⊗≫ 𝟙 _ := by
        simp only [tensorHom_def']
        monoidal
    _ = 𝟙 _ ⊗≫ (η_ R (Rᘁ) ▷ (T ⊗ S)) ⊗≫ (R ◁ (q ▷ S)) ⊗≫
      ((R ◁ ε_ S (Sᘁ)) ≫ (g ▷ (𝟙_ D))) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (η_ R (Rᘁ) ▷ (T ⊗ S)) ⊗≫ (R ◁ ((q ▷ S) ≫ ε_ S (Sᘁ))) ⊗≫
      (g ▷ (𝟙_ D)) ⊗≫ 𝟙 _ := by simp only [whiskerLeft_comp]; monoidal
    _ = 𝟙 _ ⊗≫ (η_ R (Rᘁ) ▷ (T ⊗ S)) ⊗≫
      (R ◁ (𝟙 _ ⊗≫ ((Rᘁ : D) ◁ f) ⊗≫ ε_ R (Rᘁ))) ⊗≫
      (g ▷ (𝟙_ D)) ⊗≫ 𝟙 _ := by rw [hq]
    _ = 𝟙 _ ⊗≫ ((η_ R (Rᘁ) ▷ (T ⊗ S)) ≫ (((R ⊗ Rᘁ) : D) ◁ f)) ⊗≫
      (R ◁ ε_ R (Rᘁ)) ⊗≫ g := by monoidal
    _ = 𝟙 _ ⊗≫ (((𝟙_ D) ◁ f) ≫ (η_ R (Rᘁ) ▷ R)) ⊗≫
      (R ◁ ε_ R (Rᘁ)) ⊗≫ g := by rw [whisker_exchange]
    _ = f ⊗≫ ((η_ R (Rᘁ) ▷ R) ⊗≫ (R ◁ ε_ R (Rᘁ))) ⊗≫ g := by monoidal
    _ = _ := by rw [evaluation_coevaluation'']; monoidal

set_option backward.isDefEq.respectTransparency false in
/-- A unit component followed by a crossing block reduces to a fusion endomorphism. -/
theorem unit_block (Z : CategoryTheory.Center D) {T S R : D}
    (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    (( (ρ_ Z.1).inv ≫ (Z.1 ◁ η_ R (Rᘁ)) ≫ (α_ Z.1 R (Rᘁ)).inv ≫
      ((Z.2.β R).hom ▷ (Rᘁ))) ▷ T) ≫ crossingBlock Z.1 T R S g f =
      𝟙 _ ⊗≫ (Z.1 ◁ (𝟙 T ⊗≫ T ◁ η_ S (Sᘁ) ⊗≫ (f ≫ g) ▷ Sᘁ ⊗≫
        𝟙 ((T ⊗ S) ⊗ Sᘁ))) ⊗≫ ((Z.2.β (T ⊗ S)).hom ▷ Sᘁ) ⊗≫ 𝟙 _ := by
  let q := closeFusionMap T S R f
  let bR := (Z.2.β R).hom
  let bTS := (Z.2.β (T ⊗ S)).hom
  have hn : bR ≫ (g ▷ Z.1) = (Z.1 ◁ g) ≫ bTS := (Z.2.naturality g).symm
  have hf : (𝟙 T ⊗≫ (η_ R (Rᘁ) ▷ T) ⊗≫ (g ⊗ₘ q) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ)) =
      𝟙 T ⊗≫ (T ◁ η_ S (Sᘁ)) ⊗≫ ((f ≫ g) ▷ Sᘁ) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ) :=
    fusion_coevaluation g f
  change (((ρ_ Z.1).inv ≫ (Z.1 ◁ η_ R (Rᘁ)) ≫ (α_ Z.1 R (Rᘁ)).inv ≫ (bR ▷ Rᘁ)) ▷ T) ≫
    ((α_ (R ⊗ Z.1) (Rᘁ) T).hom ≫ ((g ▷ Z.1) ⊗ₘ q) ≫
      (α_ (T ⊗ S) Z.1 (Sᘁ)).hom ≫ (α_ T S (Z.1 ⊗ Sᘁ)).hom ≫
        (T ◁ (α_ S Z.1 (Sᘁ)).inv)) =
      𝟙 _ ⊗≫ (Z.1 ◁ (𝟙 T ⊗≫ T ◁ η_ S (Sᘁ) ⊗≫ (f ≫ g) ▷ Sᘁ ⊗≫
        𝟙 ((T ⊗ S) ⊗ Sᘁ))) ⊗≫ (bTS ▷ Sᘁ) ⊗≫ 𝟙 _
  clear_value q bR bTS
  calc
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (η_ R (Rᘁ) ▷ T)) ⊗≫
      ((bR ≫ (g ▷ Z.1)) ▷ ((Rᘁ : D) ⊗ T)) ⊗≫
      ((T ⊗ S) ◁ (Z.1 ◁ q)) ⊗≫ 𝟙 _ := by
        simp only [tensorHom_def, comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (η_ R (Rᘁ) ▷ T)) ⊗≫
      (((Z.1 ◁ g) ≫ bTS) ▷ ((Rᘁ : D) ⊗ T)) ⊗≫
      ((T ⊗ S) ◁ (Z.1 ◁ q)) ⊗≫ 𝟙 _ := by rw [hn]
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (η_ R (Rᘁ) ▷ T)) ⊗≫
      ((Z.1 ◁ g) ▷ ((Rᘁ : D) ⊗ T)) ⊗≫
      ((bTS ▷ ((Rᘁ : D) ⊗ T)) ≫ (((T ⊗ S) ⊗ Z.1) ◁ q)) ⊗≫ 𝟙 _ := by
        simp only [comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (η_ R (Rᘁ) ▷ T)) ⊗≫
      ((Z.1 ◁ g) ▷ ((Rᘁ : D) ⊗ T)) ⊗≫
      ((((Z.1 ⊗ (T ⊗ S)) ◁ q)) ≫ (bTS ▷ (Sᘁ))) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (𝟙 T ⊗≫ (η_ R (Rᘁ) ▷ T) ⊗≫ (g ⊗ₘ q) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ))) ⊗≫
      (bTS ▷ Sᘁ) ⊗≫ 𝟙 _ := by simp only [tensorHom_def]; monoidal
    _ = _ := by rw [hf]

variable {k : Type*} [CommSemiring k] [Preadditive D] [Linear k D]
  [MonoidalPreadditive D] [MonoidalLinear k D]

set_option backward.isDefEq.respectTransparency false in
/-- The unit-block diagram depends linearly on its fusion endomorphism. -/
def unitBlockLinear (Z : CategoryTheory.Center D) (T S : D) :
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
theorem unitBlockLinear_id (Z : CategoryTheory.Center D) (T S : D) :
    unitBlockLinear (k := k) Z T S (𝟙 (T ⊗ S)) = (Z.2.β T).hom ≫ (T ◁
      ((ρ_ Z.1).inv ≫ (Z.1 ◁ η_ S (Sᘁ)) ≫ (α_ Z.1 S (Sᘁ)).inv ≫
        ((Z.2.β S).hom ▷ Sᘁ))) := by
  dsimp only [unitBlockLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Z.2.monoidal]
  simp only [id_whiskerRight]
  let bT := (Z.2.β T).hom
  let bS := (Z.2.β S).hom
  change 𝟙 _ ⊗≫ (Z.1 ◁ (𝟙 T ⊗≫ T ◁ η_ S (Sᘁ) ⊗≫
      𝟙 ((T ⊗ S) ⊗ Sᘁ) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ))) ⊗≫
    (((α_ Z.1 T S).inv ≫ (bT ▷ S) ≫ (α_ T Z.1 S).hom ≫ (T ◁ bS) ≫
      (α_ T S Z.1).inv) ▷ Sᘁ) ⊗≫ 𝟙 (T ⊗ ((S ⊗ Z.1) ⊗ Sᘁ)) =
    bT ≫ (T ◁ ((ρ_ Z.1).inv ≫ (Z.1 ◁ η_ S (Sᘁ)) ≫
      (α_ Z.1 S (Sᘁ)).inv ≫ (bS ▷ Sᘁ)))
  clear_value bT bS
  calc
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ T ◁ η_ S (Sᘁ)) ⊗≫
      ((bT ▷ (S ⊗ Sᘁ)) ≫ ((T ⊗ Z.1) ◁ 𝟙 (S ⊗ Sᘁ))) ⊗≫
      (T ◁ (bS ▷ Sᘁ)) ⊗≫ 𝟙 _ := by simp only [comp_whiskerRight]; monoidal
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ T ◁ η_ S (Sᘁ)) ⊗≫ (bT ▷ (S ⊗ Sᘁ)) ⊗≫
      (T ◁ (bS ▷ Sᘁ)) ⊗≫ 𝟙 _ := by simp
    _ = 𝟙 _ ⊗≫ (((Z.1 ⊗ T) ◁ η_ S (Sᘁ)) ≫ (bT ▷ (S ⊗ Sᘁ))) ⊗≫
      (T ◁ (bS ▷ Sᘁ)) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ ((bT ▷ (𝟙_ D)) ≫ ((T ⊗ Z.1) ◁ η_ S (Sᘁ))) ⊗≫
      (T ◁ (bS ▷ Sᘁ)) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = _ := by monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Fusion completeness gives the unit intertwining equation on a summand. -/
theorem unit_sum (Z : CategoryTheory.Center C.Obj) (T : C.Obj) (j : Fin (rank C)) :
  (∑ p : Σ i : Fin (rank C), Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j)),
    (unitComponent C Z p.1 ▷ T) ≫ crossingBlock Z.1 T (simples C p.1) (simples C j)
      (crossingInclusion C T p.1 j p.2) (crossingProjection C T p.1 j p.2)) =
    (Z.2.β T).hom ≫ (T ◁ unitComponent C Z j) := by
  classical
  calc
    _ = ∑ p : Σ i : Fin (rank C), Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j)),
      unitBlockLinear (k := ℂ) Z T (simples C j) (crossingProjection C T p.1 j p.2 ≫
        crossingInclusion C T p.1 j p.2) := by
      apply Finset.sum_congr rfl
      intro p _
      exact unit_block Z
        (crossingInclusion C T p.1 j p.2) (crossingProjection C T p.1 j p.2)
    _ = unitBlockLinear (k := ℂ) Z T (simples C j)
      (∑ p : Σ i : Fin (rank C), Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j)),
        crossingProjection C T p.1 j p.2 ≫ crossingInclusion C T p.1 j p.2) := by rw [map_sum]
    _ = _ := by rw [crossing_completeness, unitBlockLinear_id]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The underlying unit is the sum of its biproduct components. -/
theorem unitCandidate_sum (Z : CategoryTheory.Center C.Obj) :
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ Z.1) ⊗ (simples C k)ᘁ
  unitCandidate C Z = ∑ i, unitComponent C Z i ≫ biproduct.ι V i := by
  classical
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ Z.1) ⊗ (simples C k)ᘁ
  have hp (i) : unitCandidate C Z ≫ biproduct.π V i = unitComponent C Z i :=
    biproduct.lift_π _ _
  have hid : unitCandidate C Z ≫ 𝟙 (⨁ V) = unitCandidate C Z := Category.comp_id _
  simpa only [hid, Preadditive.comp_sum, ← Category.assoc, hp] using
    (congrArg (fun f => unitCandidate C Z ≫ f) (biproduct.total (f := V))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The proposed induction unit is a morphism in the actual Drinfeld centre. -/
theorem unitCandidate_central (Z : CategoryTheory.Center C.Obj) (T : C.Obj) :
    (unitCandidate C Z ▷ T) ≫ crossingCandidate C Z.1 T =
      (Z.2.β T).hom ≫ (T ◁ unitCandidate C Z) := by
  classical
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ Z.1) ⊗ (simples C k)ᘁ
  apply (cancel_mono (leftDistributor T V).hom).1
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, leftDistributor_hom_comp_biproduct_π]
  have hcomp : unitCandidate C Z ≫ biproduct.π V j = unitComponent C Z j := by
    exact biproduct.lift_π _ _
  have hr : (Z.2.β T).hom ≫ (T ◁ unitCandidate C Z) ≫ (T ◁ biproduct.π V j) =
      (Z.2.β T).hom ≫ (T ◁ unitComponent C Z j) := by
    rw [← whiskerLeft_comp, hcomp]
  have hl : (unitCandidate C Z ▷ T) ≫ crossingCandidate C Z.1 T ≫ (T ◁ biproduct.π V j) =
      ∑ i, ∑ a : Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j)),
        (unitComponent C Z i ▷ T) ≫ crossingBlock Z.1 T (simples C i) (simples C j)
          (crossingInclusion C T i j a) (crossingProjection C T i j a) := by
    rw [unitCandidate_sum]
    simp only [sum_whiskerRight, Preadditive.sum_comp, comp_whiskerRight, Category.assoc]
    apply Finset.sum_congr rfl
    intro i _
    have hm := crossingCandidate_matrix C Z.1 T i j
    have hmi := congrArg (fun k => (unitComponent C Z i ▷ T) ≫ k) hm
    simpa [Category.assoc, Preadditive.comp_sum] using hmi
  calc
    _ = _ := hl
    _ = _ := by simpa [Fintype.sum_sigma] using unit_sum C Z T j
    _ = _ := hr.symm

set_option backward.isDefEq.respectTransparency false in
/-- The forgetful functor is left adjoint to the actual centre induction functor. -/
def actualAdjunction : CategoryTheory.Center.forget C.Obj ⊣ induction C where
  unit := {
    app Z := ⟨unitCandidate C Z, unitCandidate_central C Z⟩
    naturality {X Y} f := by
      apply CategoryTheory.Center.ext
      change f.f ≫ unitCandidate C Y = unitCandidate C X ≫ (underlyingFunctor C).map f.f
      apply biproduct.hom_ext
      intro i
      simp only [underlyingFunctor, unitCandidate, Category.assoc, biproduct.lift_π, biproduct.lift_π_assoc, biproduct.map_π]
      simpa only [Category.assoc] using unitComponent_natural C f i }
  counit := underlyingCounit C
  left_triangle_components Z := unitCandidate_counit C Z
  right_triangle_components X := by
    apply CategoryTheory.Center.ext
    exact secondTriangle C X

end PropertyF.Ground.CentreInduction

end
end

/-! Centre fusion and FP dimension using the constructed induction adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u

/-- If the actual centre already has a fusion structure, its global FP
 dimension is the square of the base global FP dimension. -/
theorem globalFPDimension_square_of_actual_induction (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)] :
    globalFPDimension (Integrate.bundledCenter C) = (globalFPDimension C) ^ 2 :=
  globalFPDimension_square_of_adjunction C (induction C) (actualAdjunction C)
    (fun _ => ⟨Iso.refl _⟩)





end PropertyF.Ground.CentreInduction
