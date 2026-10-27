module
public import PropertyF.Ground.CentreInduction.SecondTriangle

/-! Centrality of the induction unit and the centre-forgetful adjunction. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.ExactPairing
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- Resolving a fusion strand commutes with coevaluation. -/
theorem fusion_coevaluation (T S R : C.Obj) (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    𝟙 T ⊗≫ (η_ R (Rᘁ) ▷ T) ⊗≫ (g ⊗ₘ closeFusionMap C T S R f) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ) =
      𝟙 T ⊗≫ (T ◁ η_ S (Sᘁ)) ⊗≫ ((f ≫ g) ▷ (Sᘁ)) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ) := by
  have hr : (𝟙 T ⊗≫ (T ◁ η_ S (Sᘁ)) ⊗≫ ((f ≫ g) ▷ (Sᘁ)) ⊗≫
      𝟙 ((T ⊗ S) ⊗ Sᘁ)) = (tensorRightHomEquiv T S (Sᘁ) (T ⊗ S)) (f ≫ g) := by
    dsimp [tensorRightHomEquiv]
    monoidal
  rw [hr]
  apply (tensorRightHomEquiv T S (Sᘁ) (T ⊗ S)).symm.injective
  simp only [Equiv.symm_apply_apply]
  change ((𝟙 T ⊗≫ (η_ R (Rᘁ) ▷ T) ⊗≫ (g ⊗ₘ closeFusionMap C T S R f) ⊗≫
    𝟙 ((T ⊗ S) ⊗ Sᘁ)) ▷ S) ≫ (α_ (T ⊗ S) (Sᘁ) S).hom ≫
      ((T ⊗ S) ◁ ε_ S (Sᘁ)) ≫ (ρ_ (T ⊗ S)).hom = f ≫ g
  let q := closeFusionMap C T S R f
  have hq := closeFusionMap_evaluation C T S R f
  change q ▷ S ≫ ε_ S (Sᘁ) = 𝟙 _ ⊗≫ ((Rᘁ : C.Obj) ◁ f) ⊗≫ ε_ R (Rᘁ) at hq
  change ((𝟙 T ⊗≫ (η_ R (Rᘁ) ▷ T) ⊗≫ (g ⊗ₘ q) ⊗≫
    𝟙 ((T ⊗ S) ⊗ Sᘁ)) ▷ S) ≫ (α_ (T ⊗ S) (Sᘁ) S).hom ≫
      ((T ⊗ S) ◁ ε_ S (Sᘁ)) ≫ (ρ_ (T ⊗ S)).hom = f ≫ g
  clear_value q
  calc
    _ = 𝟙 _ ⊗≫ (η_ R (Rᘁ) ▷ (T ⊗ S)) ⊗≫ (R ◁ (q ▷ S)) ⊗≫
      ((g ▷ ((Sᘁ : C.Obj) ⊗ S)) ≫ ((T ⊗ S) ◁ ε_ S (Sᘁ))) ⊗≫ 𝟙 _ := by
        simp only [tensorHom_def', comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (η_ R (Rᘁ) ▷ (T ⊗ S)) ⊗≫ (R ◁ (q ▷ S)) ⊗≫
      ((R ◁ ε_ S (Sᘁ)) ≫ (g ▷ (𝟙_ C.Obj))) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (η_ R (Rᘁ) ▷ (T ⊗ S)) ⊗≫ (R ◁ ((q ▷ S) ≫ ε_ S (Sᘁ))) ⊗≫
      (g ▷ (𝟙_ C.Obj)) ⊗≫ 𝟙 _ := by simp only [whiskerLeft_comp]; monoidal
    _ = 𝟙 _ ⊗≫ (η_ R (Rᘁ) ▷ (T ⊗ S)) ⊗≫
      (R ◁ (𝟙 _ ⊗≫ ((Rᘁ : C.Obj) ◁ f) ⊗≫ ε_ R (Rᘁ))) ⊗≫
      (g ▷ (𝟙_ C.Obj)) ⊗≫ 𝟙 _ := by rw [hq]
    _ = 𝟙 _ ⊗≫ ((η_ R (Rᘁ) ▷ (T ⊗ S)) ≫ (((R ⊗ Rᘁ) : C.Obj) ◁ f)) ⊗≫
      (R ◁ ε_ R (Rᘁ)) ⊗≫ g := by monoidal
    _ = 𝟙 _ ⊗≫ (((𝟙_ C.Obj) ◁ f) ≫ (η_ R (Rᘁ) ▷ R)) ⊗≫
      (R ◁ ε_ R (Rᘁ)) ⊗≫ g := by rw [whisker_exchange]
    _ = f ⊗≫ ((η_ R (Rᘁ) ▷ R) ⊗≫ (R ◁ ε_ R (Rᘁ))) ⊗≫ g := by monoidal
    _ = _ := by rw [evaluation_coevaluation'']; monoidal

set_option backward.isDefEq.respectTransparency false in
/-- A unit component followed by a crossing block reduces to a fusion endomorphism. -/
theorem unit_block (Z : CategoryTheory.Center C.Obj) (T S R : C.Obj)
    (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    (( (ρ_ Z.1).inv ≫ (Z.1 ◁ η_ R (Rᘁ)) ≫ (α_ Z.1 R (Rᘁ)).inv ≫
      ((Z.2.β R).hom ▷ (Rᘁ))) ▷ T) ≫ crossingBlock C Z.1 T R S g f =
      𝟙 _ ⊗≫ (Z.1 ◁ (𝟙 T ⊗≫ T ◁ η_ S (Sᘁ) ⊗≫ (f ≫ g) ▷ Sᘁ ⊗≫
        𝟙 ((T ⊗ S) ⊗ Sᘁ))) ⊗≫ ((Z.2.β (T ⊗ S)).hom ▷ Sᘁ) ⊗≫ 𝟙 _ := by
  let q := closeFusionMap C T S R f
  let bR := (Z.2.β R).hom
  let bTS := (Z.2.β (T ⊗ S)).hom
  have hn : bR ≫ (g ▷ Z.1) = (Z.1 ◁ g) ≫ bTS := (Z.2.naturality g).symm
  have hf : (𝟙 T ⊗≫ (η_ R (Rᘁ) ▷ T) ⊗≫ (g ⊗ₘ q) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ)) =
      𝟙 T ⊗≫ (T ◁ η_ S (Sᘁ)) ⊗≫ ((f ≫ g) ▷ Sᘁ) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ) :=
    fusion_coevaluation C T S R g f
  change (((ρ_ Z.1).inv ≫ (Z.1 ◁ η_ R (Rᘁ)) ≫ (α_ Z.1 R (Rᘁ)).inv ≫ (bR ▷ Rᘁ)) ▷ T) ≫
    ((α_ (R ⊗ Z.1) (Rᘁ) T).hom ≫ ((g ▷ Z.1) ⊗ₘ q) ≫
      (α_ (T ⊗ S) Z.1 (Sᘁ)).hom ≫ (α_ T S (Z.1 ⊗ Sᘁ)).hom ≫
        (T ◁ (α_ S Z.1 (Sᘁ)).inv)) =
      𝟙 _ ⊗≫ (Z.1 ◁ (𝟙 T ⊗≫ T ◁ η_ S (Sᘁ) ⊗≫ (f ≫ g) ▷ Sᘁ ⊗≫
        𝟙 ((T ⊗ S) ⊗ Sᘁ))) ⊗≫ (bTS ▷ Sᘁ) ⊗≫ 𝟙 _
  clear_value q bR bTS
  calc
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (η_ R (Rᘁ) ▷ T)) ⊗≫
      ((bR ≫ (g ▷ Z.1)) ▷ ((Rᘁ : C.Obj) ⊗ T)) ⊗≫
      ((T ⊗ S) ◁ (Z.1 ◁ q)) ⊗≫ 𝟙 _ := by
        simp only [tensorHom_def, comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (η_ R (Rᘁ) ▷ T)) ⊗≫
      (((Z.1 ◁ g) ≫ bTS) ▷ ((Rᘁ : C.Obj) ⊗ T)) ⊗≫
      ((T ⊗ S) ◁ (Z.1 ◁ q)) ⊗≫ 𝟙 _ := by rw [hn]
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (η_ R (Rᘁ) ▷ T)) ⊗≫
      ((Z.1 ◁ g) ▷ ((Rᘁ : C.Obj) ⊗ T)) ⊗≫
      ((bTS ▷ ((Rᘁ : C.Obj) ⊗ T)) ≫ (((T ⊗ S) ⊗ Z.1) ◁ q)) ⊗≫ 𝟙 _ := by
        simp only [comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (η_ R (Rᘁ) ▷ T)) ⊗≫
      ((Z.1 ◁ g) ▷ ((Rᘁ : C.Obj) ⊗ T)) ⊗≫
      ((((Z.1 ⊗ (T ⊗ S)) ◁ q)) ≫ (bTS ▷ (Sᘁ))) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ (𝟙 T ⊗≫ (η_ R (Rᘁ) ▷ T) ⊗≫ (g ⊗ₘ q) ⊗≫ 𝟙 ((T ⊗ S) ⊗ Sᘁ))) ⊗≫
      (bTS ▷ Sᘁ) ⊗≫ 𝟙 _ := by simp only [tensorHom_def, whiskerLeft_comp]; monoidal
    _ = _ := by rw [hf]

set_option backward.isDefEq.respectTransparency false in
/-- The unit-block diagram depends linearly on its fusion endomorphism. -/
def unitBlockLinear (Z : CategoryTheory.Center C.Obj) (T S : C.Obj) :
    (T ⊗ S ⟶ T ⊗ S) →ₗ[ℂ] (Z.1 ⊗ T ⟶ T ⊗ ((S ⊗ Z.1) ⊗ Sᘁ)) where
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
theorem unitBlockLinear_id (Z : CategoryTheory.Center C.Obj) (T S : C.Obj) :
    unitBlockLinear C Z T S (𝟙 (T ⊗ S)) = (Z.2.β T).hom ≫ (T ◁
      ((ρ_ Z.1).inv ≫ (Z.1 ◁ η_ S (Sᘁ)) ≫ (α_ Z.1 S (Sᘁ)).inv ≫
        ((Z.2.β S).hom ▷ Sᘁ))) := by
  dsimp only [unitBlockLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Z.2.monoidal]
  simp only [id_whiskerRight, whiskerLeft_id, Category.comp_id, Category.id_comp]
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
    _ = 𝟙 _ ⊗≫ ((bT ▷ (𝟙_ C.Obj)) ≫ ((T ⊗ Z.1) ◁ η_ S (Sᘁ))) ⊗≫
      (T ◁ (bS ▷ Sᘁ)) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = _ := by monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Fusion completeness gives the unit intertwining equation on a summand. -/
theorem unit_sum (Z : CategoryTheory.Center C.Obj) (T : C.Obj) (j : Fin (rank C)) :
  (∑ p : Σ i : Fin (rank C), Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j)),
    (unitComponent C Z p.1 ▷ T) ≫ crossingBlock C Z.1 T (simples C p.1) (simples C j)
      (crossingInclusion C T p.1 j p.2) (crossingProjection C T p.1 j p.2)) =
    (Z.2.β T).hom ≫ (T ◁ unitComponent C Z j) := by
  classical
  calc
    _ = ∑ p : Σ i : Fin (rank C), Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j)),
      unitBlockLinear C Z T (simples C j) (crossingProjection C T p.1 j p.2 ≫
        crossingInclusion C T p.1 j p.2) := by
      apply Finset.sum_congr rfl
      intro p _
      exact unit_block C Z T (simples C j) (simples C p.1)
        (crossingInclusion C T p.1 j p.2) (crossingProjection C T p.1 j p.2)
    _ = unitBlockLinear C Z T (simples C j)
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
  have h := congrArg (fun f => unitCandidate C Z ≫ f) (biproduct.total (f := V))
  have hp (i) : unitCandidate C Z ≫ biproduct.π V i = unitComponent C Z i :=
    biproduct.lift_π _ _
  simp only [Preadditive.comp_sum, ← Category.assoc, hp] at h
  have hid : unitCandidate C Z ≫ 𝟙 (⨁ V) = unitCandidate C Z := Category.comp_id _
  rw [hid] at h
  exact h.symm

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
        (unitComponent C Z i ▷ T) ≫ crossingBlock C Z.1 T (simples C i) (simples C j)
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

/-- The forgetful functor is left adjoint to the actual centre induction functor. -/
def actualAdjunction : CategoryTheory.Center.forget C.Obj ⊣ induction C :=
  adjunctionOfHalfBraiding C (halfBraidingOfCrossingCandidate C)
    (halfBraidingOfCrossingCandidate_natural C)
    (fun Z T => unitCandidate_central C Z T)
    (secondTriangle C)

end PropertyF.Ground.CentreInduction
