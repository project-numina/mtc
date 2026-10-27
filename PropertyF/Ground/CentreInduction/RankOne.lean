module
public import PropertyF.Ground.CentreInduction.UnitTest
public import PropertyF.Ground.CentreInduction.Representatives
public import PropertyF.Ground.CentreBundle.Fusion

/-! Induction and fusion in the rank-one case. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- In rank one the finite induction sum is canonically isomorphic to its
middle factor, up to the chosen unit representative. -/
def underlyingIsoOfRankOne (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] (X : C.Obj) : underlying C X ≅ X := by
  letI : Unique (Fin (rank C)) := { default := unitIndex C, uniq := fun i => Subsingleton.elim _ _ }
  let e : simples C (unitIndex C) ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  let d : (simples C (unitIndex C))ᘁ ≅ 𝟙_ C.Obj :=
    Dimensions.rightDualIsoMap e.symm ≪≫ Dimensions.rightDualUnitIso
  change (⨁ (fun i : Fin (rank C) => (simples C i ⊗ X) ⊗ (simples C i)ᘁ)) ≅ X
  exact biproductUniqueIso _ ≪≫ ((e ⊗ᵢ Iso.refl X) ⊗ᵢ d) ≪≫
    ((λ_ X) ⊗ᵢ Iso.refl (𝟙_ C.Obj)) ≪≫ ρ_ X

/-- The quasi-inverse of centre forget is a right adjoint in rank one. -/
def rightAdjointOfRankOne (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] : C.Obj ⥤ CategoryTheory.Center C.Obj :=
  (centerForgetEquivalenceOfRankOne C).inverse

/-- The adjunction is induced by the actual equivalence with the centre. -/
def adjunctionOfRankOne (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] :
    CategoryTheory.Center.forget C.Obj ⊣ rightAdjointOfRankOne C :=
  (centerForgetEquivalenceOfRankOne C).toAdjunction

/-- The rank-one right adjoint has the expected underlying induction sum. -/
theorem rightAdjoint_underlying_of_rank_one (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] (X : C.Obj) :
    Nonempty (((rightAdjointOfRankOne C).obj X).1 ≅ underlying C X) := by
  let e := centerForgetEquivalenceOfRankOne C
  exact ⟨e.counitIso.app X ≪≫ (underlyingIsoOfRankOne C X).symm⟩

/-- In rank one the centre has a ground fusion structure as soon as its
rigidity is supplied; this special case does not assume spherical data. -/
theorem fusion_of_rank_one (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] [RigidCategory (CategoryTheory.Center C.Obj)] :
    IsFusionCategory (CategoryTheory.Center C.Obj) := by
  classical
  let F := CategoryTheory.Center.forget C.Obj
  letI : F.Full := centerForgetFullOfRankOne C
  let S : Fin (rank C) → CategoryTheory.Center C.Obj := fun i =>
    (CategoryTheory.Center.ofBraided C.Obj).obj (simples C i)
  apply CentreBundle.fusionOfFiniteSemisimple C
  refine ⟨rank C, S, ?_, ?_, ?_⟩
  · intro i
    letI : Simple (S i).1 := simples_simple C i
    exact Centre.centerSimple_of_underlying (S i)
  · intro i j ⟨e⟩
    exact simples_injective C i j ⟨F.mapIso e⟩
  · intro X
    obtain ⟨m, ⟨e⟩⟩ := simples_decompose C X.1
    let W : (Σ i, Fin (m i)) → CategoryTheory.Center C.Obj := fun p => S p.1
    have e' : F.obj X ≅ F.obj (⨁ W) := e ≪≫ (F.mapBiproduct W).symm
    exact ⟨m, ⟨F.preimageIso e'⟩⟩

/-- With centre rigidity, the centre global FP-square formula holds in
rank one without assuming an adjunction or loop-sliding identity. -/
theorem globalFPDimension_square_of_rank_one (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] [RigidCategory (CategoryTheory.Center C.Obj)] :
    letI : IsFusionCategory (CategoryTheory.Center C.Obj) := fusion_of_rank_one C
    globalFPDimension (Integrate.bundledCenter C) = (globalFPDimension C) ^ 2 := by
  letI : IsFusionCategory (CategoryTheory.Center C.Obj) := fusion_of_rank_one C
  exact globalFPDimension_square_of_adjunction C (rightAdjointOfRankOne C)
    (adjunctionOfRankOne C) (fun i => rightAdjoint_underlying_of_rank_one C _)

end PropertyF.Ground.CentreInduction
