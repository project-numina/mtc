module
public import PropertyF.Ground.CentreCalculus.PermutationTraceSum
public import PropertyF.Ground.Dimensions.TensorMultiplicativity

/-! Inserting a fixed first strand in the actual permutation action. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Extend a permutation by fixing the first strand. -/
def fixHead (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) where
  toFun σ := Equiv.Perm.decomposeFin.symm (0, σ)
  map_one' := by
    ext x
    refine Fin.cases ?_ (fun j => ?_) x <;> simp
  map_mul' σ τ := by
    ext x
    refine Fin.cases ?_ (fun j => ?_) x <;>
      simp [Equiv.Perm.mul_apply]

theorem fixHead_swap (n : ℕ) (i : Fin n) :
    fixHead (n + 1) (Equiv.swap i.castSucc i.succ) =
      Equiv.swap i.succ.castSucc i.succ.succ := by
  ext x
  refine Fin.cases ?_ (fun j => ?_) x
  · simp [fixHead, Equiv.swap_apply_def, Fin.ext_iff]
  ·
    have h : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
    rw [h]
    simp only [fixHead, MonoidHom.coe_mk, OneHom.coe_mk,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
      Equiv.swap_apply_def, Fin.succ_inj]
    split_ifs <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Inserting a fixed first strand acts by tensoring the old automorphism
on the left with the identity of the new strand. -/
theorem permutationAction_fixHead (X : C)
    (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X)) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 2))) :
    permutationAction X hX (n + 1) (fixHead (n + 2) σ) =
      (tensorLeft X).mapAut (tensorPower X (n + 2)) (permutationAction X hX n σ) := by
  let f := (permutationAction X hX (n + 1)).comp (fixHead (n + 2))
  let g := ((tensorLeft X).mapAut (tensorPower X (n + 2))).comp (permutationAction X hX n)
  have heq : f = g := by
    apply MonoidHom.ext
    intro σ
    obtain ⟨w, rfl⟩ := strandPermutation_surjective n σ
    have hh : f.comp (strandPermutation n) = g.comp (strandPermutation n) := by
      apply FreeGroup.ext_hom
      intro i
      change permutationAction X hX (n + 1) (fixHead (n + 2) (strandPermutation n (FreeGroup.of i))) =
        (tensorLeft X).mapAut (tensorPower X (n + 2))
          (permutationAction X hX n (strandPermutation n (FreeGroup.of i)))
      simp only [strandPermutation, FreeGroup.lift_apply_of, fixHead_swap, permutationAction_swap]
      apply Aut.ext
      apply Iso.ext
      rcases i with ⟨i, hi⟩
      simp [Functor.mapAut, braidGenerator, tensorIso_hom, tensorLeft, id_tensorHom]
    exact DFunLike.congr_fun hh w
  exact DFunLike.congr_fun heq σ

set_option backward.isDefEq.respectTransparency false in
/-- A fixed inserted strand contributes its positive categorical dimension to
the actual permutation trace. -/
theorem tensorPermutationTrace_fixHead (D : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj))
    (hdim : ∀ i, Modular.simpleDimension D p i = (fpSimple D i : ℂ))
    (X : D.Obj) (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X)) :
    ∀ n (σ : Equiv.Perm (Fin n)),
      unitScalar D (p.rightTrace ((tensorPermutationAction X hX (n + 1))
        (fixHead n σ)).asHom) =
      (fpDimension D X : ℂ) * unitScalar D (p.rightTrace ((tensorPermutationAction X hX n) σ).asHom) := by
  intro n
  cases n with
  | zero =>
    intro σ
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst σ
    simp only [map_one, tensorPermutationAction, MonoidHom.one_apply, End.one_asHom]
    change unitScalar D (p.rightTrace (𝟙 (X ⊗ 𝟙_ D.Obj))) =
      (fpDimension D X : ℂ) * unitScalar D (p.rightTrace (𝟙 (𝟙_ D.Obj)))
    rw [Dimensions.rightTrace_unit]
    simp only [unitScalar_eq_equiv, map_one, mul_one]
    rw [← unitScalar_eq_equiv]
    change Dimensions.pivotalDimension D p (X ⊗ 𝟙_ D.Obj) = _
    rw [pivotalDimension_eq_fpDimension D p hdim]
    simp [fpDimension_tensor, fpDimension_unit]
  | succ n =>
    cases n with
    | zero =>
      intro σ
      have hσ : σ = 1 := by
        ext x
        exact congrArg Fin.val ((Fin.eq_zero (σ x)).trans (Fin.eq_zero ((1 : Equiv.Perm (Fin 1)) x)).symm)
      subst σ
      simp only [map_one, tensorPermutationAction, MonoidHom.one_apply, End.one_asHom]
      rw [← pivotalDimension_eq_fpDimension D p hdim X]
      change Dimensions.pivotalDimension D p (tensorPower X 2) =
        Dimensions.pivotalDimension D p X * Dimensions.pivotalDimension D p (tensorPower X 1)
      rw [pivotalDimension_eq_fpDimension D p hdim, pivotalDimension_eq_fpDimension D p hdim,
        pivotalDimension_eq_fpDimension D p hdim]
      simp [tensorPower, fpDimension_tensor]
    | succ n =>
      intro σ
      change unitScalar D (p.rightTrace (Aut.toEnd (permutationAction X hX (n + 1)
        (fixHead (n + 2) σ))).asHom) = _
      rw [permutationAction_fixHead]
      have ht := Dimensions.pivotalTrace_tensor p (unitScalarEquiv D) X (tensorPower X (n + 2))
        (𝟙 X) (Aut.toEnd (permutationAction X hX n σ)).asHom
      simp only [id_tensorHom, ← unitScalar_eq_equiv] at ht
      change unitScalar D (p.rightTrace (X ◁ (Aut.toEnd (permutationAction X hX n σ)).asHom)) = _
      rw [ht]
      change Dimensions.pivotalDimension D p X * _ = _
      rw [pivotalDimension_eq_fpDimension D p hdim]
      rfl

end PropertyF.Ground.CentreCalculus
