module
public import PropertyF.Ground.CentreModular.VafaNaturalTensor

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u w
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Any isomorphism-invariant additive object function is determined by
its values on simples and the actual Hom-space multiplicities. -/
theorem additive_object_function_decomposition
    (C : BraidedFusionCategory.{v,u}) (M : Type w) [AddCommGroup M] [Module ℝ M]
    (f : C.Obj → M)
    (hiso : ∀ {X Y : C.Obj}, (X ≅ Y) → f X = f Y)
    (hzero : ∀ X, IsZero X → f X = 0)
    (hadd : ∀ X Y, f (X ⊞ Y) = f X + f Y)
    (X : C.Obj) :
    f X = ∑ i, (Module.finrank ℂ (simples C i ⟶ X) : ℝ) • f (simples C i) := by
  classical
  let : ∀ A B : C.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  have hsimple (S : C.Obj) [Simple S] :
      f S = ∑ i, (Module.finrank ℂ (simples C i ⟶ S) : ℝ) • f (simples C i) := by
    obtain ⟨j, ⟨e⟩⟩ := exists_simple_iso C S
    have hr (i : Fin (rank C)) : Module.finrank ℂ (simples C i ⟶ S) =
        Module.finrank ℂ (simples C i ⟶ simples C j) :=
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq
    simp_rw [hr, finrank_simples_hom]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_eq_single j]
    · simpa using hiso e
    · intro i _ hij
      simp [hij]
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
  have h := base_finite_simple_sum C X
  induction h with
  | @zero W hz =>
    rw [hzero W hz]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro i _
    have : Subsingleton (simples C i ⟶ W) := ⟨fun a b => hz.eq_of_tgt a b⟩
    simp [Module.finrank_zero_of_subsingleton]
  | @cons W S K hs hk he ih =>
    obtain ⟨e⟩ := he
    let : Simple S := hs
    rw [hiso e, hadd, hsimple S, ih]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hdim : Module.finrank ℂ (simples C i ⟶ W) =
        Module.finrank ℂ (simples C i ⟶ S) + Module.finrank ℂ (simples C i ⟶ K) := by
      calc
        _ = Module.finrank ℂ (simples C i ⟶ S ⊞ K) :=
          (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq
        _ = Module.finrank ℂ ((simples C i ⟶ S) × (simples C i ⟶ K)) :=
          (homBiprodLinearEquiv C (simples C i) S K).finrank_eq
        _ = _ := Module.finrank_prod
    rw [hdim, Nat.cast_add, add_smul]

end PropertyF.Ground.CentreModular
