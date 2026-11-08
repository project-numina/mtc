module
public import MTC.Braided.Cabling.PureSumPositiveState
public import MTC.Braided.Cabling.ClosureInsertionCompare
public import MTC.Braided.Cabling.ClosureColoredContext

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Prefixing arbitrary original strands sends an element of a braid image
to the larger braid image, via the canonical join. -/
theorem braidImage_prefix_mem (X : C) (n p : ℕ)
    (a : Aut (tensorPower X (n + 2))) (ha : a ∈ braidImage X n) :
    (joinPowerIso X p (n + 2) ≪≫
      powerIndexIso X (by rw [strandSum_eq_add]; omega :
        strandSum p (n + 2) = (n + p) + 2)).conjAut
      ((tensorLeft (tensorPower X p)).mapAut (tensorPower X (n + 2)) a) ∈
        braidImage X (n + p) := by
  obtain ⟨w, hw⟩ := braidWordAction_surjective X n ⟨a, ha⟩
  have hw' := congrArg Subtype.val hw
  change (braidWordAction X n w).val = a at hw'
  rw [← hw', joinPrefix_braidWord]
  exact (braidWordAction X (n + p) _).property

set_option backward.isDefEq.respectTransparency false in
/-- Flattening a colored tuple starts by flattening its tail and joining the
first block. -/
theorem coloredFlatten_head_heq (X : C) (n : ℕ) (k : Fin (n + 1) → ℕ) :
    coloredTensorPowersFlatten X (n + 1) k ≍
      (Iso.refl (tensorPower X (k 0)) ⊗ᵢ
        coloredTensorPowersFlatten X n (fun j => k j.succ)) ≪≫
        joinPowerIso X (k 0) (∑ j : Fin n, k j.succ) := by
  have h := coloredTensorPowersFlatten_heq X (n + 1) k
  have ht := coloredTensorPowersFlatten_heq X n (fun j => k j.succ)
  apply h.trans
  simp only [heterogeneousPowerFlatten]
  congr 2
  all_goals try exact ht.symm
  all_goals try simp [heterogeneousStrandCount_eq_sum, heterogeneousPowerTensor, ← coloredTensor_powers_eq, strandSum_eq_add, Fin.sum_univ_succ]

/-- Flattening an unchanged prefix commutes with a crossing in the tail. -/
theorem prefix_crossing_cancel {A U V T S P Q : C}
    (f : U ≅ T) (g : U ≅ V) (h : V ≅ S)
    (j : A ⊗ T ≅ P) (k : A ⊗ S ≅ Q) :
    ((Iso.refl A ⊗ᵢ f) ≪≫ j).symm ≪≫ (Iso.refl A ⊗ᵢ g) ≪≫
        ((Iso.refl A ⊗ᵢ h) ≪≫ k) =
      j.symm ≪≫ (Iso.refl A ⊗ᵢ (f.symm ≪≫ g ≪≫ h)) ≪≫ k := by
  apply Iso.ext
  simp [Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv,
    tensorHom_comp_tensorHom, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A non-first colored generator is the flattened tail generator with the
first tensor-power block prefixed. -/
theorem coloredGenerator_succ_flatten_heq (X : C) (n : ℕ)
    (i : Fin (n + 1)) (k : Fin (n + 3) → ℕ) :
    ((coloredTensorPowersFlatten X (n + 3) k).symm ≪≫
      coloredGenerator (n + 1) i.succ (fun j => tensorPower X (k j)) ≪≫
      coloredTensorPowersFlatten X (n + 3)
        (fun j => k (coloredSwap (n + 1) i.succ j))) ≍
    ((joinPowerIso X (k 0) (∑ j : Fin (n + 2), k j.succ)).symm ≪≫
      (Iso.refl (tensorPower X (k 0)) ⊗ᵢ
        ((coloredTensorPowersFlatten X (n + 2) (fun j => k j.succ)).symm ≪≫
          coloredGenerator n i (fun j => tensorPower X (k j.succ)) ≪≫
          coloredTensorPowersFlatten X (n + 2)
            (fun j => k (coloredSwap n i j).succ))) ≪≫
      joinPowerIso X (k 0) (∑ j : Fin (n + 2), k (coloredSwap n i j).succ)) := by
  have hs := coloredFlatten_head_heq X (n + 2) k
  have ht := coloredFlatten_head_heq X (n + 2)
    (fun j => k (coloredSwap (n + 1) i.succ j))
  have hc := prefix_crossing_cancel
    (coloredTensorPowersFlatten X (n + 2) (fun j => k j.succ))
    (coloredGenerator n i (fun j => tensorPower X (k j.succ)))
    (coloredTensorPowersFlatten X (n + 2) (fun j => k (coloredSwap n i j).succ))
    (joinPowerIso X (k 0) (∑ j : Fin (n + 2), k j.succ))
    (joinPowerIso X (k 0) (∑ j : Fin (n + 2), k (coloredSwap n i j).succ))
  apply HEq.trans _ (heq_of_eq hc)
  simp only [coloredGenerator, coloredSwap, Fin.cases_succ, Fin.cases_zero] at ht ⊢
  congr 2
  all_goals try exact hs
  all_goals try exact ht
  all_goals try rfl
  all_goals try simp [coloredSwap, Fin.cases_succ, Fin.cases_zero, Fin.sum_univ_succ, strandSum_eq_add]

end MTC.Braided.Cabling
end
