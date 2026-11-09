module
public import MTC.Braided.Cabling.PureSumInverse
public import MTC.Braided.Cabling.ClosureColoredWords

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Swapping a fixed-total state twice restores the original state. -/
theorem coloredPowerSwap_involutive {n N : ℕ} (i : Fin (n + 1))
    (s : ColoredPowerState n N) :
    coloredPowerSwap n N i (coloredPowerSwap n N i s) = s := by
  apply Subtype.ext
  funext j
  exact congrArg s.val (coloredSwap_involutive n i j)

omit [Abelian C] in
set_option backward.isDefEq.respectTransparency false in
/-- The negative crossing is the inverse positive crossing after transporting
its doubly swapped endpoint. -/
theorem coloredPower_negative_crossing_eq (X : C) {n N : ℕ}
    (s : ColoredPowerState n N) (i : Fin (n + 1)) :
    coloredGeneratorInverse n i (fun j => tensorPower X (s.val j)) =
      (coloredGenerator n i (fun j => tensorPower X ((coloredPowerSwap n N i s).val j)) ≪≫
        eqToIso (congrArg (fun q : ColoredPowerState n N =>
          coloredTensor (n + 2) (fun j => tensorPower X (q.val j)))
            (coloredPowerSwap_involutive i s))).symm := by
  have h := coloredGeneratorInverse_heq_symm n i (fun j => tensorPower X (s.val j))
  have htransport : ∀ {A B D : C} (f : A ≅ B) (p : B = D),
      HEq (f ≪≫ eqToIso p).symm f.symm := by
    intro A B D f p
    cases p
    simp
  apply eq_of_heq
  exact h.trans (htransport _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- In fixed-total coordinates, the negative crossing is the inverse of the
positive crossing at the swapped state. -/
theorem coloredPower_negative_eq_inverse (X : C) (n N : ℕ)
    (s : ColoredPowerState n N) (i : Fin (n + 1)) :
    Aut.of ((coloredPowerStateFlatten X n N s).symm ≪≫
      coloredLetter n i false (fun j => tensorPower X (s.val j)) ≪≫
      coloredPowerStateFlatten X n N (coloredPowerSwap n N i s)) =
    (Aut.of ((coloredPowerStateFlatten X n N (coloredPowerSwap n N i s)).symm ≪≫
      coloredLetter n i true (fun j => tensorPower X ((coloredPowerSwap n N i s).val j)) ≪≫
      coloredPowerStateFlatten X n N (coloredPowerSwap n N i (coloredPowerSwap n N i s))))⁻¹ := by
  let t := coloredPowerSwap n N i s
  have hs : coloredPowerSwap n N i t = s := coloredPowerSwap_involutive i s
  have hclose := coloredPower_negative_crossing_eq X s i
  apply Aut.ext
  apply Iso.ext
  simp only [Aut.inv_asIso, coloredLetter, Bool.false_eq_true, ↓reduceIte,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc]
  have hh := congrArg Iso.hom hclose
  have hf := eqToHom_iso_inv_naturality (coloredPowerStateFlatten X n N) hs.symm
  simp only [eqToHom_refl, Category.id_comp] at hf
  simp only [Iso.symm_hom, Iso.trans_inv] at hh
  rw [hh]
  rw [← hf]
  simp [Category.assoc, t]

/-- Positive fixed-total generator membership implies membership for both signs. -/
theorem coloredPower_letters_mem_of_positive (X : C) {n : ℕ} (N : ℕ)
    (G : Subgroup (Aut (tensorPower X N)))
    (h : ∀ (s : ColoredPowerState n N) (i : Fin (n + 1)),
      Aut.of ((coloredPowerStateFlatten X n N s).symm ≪≫
        coloredLetter n i true (fun j => tensorPower X (s.val j)) ≪≫
        coloredPowerStateFlatten X n N (coloredPowerSwap n N i s)) ∈ G) :
    ∀ (s : ColoredPowerState n N) (a : Fin (n + 1) × Bool),
      Aut.of ((coloredPowerStateFlatten X n N s).symm ≪≫
        coloredLetter n a.1 a.2 (fun j => tensorPower X (s.val j)) ≪≫
        coloredPowerStateFlatten X n N (coloredPowerSwap n N a.1 s)) ∈ G := by
  intro s ⟨i, b⟩
  cases b with
  | false =>
    rw [coloredPower_negative_eq_inverse]
    exact G.inv_mem (h (coloredPowerSwap n N i s) i)
  | true => exact h s i

end MTC.Braided.Cabling
end
