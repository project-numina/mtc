module
public import PropertyF.Ground.Cabling.BlockWords
public import PropertyF.Ground.Cabling.CablingDiagram
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C]
attribute [local instance] Abelian.hasFiniteBiproducts

def cableHom (X : C) (a b : ℕ) (f : tensorPower X a ⟶ tensorPower X b) : Prop :=
  ∃ (h : a = b) (g : braidImageAllSubgroup X a),
    f = g.val.asIso.hom ≫ eqToHom (congrArg (tensorPower X) h)

theorem cableHom_comp (X : C) {a b c : ℕ}
    {f : tensorPower X a ⟶ tensorPower X b} {g : tensorPower X b ⟶ tensorPower X c}
    (hf : cableHom X a b f) (hg : cableHom X b c g) : cableHom X a c (f ≫ g) := by
  obtain ⟨h, p, rfl⟩ := hf
  obtain ⟨h', q, rfl⟩ := hg
  subst b
  subst c
  refine ⟨rfl, q*p, ?_⟩
  simp [Aut.mul_asIso, Category.assoc]

theorem cableHom_inv (X : C) {a b : ℕ} (e : tensorPower X a ≅ tensorPower X b)
    (he : cableHom X a b e.hom) : cableHom X b a e.inv := by
  obtain ⟨h, p, he⟩ := he
  subst b
  refine ⟨rfl, p⁻¹, ?_⟩
  simp only [eqToHom_refl, Category.comp_id] at he ⊢
  have heq : e = p.val.asIso := Iso.ext he
  rw [heq]
  rfl

def cableClass {I : Type} (X : C) (len : I → ℕ) : BlockMorphismClass (fun i => tensorPower X (len i)) where
  holds := fun i j f => cableHom X (len i) (len j) f
  id_mem := by
    intro i
    exact ⟨rfl, 1, by simp⟩
  comp_mem := by intro i j k f g hf hg; exact cableHom_comp X hf hg
  inv_mem := by intro i j e he; exact cableHom_inv X e he
/-- A same-length cabled map identifies its automorphism with an actual
braid-image element. -/
theorem cableHom_aut_mem (X : C) (n : ℕ) (a : Aut (tensorPower X n))
    (h : cableHom X n n a.asIso.hom) : a ∈ braidImageAllSubgroup X n := by
  obtain ⟨eqn, b, hb⟩ := h
  have heq : eqn = rfl := Subsingleton.elim _ _
  rw [heq] at hb
  simp only [eqToHom_refl, Category.comp_id] at hb
  have ha : a = b.val := by
    apply Aut.ext
    apply Iso.ext
    exact hb
  rw [ha]
  exact b.property

/-- Local braid-image membership for the block crossing of each generator
implies braid-image membership for every pure-word block. -/
theorem powerSum_pureBlock_mem_of_generators (X : C) (k : Fin count → ℕ) (n : ℕ)
    (hgen : ∀ i, permutesBlocks (powerSumBlock X k n)
      (sumPowerWordAction X k n (FreeGroup.of i))
      (((tuplePermutation (Fin count) (n + 2)).comp (strandPermutation n)) (FreeGroup.of i)))
    (hloc : ∀ (j : Fin (n+1)) (t : Fin (n+2) → Fin count),
      cableHom X (∑ i, k (t i))
        (∑ i, k ((((tuplePermutation (Fin count) (n+2)).comp (strandPermutation n)) (FreeGroup.of j)) t i))
        (permutedBlockMap (powerSumBlock X k n) (sumPowerWordAction X k n (FreeGroup.of j))
          (((tuplePermutation (Fin count) (n+2)).comp (strandPermutation n)) (FreeGroup.of j)) t)) :
    ∀ (w : pureWords n) (t : Fin (n+2) → Fin count),
      powerSumPureBlockAction X k n hgen w t ∈ braidImageAllSubgroup X (∑ i, k (t i)) := by
  intro w t
  let f := powerSumBlock X k n
  let ρ := sumPowerWordAction X k n
  let π := (tuplePermutation (Fin count) (n+2)).comp (strandPermutation n)
  let P := cableClass X (fun t : Fin (n+2) → Fin count => ∑ i, k (t i))
  have hall := braidWords_blockMaps_mem f n ρ π hgen P hloc w.val t
  have hp : π w.val = 1 := pureWord_fixes_tuples (Fin count) n w
  rw [hp] at hall
  have hmap : cableHom X (∑ i, k (t i)) (∑ i, k (t i))
      ((powerSumPureBlockAction X k n hgen w t).asIso.hom) := by
    simpa [P, cableClass, f, ρ, permutedBlockMap, powerSumPureBlockAction,
      pureTupleBlockAction, blockRestrictionHom, blockRestriction] using hall
  exact cableHom_aut_mem X _ _ hmap
end PropertyF
