module
public import PropertyF.Ground.Cabling.CableAppend
public import PropertyF.Ground.Cabling.BlockSwap
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Insert a block of left spectator strands, at any initial strand count. -/
def prefixPowerIso (X : C) (m : ℕ) : ∀ k, tensorPower X k ⊗ tensorPower X m ≅ tensorPower X (m+k)
  | 0 => λ_ (tensorPower X m)
  | k+1 => (α_ X (tensorPower X k) (tensorPower X m)) ≪≫
      (Iso.refl X ⊗ᵢ prefixPowerIso X m k)

/-- Iterated left insertion for any initial strand count. -/
def addLeftAutAllIter (X : C) (m : ℕ) : ∀ k, Aut (tensorPower X m) →* Aut (tensorPower X (m+k))
  | 0 => MonoidHom.id _
  | k+1 => (addLeftAutAll X (m+k)).comp (addLeftAutAllIter X m k)

theorem addLeftAutAllIter_mem (X : C) (m : ℕ) (a : Aut (tensorPower X m))
    (ha : a ∈ braidImageAllSubgroup X m) : ∀ k,
      addLeftAutAllIter X m k a ∈ braidImageAllSubgroup X (m+k)
  | 0 => ha
  | k+1 => addLeftAutAll_mem X (m+k) _ (addLeftAutAllIter_mem X m a ha k)

/-- Repeated left insertion is conjugation by the left-prefix comparison. -/
theorem addLeftAutAllIter_hom (X : C) (m k : ℕ) (a : Aut (tensorPower X m)) :
    (addLeftAutAllIter X m k a).asIso.hom =
      (prefixPowerIso X m k).inv ≫ (tensorPower X k ◁ a.asIso.hom) ≫
        (prefixPowerIso X m k).hom := by
  induction k with
  | zero =>
    change a.asIso.hom = (λ_ (tensorPower X m)).inv ≫ ((𝟙_ C) ◁ a.asIso.hom) ≫
      (λ_ (tensorPower X m)).hom
    monoidal
  | succ k ih =>
    change X ◁ (addLeftAutAllIter X m k a).asIso.hom = _
    rw [ih]
    dsimp only [prefixPowerIso, Iso.trans_hom, Iso.trans_inv, tensorIso_hom,
      tensorIso_inv, Iso.refl_hom, Iso.refl_inv, id_tensorHom, whiskerLeft_comp,
      Category.assoc, tensorPower]
    monoidal
end PropertyF
