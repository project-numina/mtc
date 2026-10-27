module
public import PropertyF.Ground.Cabling.BlockOne
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Add a left identity strand for an arbitrary strand count. -/
def addLeftAutAll (X : C) (m : ℕ) : Aut (tensorPower X m) →* Aut (tensorPower X (m+1)) :=
  (tensorLeft X).mapAut (tensorPower X m)

/-- Left identity-strand insertion preserves the uniform braid subgroup,
including the zero- and one-strand cases. -/
theorem addLeftAutAll_mem (X : C) : ∀ m (a : Aut (tensorPower X m)),
    a ∈ braidImageAllSubgroup X m → addLeftAutAll X m a ∈ braidImageAllSubgroup X (m+1)
  | 0, a, ha => by
    have h : a = 1 := by simpa [braidImageAllSubgroup] using ha
    subst a
    rw [map_one]
    exact Subgroup.one_mem _
  | 1, a, ha => by
    have h : a = 1 := by simpa [braidImageAllSubgroup] using ha
    subst a
    rw [map_one]
    exact Subgroup.one_mem _
  | m+2, a, ha => by
    let b : braidImage X m := ⟨a, ha⟩
    have hb := (addLeftStrand X m b).property
    change addLeftAutAll X (m+2) a ∈ braidImage X (m+1)
    convert hb using 1
    apply Aut.ext
    apply Iso.ext
    rfl

/-- Add a right identity strand for an arbitrary strand count. -/
def addRightAutAll (X : C) (m : ℕ) : Aut (tensorPower X m) →* Aut (tensorPower X (m+1)) :=
  (appendIso X m).conjAut.toMonoidHom.comp ((tensorRight X).mapAut (tensorPower X m))

/-- Right identity-strand insertion preserves the uniform braid subgroup. -/
theorem addRightAutAll_mem (X : C) : ∀ m (a : Aut (tensorPower X m)),
    a ∈ braidImageAllSubgroup X m → addRightAutAll X m a ∈ braidImageAllSubgroup X (m+1)
  | 0, a, ha => by
    have h : a = 1 := by simpa [braidImageAllSubgroup] using ha
    subst a
    simp [addRightAutAll]
  | 1, a, ha => by
    have h : a = 1 := by simpa [braidImageAllSubgroup] using ha
    subst a
    simp [addRightAutAll, braidImageAllSubgroup]
  | m+2, a, ha => by
    let b : braidImage X m := ⟨a, ha⟩
    have hb := (addRightStrand X m b).property
    change addRightAutAll X (m+2) a ∈ braidImage X (m+1)
    convert hb using 1
    apply Aut.ext
    apply Iso.ext
    rfl
/-- Iterated right insertion for any starting strand count. -/
def addRightAutAllIter (X : C) (m : ℕ) : ∀ k, Aut (tensorPower X m) →* Aut (tensorPower X (m+k))
  | 0 => MonoidHom.id _
  | k+1 => (addRightAutAll X (m+k)).comp (addRightAutAllIter X m k)

/-- Iterated right insertion preserves all braid images. -/
theorem addRightAutAllIter_mem (X : C) (m : ℕ) (a : Aut (tensorPower X m))
    (ha : a ∈ braidImageAllSubgroup X m) : ∀ k,
      addRightAutAllIter X m k a ∈ braidImageAllSubgroup X (m+k)
  | 0 => ha
  | k+1 => addRightAutAll_mem X (m+k) _ (addRightAutAllIter_mem X m a ha k)
end PropertyF
