module
public import PropertyF.Ground.Cabling.Generated
public import Mathlib.CategoryTheory.Endomorphism
open CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {G : Type*} [Group G]

/-- Restrict an action preserving the individual summands. -/
def blockRestriction {ι : Type} [Fintype ι] (f : ι → C)
    (ρ : G →* Aut (⨁ f))
    (h : ∀ g i, biproduct.ι f i ≫ (ρ g).asIso.hom =
      (biproduct.ι f i ≫ (ρ g).asIso.hom ≫ biproduct.π f i) ≫ biproduct.ι f i)
    (g : G) (i : ι) : Aut (f i) := Aut.of {
      hom := biproduct.ι f i ≫ (ρ g).asIso.hom ≫ biproduct.π f i
      inv := biproduct.ι f i ≫ (ρ g).asIso.inv ≫ biproduct.π f i
      hom_inv_id := by
        calc
          _ = (biproduct.ι f i ≫ (ρ g).asIso.hom) ≫ (ρ g).asIso.inv ≫ biproduct.π f i := by rw [h g i]; simp [Category.assoc]
          _ = _ := by simp
      inv_hom_id := by
        have hg : (ρ g).asIso.inv = (ρ g⁻¹).asIso.hom := by simp
        rw [hg]
        calc
          _ = (biproduct.ι f i ≫ (ρ g⁻¹).asIso.hom) ≫ (ρ g).asIso.hom ≫ biproduct.π f i := by rw [h g⁻¹ i]; simp [Category.assoc]
          _ = _ := by simp
    }

/-- The summand restrictions form a group homomorphism. -/
def blockRestrictionHom {ι : Type} [Fintype ι] (f : ι → C)
    (ρ : G →* Aut (⨁ f))
    (h : ∀ g i, biproduct.ι f i ≫ (ρ g).asIso.hom =
      (biproduct.ι f i ≫ (ρ g).asIso.hom ≫ biproduct.π f i) ≫ biproduct.ι f i) :
    G →* (∀ i, Aut (f i)) where
  toFun g i := blockRestriction f ρ h g i
  map_one' := by ext i; simp [blockRestriction]
  map_mul' x y := by
    ext i
    change biproduct.ι f i ≫ (ρ (x * y)).asIso.hom ≫ biproduct.π f i =
      (biproduct.ι f i ≫ (ρ y).asIso.hom ≫ biproduct.π f i) ≫
        (biproduct.ι f i ≫ (ρ x).asIso.hom ≫ biproduct.π f i)
    simp only [map_mul, Aut.mul_asIso, Iso.trans_hom]
    simpa [Category.assoc] using congrArg
      (fun z => z ≫ (ρ x).asIso.hom ≫ biproduct.π f i) (h y i)

/-- Diagonal block actions jointly detect the action on the biproduct. -/
theorem blockRestriction_ker_le {ι : Type} [Fintype ι] (f : ι → C)
    (ρ : G →* Aut (⨁ f))
    (h : ∀ g i, biproduct.ι f i ≫ (ρ g).asIso.hom =
      (biproduct.ι f i ≫ (ρ g).asIso.hom ≫ biproduct.π f i) ≫ biproduct.ι f i) :
    (blockRestrictionHom f ρ h).ker ≤ ρ.ker := by
  intro g hg
  change blockRestrictionHom f ρ h g = 1 at hg
  change ρ g = 1
  apply Aut.ext
  apply Iso.ext
  apply biproduct.hom_ext'
  intro i
  rw [h g i]
  have hi := congrArg (fun x : ∀ i, Aut (f i) => (x i).asIso.hom) hg
  change biproduct.ι f i ≫ (ρ g).asIso.hom ≫ biproduct.π f i = 𝟙 (f i) at hi
  rw [hi]
  simp
end PropertyF
