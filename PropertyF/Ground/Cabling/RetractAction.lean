module
public import PropertyF.Ground.Cabling.Blocks
open CategoryTheory
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] {G : Type*} [Group G]

/-- Restrict an action which preserves a retract to an action on that retract. -/
def retractAction {Y Z : C} (r : Retract Y Z) (ρ : G →* Aut Z)
    (h : ∀ g, r.i ≫ (ρ g).asIso.hom = (r.i ≫ (ρ g).asIso.hom ≫ r.r) ≫ r.i)
    (g : G) : Aut Y := Aut.of {
  hom := r.i ≫ (ρ g).asIso.hom ≫ r.r
  inv := r.i ≫ (ρ g).asIso.inv ≫ r.r
  hom_inv_id := by
    calc
      _ = (r.i ≫ (ρ g).asIso.hom) ≫ (ρ g).asIso.inv ≫ r.r := by rw [h g]; simp [Category.assoc]
      _ = _ := by simp
  inv_hom_id := by
    have hg : (ρ g).asIso.inv = (ρ g⁻¹).asIso.hom := by simp
    rw [hg]
    calc
      _ = (r.i ≫ (ρ g⁻¹).asIso.hom) ≫ (ρ g).asIso.hom ≫ r.r := by rw [h g⁻¹]; simp [Category.assoc]
      _ = _ := by simp
}

/-- The restrictions define a group homomorphism. -/
def retractActionHom {Y Z : C} (r : Retract Y Z) (ρ : G →* Aut Z)
    (h : ∀ g, r.i ≫ (ρ g).asIso.hom = (r.i ≫ (ρ g).asIso.hom ≫ r.r) ≫ r.i) :
    G →* Aut Y where
  toFun g := retractAction r ρ h g
  map_one' := by ext; simp [retractAction]
  map_mul' x y := by
    ext
    change r.i ≫ (ρ (x * y)).asIso.hom ≫ r.r =
      (r.i ≫ (ρ y).asIso.hom ≫ r.r) ≫ (r.i ≫ (ρ x).asIso.hom ≫ r.r)
    simp only [map_mul, Aut.mul_asIso, Iso.trans_hom]
    simpa [Category.assoc] using congrArg (fun z => z ≫ (ρ x).asIso.hom ≫ r.r) (h y)

/-- An element acting trivially on the ambient object acts trivially on the retract. -/
theorem retractAction_ker_le {Y Z : C} (r : Retract Y Z) (ρ : G →* Aut Z)
    (h : ∀ g, r.i ≫ (ρ g).asIso.hom = (r.i ≫ (ρ g).asIso.hom ≫ r.r) ≫ r.i) :
    ρ.ker ≤ (retractActionHom r ρ h).ker := by
  intro g hg
  change ρ g = 1 at hg
  change retractActionHom r ρ h g = 1
  ext
  change r.i ≫ (ρ g).asIso.hom ≫ r.r = 𝟙 Y
  rw [hg]
  simp
end PropertyF
