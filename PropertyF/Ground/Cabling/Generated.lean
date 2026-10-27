module
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-! Basic closure properties of the object property defining the generated
subcategory. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [Abelian C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Any tensor power is in the generated closure. -/
theorem generatedBy_tensorPower (X : C) (k : ℕ) : GeneratedBy X (tensorPower X k) := by
  let f : Fin 1 → C := fun _ => tensorPower X k
  refine ⟨1, fun _ => k, ⟨{ i := biproduct.ι f 0, r := biproduct.π f 0, retract := ?_ }⟩⟩
  simp [f]

/-- The tensor unit belongs to the generated closure, including for `X = 0`. -/
theorem generatedBy_unit (X : C) : GeneratedBy X (𝟙_ C) :=
  generatedBy_tensorPower X 0

/-- The generated closure is closed under retracts. -/
theorem generatedBy_retract {X Y Z : C} (hY : GeneratedBy X Y) (h : Retract Z Y) :
    GeneratedBy X Z := by
  obtain ⟨n, k, ⟨r⟩⟩ := hY
  exact ⟨n, k, ⟨h.trans r⟩⟩

/-- The generated closure is invariant under isomorphism. -/
theorem generatedBy_of_iso {X Y Z : C} (hY : GeneratedBy X Y) (e : Z ≅ Y) :
    GeneratedBy X Z := generatedBy_retract hY (Retract.ofIso e)

/-- The generating object itself belongs to the generated closure. -/
theorem generatedBy_self (X : C) : GeneratedBy X X :=
  generatedBy_of_iso (generatedBy_tensorPower X 1) (ρ_ X).symm

/-- The full subcategory of generated objects, with its inherited category. -/
abbrev generatedCategory (X : C) := (show ObjectProperty C from GeneratedBy X).FullSubcategory

/-- The canonical full and faithful inclusion. -/
abbrev generatedInclusion (X : C) : generatedCategory X ⥤ C :=
  (show ObjectProperty C from GeneratedBy X).ι

/-- The inclusion has precisely the generated objects as its essential image. -/
theorem generatedInclusion_essentialImage (X Y : C) :
    GeneratedBy X Y ↔ ∃ Z : generatedCategory X, Nonempty ((generatedInclusion X).obj Z ≅ Y) := by
  constructor
  · intro h
    exact ⟨⟨Y, h⟩, ⟨Iso.refl Y⟩⟩
  · rintro ⟨Z, ⟨e⟩⟩
    exact generatedBy_of_iso Z.property e.symm

/-- The full subcategory on the generated objects contains the unit. -/
instance generatedBy_containsUnit (X : C) : ObjectProperty.ContainsUnit (GeneratedBy X) where
  prop_unit := generatedBy_unit X

end PropertyF
