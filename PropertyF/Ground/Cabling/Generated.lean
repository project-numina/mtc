module
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Basic closure properties of the object property defining the generated
subcategory. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [Abelian C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Tensoring two powers gives the corresponding combined power. -/
def tensorPowerTensorIso (X : C) : ∀ n m : ℕ,
    tensorPower X n ⊗ tensorPower X m ≅ tensorPower X (n + m)
  | 0, m => by simpa [tensorPower] using (λ_ (tensorPower X m))
  | n + 1, m => by
      simpa only [Nat.succ_add, tensorPower] using
        ((α_ X (tensorPower X n) (tensorPower X m)) ≪≫
          (Iso.refl X ⊗ᵢ tensorPowerTensorIso X n m))

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

/-- Flatten an iterated finite biproduct. -/
def flattenBiproduct (a b : ℕ) (f : Fin a → Fin b → C) :
    (⨁ fun i => ⨁ fun j => f i j) ≅ ⨁ fun p : Fin a × Fin b => f p.1 p.2 :=
  biproduct.isoProduct _ ≪≫
    Pi.mapIso (fun i => biproduct.isoProduct (f i)) ≪≫
    piPiIso (fun _ : Fin a => Fin b) f ≪≫
    Pi.whiskerEquiv (f := fun p : Σ _ : Fin a, Fin b => f p.1 p.2)
      (g := fun p : Fin a × Fin b => f p.1 p.2)
      (Equiv.sigmaEquivProd (Fin a) (Fin b)) (fun _ => Iso.refl _) ≪≫
    (biproduct.isoProduct _).symm

variable [MonoidalPreadditive C]
/-- Distribute tensor product over two finite biproducts. -/
def tensorBiproduct (a b : ℕ) (f : Fin a → C) (g : Fin b → C) :
    (⨁ f) ⊗ (⨁ g) ≅ ⨁ fun p : Fin a × Fin b => f p.1 ⊗ g p.2 :=
  rightDistributor f (⨁ g) ≪≫
    biproduct.mapIso (fun i => leftDistributor (f i) g) ≪≫
    flattenBiproduct a b (fun i j => f i ⊗ g j)
/-- Tensor products of finite sums of powers are finite sums of powers. -/
def sumPowersTensorIso (X : C) (a b : ℕ) (k : Fin a → ℕ) (l : Fin b → ℕ) :
    (⨁ fun i => tensorPower X (k i)) ⊗ (⨁ fun j => tensorPower X (l j)) ≅
    ⨁ fun p : Fin (a * b) => tensorPower X
      (k (finProdFinEquiv.symm p).1 + l (finProdFinEquiv.symm p).2) :=
  tensorBiproduct a b (fun i => tensorPower X (k i)) (fun j => tensorPower X (l j)) ≪≫
    biproduct.whiskerEquiv finProdFinEquiv (fun p => by
      simpa using (tensorPowerTensorIso X (k p.1) (l p.2)).symm)

/-- The generated objects are closed under tensor product. -/
theorem generatedBy_tensor (X Y Z : C) (hY : GeneratedBy X Y) (hZ : GeneratedBy X Z) :
    GeneratedBy X (Y ⊗ Z) := by
  obtain ⟨a, k, ⟨rY⟩⟩ := hY
  obtain ⟨b, l, ⟨rZ⟩⟩ := hZ
  let r : Retract (Y ⊗ Z) ((⨁ fun i => tensorPower X (k i)) ⊗
      (⨁ fun j => tensorPower X (l j))) :=
    { i := rY.i ⊗ₘ rZ.i
      r := rY.r ⊗ₘ rZ.r
      retract := by rw [tensorHom_comp_tensorHom, rY.retract, rZ.retract, id_tensorHom_id] }
  exact ⟨a * b, fun p => k (finProdFinEquiv.symm p).1 + l (finProdFinEquiv.symm p).2,
    ⟨r.trans (Retract.ofIso (sumPowersTensorIso X a b k l))⟩⟩
/-- The generated full subcategory inherits a braided monoidal structure. -/
instance generatedBy_isMonoidal (X : C) :
    ObjectProperty.IsMonoidal (GeneratedBy X) where
  prop_tensor _ _ hY hZ := generatedBy_tensor X _ _ hY hZ

/-- The generated inclusion inherits Mathlib's braided functor structure. -/
@[instance_reducible] def generatedInclusionBraided (X : C) : (generatedInclusion X).Braided := inferInstance

end PropertyF
