module
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-! Basic closure properties of the object property defining the generated
subcategory. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Abelian C]
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
theorem generatedBy_tensorPower (X : C) (k : ℕ) : GeneratedBy X (tensorPower X k) :=
  let f : Fin 1 → C := fun _ => tensorPower X k
  ⟨1, fun _ => k, ⟨{ i := biproduct.ι f 0, r := biproduct.π f 0, retract := by simp [f] }⟩⟩

/-- The tensor unit belongs to the generated closure, including for `X = 0`. -/
theorem generatedBy_unit (X : C) : GeneratedBy X (𝟙_ C) :=
  generatedBy_tensorPower X 0

/-- The generated closure is closed under retracts. -/
theorem generatedBy_retract {X Y Z : C} (hY : GeneratedBy X Y) (h : Retract Z Y) :
    GeneratedBy X Z :=
  let ⟨n, k, ⟨r⟩⟩ := hY
  ⟨n, k, ⟨h.trans r⟩⟩

/-- The generated closure is invariant under isomorphism. -/
theorem generatedBy_of_iso {X Y Z : C} (hY : GeneratedBy X Y) (e : Z ≅ Y) :
    GeneratedBy X Z := generatedBy_retract hY (Retract.ofIso e)

/-- The generating object itself belongs to the generated closure. -/
theorem generatedBy_self (X : C) : GeneratedBy X X :=
  generatedBy_of_iso (generatedBy_tensorPower X 1) (ρ_ X).symm

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

/-- Flatten a dependently indexed finite biproduct. -/
def flattenDependent (a : ℕ) (b : Fin a → ℕ) (f : (i : Fin a) → Fin (b i) → C) :
    (⨁ fun i => ⨁ fun j => f i j) ≅ ⨁ fun p : Σ i, Fin (b i) => f p.1 p.2 :=
  biproduct.isoProduct _ ≪≫
    Pi.mapIso (fun i => biproduct.isoProduct (f i)) ≪≫
    piPiIso (fun i => Fin (b i)) f ≪≫ (biproduct.isoProduct _).symm

/-- Finite biproducts of generated objects are generated. -/
theorem generatedBy_biproduct {X : C} {a : ℕ} (f : Fin a → C)
    (hf : ∀ i, GeneratedBy X (f i)) : GeneratedBy X (⨁ f) := by
  classical
  choose n k hr using hf
  let r : ∀ i, Retract (f i) (⨁ fun j => tensorPower X (k i j)) := fun i => (hr i).some
  let h : Fin a → C := fun i => ⨁ fun j => tensorPower X (k i j)
  let R : Retract (⨁ f) (⨁ h) := {
    i := biproduct.map fun i => (r i).i
    r := biproduct.map fun i => (r i).r
    retract := by
      apply biproduct.hom_ext
      intro i
      simp [Category.assoc, (r i).retract]
  }
  let e : (Σ i, Fin (n i)) ≃ Fin (Fintype.card (Σ i, Fin (n i))) := Fintype.equivFin _
  let k' : Fin (Fintype.card (Σ i, Fin (n i))) → ℕ := fun p => k (e.symm p).1 (e.symm p).2
  let e' : (⨁ h) ≅ ⨁ fun p => tensorPower X (k' p) :=
    flattenDependent a n (fun i j => tensorPower X (k i j)) ≪≫
      biproduct.whiskerEquiv e (fun p => eqToIso (by
        change tensorPower X (k (e.symm (e p)).1 (e.symm (e p)).2) = _
        rw [e.symm_apply_apply]))
  exact ⟨_, k', ⟨R.trans (Retract.ofIso e')⟩⟩

/-- Generated objects are closed under biproducts indexed by any finite type. -/
theorem generatedBy_finiteBiproduct {X : C} {J : Type} [Finite J] (f : J → C)
    (hf : ∀ i, GeneratedBy X (f i)) : GeneratedBy X (⨁ f) := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  let e := Fintype.equivFin J
  let g : Fin (Fintype.card J) → C := fun i => f (e.symm i)
  exact generatedBy_of_iso (generatedBy_biproduct g (fun i => hf (e.symm i)))
    (biproduct.whiskerEquiv e (fun j => eqToIso (by simp [g])))

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
theorem generatedBy_tensor {X Y Z : C} (hY : GeneratedBy X Y) (hZ : GeneratedBy X Z) :
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
/-- Tensor powers of a generated object remain generated. -/
theorem generatedBy_tensorPower_of_generated {X Y : C} (hY : GeneratedBy X Y) :
    ∀ n, GeneratedBy X (tensorPower Y n)
  | 0 => generatedBy_unit X
  | n + 1 => generatedBy_tensor hY
      (generatedBy_tensorPower_of_generated hY n)

/-- Generation is transitive: if Y is generated by X, every object generated
by Y is generated by X. -/
theorem generatedBy_trans {X Y Z : C} (hY : GeneratedBy X Y) (hZ : GeneratedBy Y Z) :
    GeneratedBy X Z :=
  let ⟨_, k, ⟨r⟩⟩ := hZ
  generatedBy_retract
    (generatedBy_biproduct (fun i => tensorPower Y (k i))
      (fun i => generatedBy_tensorPower_of_generated hY (k i))) r

end PropertyF
