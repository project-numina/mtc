module
public import MTC.Braided.Cabling.ClosureFirstBlock

/-! Left insertion and conjugation of genuine categorical braid actions. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Repeated left insertion is left whiskering by a tensor power, transported
through the canonical insertion isomorphism. -/
theorem addLeftStrands_asHom (X : C) (n : ℕ) : ∀ (k : ℕ) (a : braidImage X n),
    ((Trace.addLeftStrands X n k a).val).asIso.hom =
      (Trace.insertLeftPowerIso X n k).inv ≫ (tensorPower X k ◁ a.val.asIso.hom) ≫
        (Trace.insertLeftPowerIso X n k).hom
  | 0, a => by simp [Trace.addLeftStrands, Trace.insertLeftPowerIso, Trace.braidTensorPower, tensorPower]
  | k+1, a => by
    change X ◁ ((Trace.addLeftStrands X n k a).val).asIso.hom = _
    rw [addLeftStrands_asHom X n k a]
    simp only [Trace.insertLeftPowerIso, Iso.trans_hom, Iso.trans_inv, tensorIso_hom,
      tensorIso_inv, Iso.refl_hom, Iso.refl_inv, id_tensorHom, whiskerLeft_comp,
      Category.assoc, tensorPower]
    monoidal

/-- Conjugating a left-padded operator by the insertion isomorphism gives the
actual iterated left-strand image. -/
theorem leftInsertion_conjAut (X : C) (n t : ℕ) (a : braidImage X n) :
    (Trace.insertLeftPowerIso X n t).conjAut
      ((tensorLeft (tensorPower X t)).mapAut (tensorPower X (n+2)) a.val) =
        (Trace.addLeftStrands X n t a).val := by
  apply Aut.ext
  apply Iso.ext
  change (Trace.insertLeftPowerIso X n t).inv ≫
      (tensorPower X t ◁ a.val.asIso.hom) ≫ (Trace.insertLeftPowerIso X n t).hom = _
  exact (addLeftStrands_asHom X n t a).symm

/-- Recover a local operator and its identity prefix from its inserted image. -/
theorem leftInsertion_inverse_conjAut (X : C) (n t : ℕ) (a : braidImage X n) :
    (Trace.insertLeftPowerIso X n t).symm.conjAut (Trace.addLeftStrands X n t a).val =
      (tensorLeft (tensorPower X t)).mapAut (tensorPower X (n+2)) a.val := by
  rw [← leftInsertion_conjAut, conjAut_symm_cancel]

omit [BraidedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Tensor isomorphisms transport a left-padded operator on its right factor. -/
theorem tensor_conj_left {A B D E : C} (e : A ≅ B) (f : D ≅ E) (a : Aut D) :
    (e ⊗ᵢ f).conjAut ((tensorLeft A).mapAut D a) =
      (tensorLeft B).mapAut E (f.conjAut a) := by
  apply Aut.ext
  apply Iso.ext
  change (e ⊗ᵢ f).inv ≫ (A ◁ a.asIso.hom) ≫ (e ⊗ᵢ f).hom =
    B ◁ (f.inv ≫ a.asIso.hom ≫ f.hom)
  simp only [tensorIso_inv, tensorIso_hom, tensorHom_def, whisker_exchange_assoc,
    whiskerLeft_comp, Category.assoc]
  simp

end MTC.Braided
