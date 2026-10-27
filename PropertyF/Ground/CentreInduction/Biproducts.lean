module
public import PropertyF.Ground.CentreInduction.FiniteSum

/-! Converting binary simple sums to indexed finite biproducts. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
variable {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D] [HasBinaryBiproducts D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A binary sum with a finite biproduct is a biproduct indexed by `Option`. -/
def biprodOptionIso {ι : Type} [Fintype ι] (S : D) (V : ι → D) :
    S ⊞ (⨁ V) ≅ ⨁ (fun o : Option ι => o.elim S V) := by
  classical
  let W : Option ι → D := fun o => o.elim S V
  refine { hom := biprod.desc (biproduct.ι W none)
              (biproduct.desc fun i => biproduct.ι W (some i))
           inv := biproduct.desc (fun o => ?_) 
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · cases o with
    | none => exact biprod.inl
    | some i => exact biproduct.ι V i ≫ biprod.inr
  · apply biprod.hom_ext'
    · simp [Category.assoc]
    · apply biproduct.hom_ext'
      intro i
      simp [Category.assoc]
  · apply biproduct.hom_ext'
    intro o
    cases o with
    | none => simp [W, Category.assoc]
    | some i => simp [W, Category.assoc]

/-- An iterated finite binary sum of simples admits a presentation as a
single finite biproduct of simple objects. -/
theorem finiteSimpleSum_biproduct {X : D} (hX : FiniteSimpleSum D X) :
    ∃ (n : ℕ) (V : Fin n → D), (∀ i, Simple (V i)) ∧ Nonempty (X ≅ ⨁ V) := by
  classical
  induction hX with
  | zero hz =>
    let V : Fin 0 → D := Fin.elim0
    have hzero : IsZero (⨁ V) := (IsZero.iff_id_eq_zero _).mpr (by
      apply biproduct.hom_ext
      intro i
      exact Fin.elim0 i)
    exact ⟨0, V, by intro i; exact Fin.elim0 i, ⟨hz.iso hzero⟩⟩
  | @cons X S K hs hk he ih =>
    obtain ⟨n, V, hv, ⟨e⟩⟩ := ih
    obtain ⟨eX⟩ := he
    let W : Option (Fin n) → D := fun i => i.elim S V
    let W' : Fin (n + 1) → D := fun i => W (finSuccEquiv n i)
    refine ⟨n + 1, W', ?_, ?_⟩
    · intro i
      change Simple (W (finSuccEquiv n i))
      cases h : finSuccEquiv n i with
      | none => exact hs
      | some j => exact hv j
    · let ei : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm
      let er : (⨁ W) ≅ ⨁ W' := biproduct.whiskerEquiv ei (fun i => eqToIso (by simp [W', ei]))
      exact ⟨eX ≪≫ biprod.mapIso (Iso.refl S) e ≪≫ biprodOptionIso S V ≪≫ er⟩

end PropertyF.Ground.CentreInduction
