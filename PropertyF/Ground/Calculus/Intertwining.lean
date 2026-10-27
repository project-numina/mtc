module
public import PropertyF.Ground.Calculus.UnitaryBlocks
public import PropertyF.Ground.Calculus.StarSpan

/-! Compatibility of unitary block realizations under maps of group images. -/

@[expose] public noncomputable section
namespace PropertyF.Ground.Calculus

variable {G H A B : Type*} [Group G] [Group H]
  [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

/-- The group image spans any algebra-equivalent block presentation. -/
theorem presented_group_span (ρ : G →* A) {n : ℕ} {d : Fin n → ℕ}
    (e : groupImageAlgebra ρ ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    Submodule.span ℂ (Set.range (e.toMonoidHom.comp (groupInImage ρ))) = ⊤ := by
  classical
  change Submodule.span ℂ (Set.range (fun g => e (groupInImage ρ g))) = ⊤
  rw [Set.range_comp']
  change Submodule.span ℂ (e.toLinearEquiv.toLinearMap '' Set.range (groupInImage ρ)) = ⊤
  rw [← Submodule.map_span, groupInImage_span, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.surjective

/-- A unitary block representation sends group inversion to conjugate transpose. -/
theorem unitary_block_star_inv {n : ℕ} {d : Fin n → ℕ}
    (ρ : G →* ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hu : ∀ g i, ρ g i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) (g : G) :
    star (ρ g) = ρ g⁻¹ := by
  apply funext
  intro i
  change star (ρ g i) = ρ g⁻¹ i
  have h := star_eq_coe_inv_of_unitary (((Pi.evalMonoidHom _ i).comp ρ).toHomUnits g) (hu g i)
  exact h

/-- Any algebra map intertwining two unitary block presentations is a star map.
This gives the analytic part of identity-strand compatibility; the categorical
strand map and its intertwining property must still be supplied separately. -/
theorem presented_intertwiner_map_star
    (ρ : G →* A) (σ : H →* B) (τ : G →* H)
    {n m : ℕ} {d : Fin n → ℕ} {k : Fin m → ℕ}
    (e : groupImageAlgebra ρ ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : groupImageAlgebra σ ≃ₐ[ℂ] ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ)
    (he : ∀ g i, e (groupInImage ρ g) i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hf : ∀ h i, f (groupInImage σ h) i ∈ Matrix.unitaryGroup (Fin (k i)) ℂ)
    (φ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ]
      (∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ))
    (hφ : ∀ g, φ (e (groupInImage ρ g)) = f (groupInImage σ (τ g)))
    (x : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) : φ (star x) = star (φ x) := by
  let ρ' := e.toMonoidHom.comp (groupInImage ρ)
  let σ' := f.toMonoidHom.comp (groupInImage σ)
  apply map_star_of_group_span ρ' σ' τ φ (presented_group_span ρ e)
  · exact unitary_block_star_inv ρ' he
  · exact unitary_block_star_inv σ' hf
  · exact hφ

end PropertyF.Ground.Calculus
