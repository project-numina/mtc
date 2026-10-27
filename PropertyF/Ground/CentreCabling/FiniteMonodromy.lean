module
public import PropertyF.Ground.Calculus.ThreeRigidity
public import PropertyF.Ground.Modular.SAdditivity

/-! Property F gives finite order for mixed double braidings. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreCabling
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Double braiding is natural simultaneously in both strands. -/
theorem doubleBraiding_natural {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    Modular.doubleBraiding X Y ≫ (f ⊗ₘ g) =
      (f ⊗ₘ g) ≫ Modular.doubleBraiding X' Y' := by
  unfold Modular.doubleBraiding
  rw [Category.assoc, ← BraidedCategory.braiding_naturality g f,
    ← Category.assoc, ← BraidedCategory.braiding_naturality f g, Category.assoc]

/-- A split intertwiner carries finite-order endomorphisms to finite-order
endomorphisms. -/
theorem finite_order_of_retract {D : Type u} [Category.{v} D]
    {X Y : D} (r : Retract X Y) (f : End X) (g : End Y)
    (h : f.asHom ≫ r.i = r.i ≫ g.asHom)
    (n : ℕ) (hn : g ^ n = 1) : f ^ n = 1 := by
  have hp : ∀ n : ℕ, (f ^ n).asHom ≫ r.i = r.i ≫ (g ^ n).asHom := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ, End.mul_asHom]
      rw [Category.assoc, ih, ← Category.assoc, h, Category.assoc]
  apply End.ext
  apply (cancel_mono r.i).mp
  simpa [hn] using hp n

/-- In a property-F fusion category, mixed double braidings have finite order. -/
theorem mixedMonodromy_finite_order (D : Ground.BraidedFusionCategory.{v,u})
    (hF : HasPropertyF D.Obj) (X Y : D.Obj) :
    ∃ n : ℕ, n ≠ 0 ∧ (End.of (Modular.doubleBraiding X Y)) ^ n = 1 := by
  let V := X ⊞ Y
  let r : Retract (X ⊗ Y) (V ⊗ V) := {
    i := biprod.inl ⊗ₘ biprod.inr
    r := biprod.fst ⊗ₘ biprod.snd
    retract := by simp [tensorHom_comp_tensorHom] }
  obtain ⟨n, hn, hpow⟩ := Calculus.selfMonodromy_finite_order D V (hF V)
  refine ⟨n, hn, finite_order_of_retract r _ _ ?_ n hpow⟩
  exact doubleBraiding_natural biprod.inl biprod.inr

end PropertyF.Ground.CentreCabling
