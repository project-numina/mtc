module
public import PropertyF.Ground.Cabling.PowerAssoc
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Tensor expressions in a single generator and the unit. -/
inductive PowerExpr where
  | unit
  | atom
  | tensor (a b : PowerExpr)

def PowerExpr.eval (X : C) : PowerExpr → C
  | .unit => 𝟙_ C
  | .atom => X
  | .tensor a b => a.eval X ⊗ b.eval X

def PowerExpr.length : PowerExpr → ℕ
  | .unit => 0
  | .atom => 1
  | .tensor a b => a.length + b.length

/-- Canonical right-associated normalization of an expression. -/
def PowerExpr.normalize (X : C) : ∀ a : PowerExpr, a.eval X ≅ tensorPower X a.length
  | .unit => Iso.refl _
  | .atom => (ρ_ X).symm
  | .tensor a b => (a.normalize X ⊗ᵢ b.normalize X) ≪≫ tensorPowerTensorIso X a.length b.length

/-- A morphism is a cabled braid when its canonical normalization belongs to
the appropriate braid image, with strand-count transport. -/
def PowerExpr.IsCable (X : C) (a b : PowerExpr) (f : a.eval X ⟶ b.eval X) : Prop :=
  cableHom X a.length b.length ((a.normalize X).inv ≫ f ≫ (b.normalize X).hom)

theorem cableHom_id (X : C) (n : ℕ) : cableHom X n n (𝟙 _) := ⟨rfl, 1, by simp⟩

theorem PowerExpr.isCable_id (X : C) (a : PowerExpr) : IsCable X a a (𝟙 _) := by
  simpa [IsCable] using cableHom_id X a.length

theorem PowerExpr.isCable_comp (X : C) {a b c : PowerExpr}
    {f : a.eval X ⟶ b.eval X} {g : b.eval X ⟶ c.eval X}
    (hf : IsCable X a b f) (hg : IsCable X b c g) : IsCable X a c (f ≫ g) := by
  have h := cableHom_comp X hf hg
  simpa [IsCable, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
theorem PowerExpr.isCable_tensor (X : C) {a b c d : PowerExpr}
    {f : a.eval X ⟶ b.eval X} {g : c.eval X ⟶ d.eval X}
    (hf : IsCable X a b f) (hg : IsCable X c d g) :
    IsCable X (.tensor a c) (.tensor b d) (f ⊗ₘ g) := by
  have h := cableHom_tensor X _ _ hf hg
  have heq : ((PowerExpr.tensor a c).normalize X).inv ≫ (f ⊗ₘ g) ≫
      ((PowerExpr.tensor b d).normalize X).hom =
        (tensorPowerTensorIso X a.length c.length).inv ≫
          (((a.normalize X).inv ≫ f ≫ (b.normalize X).hom) ⊗ₘ
            ((c.normalize X).inv ≫ g ≫ (d.normalize X).hom)) ≫
              (tensorPowerTensorIso X b.length d.length).hom := by
    dsimp only [normalize, Iso.trans_inv, Iso.trans_hom, tensorIso_inv, tensorIso_hom]
    simp only [← Category.assoc]
    rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
  change cableHom X (a.length+c.length) (b.length+d.length) _
  rw [heq]
  exact h
/-- Inverses of cabled isomorphisms remain cabled. -/
theorem PowerExpr.isCable_inv (X : C) {a b : PowerExpr} (e : a.eval X ≅ b.eval X)
    (he : IsCable X a b e.hom) : IsCable X b a e.inv := by
  let e' := (a.normalize X).symm ≪≫ e ≪≫ b.normalize X
  have h : cableHom X b.length a.length e'.inv := cableHom_inv X e' he
  simpa [IsCable, e', Category.assoc] using h

/-- Identity transport of strand counts is a cabled map. -/
theorem cableHom_eqToHom (X : C) {m n : ℕ} (h : m = n) :
    cableHom X m n (eqToHom (congrArg (tensorPower X) h)) := by
  refine ⟨h, 1, ?_⟩
  simp
end PropertyF
