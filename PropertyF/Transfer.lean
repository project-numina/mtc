module
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic

@[expose] public noncomputable section
namespace PropertyF

/-- Quotient transfer of finite images, the group-theoretic part of §2.1. -/
theorem finite_range_of_ker_le {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : G →* K) [Finite f.range] (hker : f.ker ≤ g.ker) : Finite g.range := by
  let : g.ker.FiniteIndex := Subgroup.finiteIndex_of_le hker
  exact Finite.of_equiv (G ⧸ g.ker) (QuotientGroup.quotientKerEquivRange g)

/-- Restriction to an invariant embedded set preserves finite images. Applying
this to the split inclusion of each tensor power gives summand transfer in §2.1.
No linearity is needed for this finiteness argument. -/
theorem finite_range_of_intertwiner {G V W : Type*} [Group G]
    (ρV : G →* Equiv.Perm V) (ρW : G →* Equiv.Perm W) [Finite ρV.range]
    (i : W → V) (hi : Function.Injective i)
    (hintertwine : ∀ g w, ρV g (i w) = i (ρW g w)) : Finite ρW.range := by
  apply finite_range_of_ker_le ρV ρW
  intro g hg
  change ρV g = 1 at hg
  change ρW g = 1
  ext w
  apply hi
  rw [← hintertwine, hg]
  rfl

/-- The diagonal braid image in a product embeds in the product of its factor
images, so finite factor images imply a finite product image (§2.1). -/
theorem finite_product_image {G H ι : Type*} [Group G] [Group H]
    (g : ι → G) (h : ι → H)
    [Finite (Subgroup.closure (Set.range g))] [Finite (Subgroup.closure (Set.range h))] :
    Finite (Subgroup.closure (Set.range (fun i => (g i, h i)))) := by
  let A := Subgroup.closure (Set.range g)
  let B := Subgroup.closure (Set.range h)
  have hle : Subgroup.closure (Set.range (fun i => (g i, h i))) ≤ A.prod B := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨Subgroup.subset_closure (Set.mem_range_self i),
      Subgroup.subset_closure (Set.mem_range_self i)⟩
  let j : Subgroup.closure (Set.range (fun i => (g i, h i))) → A × B :=
    fun x => (⟨x.val.1, (hle x.property).1⟩, ⟨x.val.2, (hle x.property).2⟩)
  apply Finite.of_injective j
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun p : A × B => (p.1 : G)) hxy
  · exact congrArg (fun p : A × B => (p.2 : H)) hxy

end PropertyF
