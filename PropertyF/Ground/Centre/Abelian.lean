module
public import PropertyF.Ground.Centre.Cokernel

/-! The Drinfeld centre of a rigid abelian monoidal category is abelian. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [RigidCategory C]

/-- A monomorphism in the centre is the kernel of its cokernel. -/
@[instance_reducible]
def centerNormalMono {X Y : CategoryTheory.Center C} (f : X ⟶ Y) [Mono f] : NormalMono f := by
  let k := centerKernelLift (centerCokernelπ f) f (centerCokernel_condition f)
  have hk : k ≫ centerKernelι (centerCokernelπ f) = f := by
    apply CategoryTheory.Center.ext
    change kernel.lift (cokernel.π f.f) f.f _ ≫ kernel.ι (cokernel.π f.f) = f.f
    exact kernel.lift_ι _ _ _
  have : Mono f.f := by
    change Mono ((CategoryTheory.Center.forget C).map f)
    infer_instance
  have : IsIso k.f := by
    change IsIso (Abelian.factorThruImage f.f)
    infer_instance
  have : IsIso k := CategoryTheory.Center.isIso_of_f_isIso k
  refine { Z := centerCokernel f
           g := centerCokernelπ f
           w := centerCokernel_condition f
           isLimit := ?_ }
  apply KernelFork.IsLimit.ofι' _ _
  intro W g hg
  let l := centerKernelLift (centerCokernelπ f) g hg
  have hl : l ≫ centerKernelι (centerCokernelπ f) = g := by
    apply CategoryTheory.Center.ext
    change kernel.lift (cokernel.π f.f) g.f _ ≫ kernel.ι (cokernel.π f.f) = g.f
    exact kernel.lift_ι _ _ _
  refine ⟨l ≫ inv k, ?_⟩
  calc
    (l ≫ inv k) ≫ f = (l ≫ inv k) ≫ (k ≫ centerKernelι (centerCokernelπ f)) :=
      congrArg (fun t => (l ≫ inv k) ≫ t) hk.symm
    _ = g := by simp [Category.assoc, hl]

/-- An epimorphism in the centre is the cokernel of its kernel. -/
@[instance_reducible]
def centerNormalEpi {X Y : CategoryTheory.Center C} (f : X ⟶ Y) [Epi f] : NormalEpi f := by
  let k := centerCokernelDesc (centerKernelι f) f (centerKernel_condition f)
  have hk : centerCokernelπ (centerKernelι f) ≫ k = f := by
    apply CategoryTheory.Center.ext
    change cokernel.π (kernel.ι f.f) ≫ cokernel.desc (kernel.ι f.f) f.f _ = f.f
    exact cokernel.π_desc _ _ _
  have : Epi f.f := by
    change Epi ((CategoryTheory.Center.forget C).map f)
    infer_instance
  have : IsIso k.f := by
    change IsIso (Abelian.factorThruCoimage f.f)
    infer_instance
  have : IsIso k := CategoryTheory.Center.isIso_of_f_isIso k
  refine { W := centerKernel f
           g := centerKernelι f
           w := centerKernel_condition f
           isColimit := ?_ }
  apply CokernelCofork.IsColimit.ofπ' _ _
  intro W g hg
  let l := centerCokernelDesc (centerKernelι f) g hg
  have hl : centerCokernelπ (centerKernelι f) ≫ l = g := by
    apply CategoryTheory.Center.ext
    change cokernel.π (kernel.ι f.f) ≫ cokernel.desc (kernel.ι f.f) g.f _ = g.f
    exact cokernel.π_desc _ _ _
  refine ⟨inv k ≫ l, ?_⟩
  calc
    f ≫ (inv k ≫ l) = (centerCokernelπ (centerKernelι f) ≫ k) ≫ (inv k ≫ l) :=
      congrArg (fun t => t ≫ (inv k ≫ l)) hk.symm
    _ = g := by simp [Category.assoc, hl]

/-- The centre of a rigid abelian monoidal category is abelian. -/
instance centerAbelian : Abelian (CategoryTheory.Center C) where
  normalMonoOfMono f := ⟨centerNormalMono f⟩
  normalEpiOfEpi f := ⟨centerNormalEpi f⟩

end PropertyF.Ground.Centre
