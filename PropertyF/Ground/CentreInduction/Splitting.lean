module
public import PropertyF.Ground.CentreInduction.Averaging
public import PropertyF.Ground.CentreInduction.SimpleDetection
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import PropertyF.Ground.Centre.Cokernel

/-! The Maschke consequence of the remaining loop-sliding identity. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- The specific, as-yet-unproved sliding identity needed for averaging. It is
stated only against the finite family of simple representatives. -/
def SimpleLoopCentrality (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) : Prop :=
  ∀ (X Y : CategoryTheory.Center C.Obj) (f : X.1 ⟶ Y.1) i,
    (loopSum C p X Y f ▷ simples C i) ≫ (Y.2.β (simples C i)).hom =
      (X.2.β (simples C i)).hom ≫ (simples C i ◁ loopSum C p X Y f)

/-- Assuming the loop-sliding identity, normalized averaging produces an
actual centre map from any underlying map. -/
def average (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hslide : SimpleLoopCentrality C p)
    (X Y : CategoryTheory.Center C.Obj) (f : X.1 ⟶ Y.1) : X ⟶ Y where
  f := (globalDimension C)⁻¹ • loopSum C p X Y f
  comm U := by
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp,
      MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]
    rw [comm_of_simples C X Y (loopSum C p X Y f) (hslide X Y f) U]

/-- The normalized average fixes all centre morphisms when the global
dimension is nonzero. -/
theorem average_center_hom (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    {X Y : CategoryTheory.Center C.Obj} (f : X ⟶ Y) :
    average C p hslide X Y f.f = f := by
  apply CategoryTheory.Center.ext
  simp [average, loopSum_center_hom C p hp f, smul_smul, hne]

/-- Normalized averaging is idempotent once the sliding identity has been
proved. -/
theorem average_idempotent (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (X Y : CategoryTheory.Center C.Obj) (f : X.1 ⟶ Y.1) :
    average C p hslide X Y (average C p hslide X Y f).f =
      average C p hslide X Y f :=
  average_center_hom C p hp hslide hne (average C p hslide X Y f)

/-- If the loop-sliding identity holds, every epimorphism in the centre splits.
The global-dimension and spherical hypotheses remain explicit. -/
theorem epi_splits_of_loop_centrality (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    {X Y : CategoryTheory.Center C.Obj} (f : X ⟶ Y) [Epi f] : IsSplitEpi f := by
  letI : Epi f.f := by
    change Epi ((CategoryTheory.Center.forget C.Obj).map f)
    infer_instance
  letI : IsSplitEpi f.f := epi_splits C f.f
  let s := average C p hslide Y X (section_ f.f)
  refine IsSplitEpi.mk' { section_ := s, id := ?_ }
  apply CategoryTheory.Center.ext
  change ((globalDimension C)⁻¹ • loopSum C p Y X (section_ f.f)) ≫ f.f = 𝟙 Y.1
  rw [Linear.smul_comp, ← loopSum_postcompose C p (section_ f.f) f]
  rw [IsSplitEpi.id, ← CategoryTheory.Center.id_f Y, loopSum_center_hom C p hp (𝟙 Y)]
  simp [smul_smul, hne]

/-- The same averaging argument splits monomorphisms in the centre. -/
theorem mono_splits_of_loop_centrality (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    {X Y : CategoryTheory.Center C.Obj} (f : X ⟶ Y) [Mono f] : IsSplitMono f := by
  letI : Mono f.f := by
    change Mono ((CategoryTheory.Center.forget C.Obj).map f)
    infer_instance
  letI : IsSplitMono f.f := mono_splits C f.f
  let r := average C p hslide Y X (retraction f.f)
  refine IsSplitMono.mk' { retraction := r, id := ?_ }
  apply CategoryTheory.Center.ext
  change f.f ≫ ((globalDimension C)⁻¹ • loopSum C p Y X (retraction f.f)) = 𝟙 X.1
  rw [Linear.comp_smul, ← loopSum_precompose C p f (retraction f.f)]
  rw [IsSplitMono.id, ← CategoryTheory.Center.id_f X, loopSum_center_hom C p hp (𝟙 X)]
  simp [smul_smul, hne]

end PropertyF.Ground.CentreInduction
