/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

universe v u

open CategoryTheory ShortComplex Limits


namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C] {X Y : ShortComplex C} (f : X ⟶ Y)

namespace ShortComplex

variable [HasKernel f.τ₁] [HasKernel f.τ₂] [HasKernel f.τ₃]

/-- Construction of a kernel fork for a functor `J ⥤ ShortComplex C` using the kernels
of the three components `J ⥤ C`. -/
@[simps!]
noncomputable def kernelFork : KernelFork f :=
  KernelFork.ofι (Z := ShortComplex.mk (kernel.map _ _ X.f Y.f f.comm₁₂)
    (kernel.map _ _ X.g Y.g f.comm₂₃) <| by simp [← cancel_mono (kernel.ι _)])
    { τ₁ := kernel.ι _, τ₂ := kernel.ι _, τ₃ := kernel.ι _ } <| by ext <;> simp

/-- `kernelFork` is a kernel. -/
noncomputable def isKernelKernelFork : IsLimit (kernelFork f) := by
  refine isLimitOfIsLimitπ _
    (IsLimit.equivOfNatIsoOfIso (parallelPair.ext (eqToIso ?_) (eqToIso ?_) ?_ ?_) _ _
      (Cones.ext (eqToIso ?_) (by rintro (_ | _) <;> simp)) (limit.isLimit <| parallelPair f.τ₁ 0))
    (IsLimit.equivOfNatIsoOfIso (parallelPair.ext (eqToIso ?_) (eqToIso ?_) ?_ ?_) _ _
      (Cones.ext (eqToIso ?_) (by rintro (_ | _) <;> simp)) (limit.isLimit <| parallelPair f.τ₂ 0))
    (IsLimit.equivOfNatIsoOfIso (parallelPair.ext (eqToIso ?_) (eqToIso ?_) ?_ ?_) _ _
      (Cones.ext (eqToIso ?_) (by rintro (_ | _) <;> simp)) (limit.isLimit (parallelPair f.τ₃ 0)))
  <;> simp

variable [HasCokernel f.τ₁] [HasCokernel f.τ₂] [HasCokernel f.τ₃]

/-- Construction of a cokernel cofork for a functor `J ⥤ ShortComplex C` using the cokernels
of the three components `J ⥤ C`. -/
@[simps!]
noncomputable def cokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (Z := ShortComplex.mk (cokernel.map _ _ X.f Y.f f.comm₁₂)
    (cokernel.map _ _ X.g Y.g f.comm₂₃) <| by simp [← cancel_epi (cokernel.π _)])
    { τ₁ := cokernel.π _, τ₂ := cokernel.π _, τ₃ := cokernel.π _ } <| by ext <;> simp

/-- `cokernelCofork` is a kernel. -/
noncomputable def isCokernelCokernelCofork : IsColimit (cokernelCofork f) := by
  refine isColimitOfIsColimitπ _
    (IsColimit.equivOfNatIsoOfIso (parallelPair.ext (eqToIso ?_) (eqToIso ?_) ?_ ?_) _ _
      (Cocones.ext (eqToIso ?_) (by rintro (_ | _) <;> simp [-colimit.cocone_ι]))
        (colimit.isColimit <| parallelPair f.τ₁ 0))
    (IsColimit.equivOfNatIsoOfIso (parallelPair.ext (eqToIso ?_) (eqToIso ?_) ?_ ?_) _ _
      (Cocones.ext (eqToIso ?_) (by rintro (_ | _) <;> simp [-colimit.cocone_ι]))
        (colimit.isColimit <| parallelPair f.τ₂ 0))
    (IsColimit.equivOfNatIsoOfIso (parallelPair.ext (eqToIso ?_) (eqToIso ?_) ?_ ?_) _ _
      (Cocones.ext (eqToIso ?_) (by rintro (_ | _) <;> simp [-colimit.cocone_ι]))
        (colimit.isColimit (parallelPair f.τ₃ 0)))
  <;> simp

end ShortComplex
end CategoryTheory
namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- For a representation `A` of a finite group `G`, the norm map `A ⟶ A` induces a linear map
`A_G →ₗ[k] Aᴳ`. -/
noncomputable def liftRestrictNorm : ρ.Coinvariants →ₗ[k] ρ.invariants :=
  Coinvariants.lift ρ ((norm ρ).codRestrict _ <| by simp) <| by simp

end Representation
namespace Rep

variable (k G : Type u) [CommRing k] [Group G] [Fintype G] (A : Rep k G)

/-- Given a finite group `G`, this is the natural transformation sending a `G`-representation `A`
to the map `A_G →ₗ[k] Aᴳ` induced by the norm map on `A`. -/
@[simps]
noncomputable def liftRestrictNormNatTrans :
    coinvariantsFunctor k G ⟶ invariantsFunctor k G where
  app A := ModuleCat.ofHom <| Representation.liftRestrictNorm A.ρ
  naturality _ _ _ := by
    ext
    simp [Representation.liftRestrictNorm, invariantsFunctor, Representation.norm,
      hom_comm_apply, LinearMap.codRestrict]

end Rep
section

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D] (F G : C ⥤ D)
  [F.Additive] [G.Additive] [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  (X : ShortComplex C) (hX : ShortExact X) [PreservesFiniteColimits F] [PreservesFiniteLimits G]
  (T : F ⟶ G)

@[simps]
noncomputable def CategoryTheory.ShortComplex.natTransSnakeInput : SnakeInput D where
  L₀ := kernel (X.mapNatTrans T)
  L₁ := F.mapShortComplex.obj X
  L₂ := G.mapShortComplex.obj X
  L₃ := cokernel (X.mapNatTrans T)
  v₀₁ := kernel.ι (X.mapNatTrans T)
  v₁₂ := X.mapNatTrans T
  v₂₃ := cokernel.π (X.mapNatTrans T)
  w₀₂ := kernel.condition (X.mapNatTrans T)
  w₁₃ := cokernel.condition (X.mapNatTrans T)
  h₀ := kernelIsKernel (X.mapNatTrans T)
  h₃ := cokernelIsCokernel (X.mapNatTrans T)
  L₁_exact := by
    have := (F.preservesFiniteColimits_tfae.out 3 0).1
    exact (this ⟨PreservesFiniteColimits.preservesFiniteColimits⟩ X hX).1
  epi_L₁_g := by
    have := (F.preservesFiniteColimits_tfae.out 3 0).1
    apply (this ⟨PreservesFiniteColimits.preservesFiniteColimits⟩ X hX).2
  L₂_exact := by
    have := (G.preservesFiniteLimits_tfae.out 3 0).1
    apply (this ⟨PreservesFiniteLimits.preservesFiniteLimits⟩ X hX).1
  mono_L₂_f := by
    have := (G.preservesFiniteLimits_tfae.out 3 0).1
    apply (this ⟨PreservesFiniteLimits.preservesFiniteLimits⟩ X hX).2

end

open Rep Representation

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] [DecidableEq G]
  (S : ShortComplex (Rep k G)) (hS : S.ShortExact)

noncomputable def TateCohomology {k G : Type u} [CommRing k] [Group G]
    [Fintype G] [DecidableEq G] (A : Rep k G) (i : ℤ) : ModuleCat k :=
  match i with
  | 0 => cokernel ((liftRestrictNormNatTrans k G).app A) --ModuleCat.of k (A.ρ.invariants ⧸ (LinearMap.range (liftRestrictNorm A.ρ)))
  | (n + 1 : ℕ) => groupCohomology A (n + 1)
  | -1 => kernel ((liftRestrictNormNatTrans k G).app A) --ModuleCat.of k (LinearMap.ker (liftRestrictNorm A.ρ))
  | -(n + 2 : ℕ) => groupHomology A (n + 1)

namespace TateCohomology
open groupCohomology groupHomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] [DecidableEq G] (A : Rep k G)
  {A B : Rep k G}

noncomputable def map (φ : A ⟶ B) (n : ℤ) :
    TateCohomology A n ⟶ TateCohomology B n :=
  match n with
  | 0 => cokernel.map _ _ ((coinvariantsFunctor k G).map φ) ((invariantsFunctor k G).map φ) <| by
      ext
      simp [liftRestrictNorm, LinearMap.codRestrict, invariantsFunctor, Representation.norm,
        hom_comm_apply]
  /- ModuleCat.ofHom <| Submodule.mapQ _ _ ((invariantsFunctor k G).map φ).hom <| by
    rintro y ⟨x, rfl⟩
    induction' x using Quotient.inductionOn' with x
    use (Submodule.Quotient.mk (φ.hom x))
    ext
    simpa [liftRestrictNorm, Submodule.Quotient.mk''_eq_mk, norm]
      using congr(∑ c : G, $((hom_comm_apply φ _ _).symm))-/
  | (n + 1 : ℕ) => groupCohomology.map (MonoidHom.id G) φ (n + 1)
  | -1 => kernel.map _ _ ((coinvariantsFunctor k G).map φ) ((invariantsFunctor k G).map φ) <| by
      ext
      simp [liftRestrictNorm, LinearMap.codRestrict, invariantsFunctor, Representation.norm,
        hom_comm_apply]
  /-ModuleCat.ofHom <| LinearMap.restrict (coinvariantsMap φ) <| by
    rintro x (hx : _ = _)
    ext
    induction' x using Quotient.inductionOn' with x
    have := fun c => (hom_comm_apply φ c x).symm
    simp_all [liftRestrictNorm, Submodule.Quotient.mk''_eq_mk, Subtype.ext_iff,
      norm, ← map_sum, @map_zero A B]-/
  | -(n + 2 : ℕ) => groupHomology.map (MonoidHom.id G) φ (n + 1)

@[simp]
theorem map_id (n : ℤ) : map (𝟙 A) n = 𝟙 _ :=
  match n with
  | 0 => by simp [← cancel_epi (cokernel.π _), map, TateCohomology]
  | (n + 1 : ℕ) => by
    simp [-Int.natCast_add, ← cancel_epi (groupCohomology.π _ _), TateCohomology, map]
  | -1 => by simp [← cancel_mono (kernel.ι _), map, TateCohomology]
  | Int.negSucc (n + 1) => by simp [← cancel_epi (groupHomology.π _ _), TateCohomology, map]

@[simp]
theorem map_comp {C : Rep k G} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ) :
    map (f ≫ g) n = map f n ≫ map g n :=
  match n with
  | 0 => by simp [← cancel_epi (cokernel.π _), map, TateCohomology]
  | (n + 1 : ℕ) => by
    simp [-Int.natCast_add, ← cancel_epi (groupCohomology.π _ _), TateCohomology, map,
      cochainsMap_id_comp, HomologicalComplex.cyclesMap_comp]
  | -1 => by simp [← cancel_mono (kernel.ι _), map, TateCohomology]
  | Int.negSucc (n + 1) => by simp [← cancel_epi (groupHomology.π _ _), TateCohomology, map,
      chainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

variable (k G) in
@[simps]
noncomputable def _root_.tateCohomologyFunctor (n : ℤ) : Rep k G ⥤ ModuleCat k where
  obj A := TateCohomology A n
  map f := map f n
  map_id _ := map_id n
  map_comp f g := map_comp f g n

instance (n : ℤ) : (tateCohomologyFunctor k G n).PreservesZeroMorphisms :=
  match n with
  | 0 => ⟨fun _ _ => by simp [← cancel_epi (cokernel.π _), map]⟩
  | (n + 1 : ℕ) => inferInstanceAs (groupCohomology.functor k G (n + 1)).PreservesZeroMorphisms
  | -1 => ⟨fun _ _ => by simp [← cancel_mono (kernel.ι _), map]⟩
  | -(n + 2 : ℕ) => inferInstanceAs (groupHomology.functor k G (n + 1)).PreservesZeroMorphisms

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

noncomputable def snakeInput : SnakeInput (ModuleCat k) where
  L₀ := (kernelFork (X.mapNatTrans <| liftRestrictNormNatTrans k G)).pt
  L₁ := (coinvariantsFunctor k G).mapShortComplex.obj X
  L₂ := (invariantsFunctor k G).mapShortComplex.obj X
  L₃ := (cokernelCofork (X.mapNatTrans <| liftRestrictNormNatTrans k G)).pt
  v₀₁ := (kernelFork (X.mapNatTrans <| liftRestrictNormNatTrans k G)).ι
  v₁₂ := X.mapNatTrans (liftRestrictNormNatTrans k G)
  v₂₃ := (cokernelCofork (X.mapNatTrans <| liftRestrictNormNatTrans k G)).π
  w₀₂ := (kernelFork _).condition
  w₁₃ := (cokernelCofork _).condition
  h₀ := isKernelKernelFork _
  h₃ := isCokernelCokernelCofork _
  L₁_exact := by
    have := ((coinvariantsFunctor k G).preservesFiniteColimits_tfae.out 3 0).1
    exact (this ⟨PreservesFiniteColimits.preservesFiniteColimits⟩ X hX).1
  epi_L₁_g := by
    have := ((coinvariantsFunctor k G).preservesFiniteColimits_tfae.out 3 0).1
    apply (this ⟨PreservesFiniteColimits.preservesFiniteColimits⟩ X hX).2
  L₂_exact := by
    have := ((invariantsFunctor k G).preservesFiniteLimits_tfae.out 3 0).1
    apply (this ⟨PreservesFiniteLimits.preservesFiniteLimits⟩ X hX).1
  mono_L₂_f := by
    have := ((invariantsFunctor k G).preservesFiniteLimits_tfae.out 3 0).1
    apply (this ⟨PreservesFiniteLimits.preservesFiniteLimits⟩ X hX).2
/-
noncomputable def snakeInputIso₀ :
    (snakeInput hX).L₀ ≅ X.map (tateCohomologyFunctor k G (-1)) :=
  Iso.refl _ --Limits.limit.isoLimitCone ⟨limitCone _, isLimitLimitCone _⟩

variable (X) in
noncomputable def isoShortComplex₀ :
    (colimitCocone (parallelPair (X.mapNatTrans <| liftRestrictNormNatTrans k G) 0)).pt
      ≅ X.map (tateCohomologyFunctor k G 0) :=
  ShortComplex.isoMk ((isColimitπ₁MapCoconeColimitCocone _).coconePointsIsoOfNatIso
    (ModuleCat.cokernelIsColimit _) (diagramIsoParallelPair <| parallelPair _ 0 ⋙ π₁))
    ((isColimitπ₂MapCoconeColimitCocone _).coconePointsIsoOfNatIso
    (ModuleCat.cokernelIsColimit _) (diagramIsoParallelPair <| parallelPair _ 0 ⋙ π₂))
    ((isColimitπ₃MapCoconeColimitCocone _).coconePointsIsoOfNatIso
    (ModuleCat.cokernelIsColimit _) (diagramIsoParallelPair <| parallelPair _ 0 ⋙ π₃))
    (by
      apply IsColimit.hom_ext (isColimitπ₁MapCoconeColimitCocone
        (parallelPair (X.mapNatTrans <| liftRestrictNormNatTrans k G) 0))
      rintro (_ | _)
      · simp
      · simp only [IsColimit.coconePointsIsoOfNatIso_hom, ← Category.assoc, IsColimit.ι_map]
        simp only [colimitCocone, π₁_map, parallelPair_obj_zero, Functor.comp_obj,
          diagramIsoParallelPair_hom_app, eqToHom_refl, Functor.mapCocone_ι_app, ι_colimMap,
          Category.id_comp, Category.assoc]
        exact (isColimitπ₂MapCoconeColimitCocone _).ι_map (ModuleCat.cokernelCocone
          (π₂.map (X.mapNatTrans <| liftRestrictNormNatTrans k G))) (diagramIsoParallelPair
          (parallelPair (X.mapNatTrans <| liftRestrictNormNatTrans k G) 0 ⋙ π₂)).hom
          WalkingParallelPair.one ▸ rfl)
    (by
      apply IsColimit.hom_ext (isColimitπ₂MapCoconeColimitCocone
        (parallelPair (X.mapNatTrans <| liftRestrictNormNatTrans k G) 0))
      rintro (_ | _)
      · simp
      · simp only [IsColimit.coconePointsIsoOfNatIso_hom, ← Category.assoc, IsColimit.ι_map]
        simp only [colimitCocone, π₂_map, parallelPair_obj_zero, Functor.comp_obj,
          diagramIsoParallelPair_hom_app, eqToHom_refl, Functor.mapCocone_ι_app, ι_colimMap,
          Category.id_comp, Category.assoc]
        exact (isColimitπ₃MapCoconeColimitCocone _).ι_map (ModuleCat.cokernelCocone
          (π₃.map (X.mapNatTrans <| liftRestrictNormNatTrans k G))) (diagramIsoParallelPair
          (parallelPair (X.mapNatTrans <| liftRestrictNormNatTrans k G) 0 ⋙ π₃)).hom
          WalkingParallelPair.one ▸ rfl)

noncomputable def snakeInputIso₃ :
    (snakeInput hX).L₃ ≅ X.map (tateCohomologyFunctor k G 0) :=
  Limits.colimit.isoColimitCocone ⟨colimitCocone _, isColimitColimitCocone _⟩
    ≪≫ isoShortComplex₀ X

@[reassoc (attr := simp)]
theorem map_π₁_snakeInputIso₀_inv_comp_ι :
    π₁.map ((snakeInputIso₀ hX).inv ≫ kernel.ι _) = ModuleCat.ofHom (Submodule.subtype _) := by
  unfold snakeInputIso₀
  simp only [Int.reduceNeg, Functor.comp_obj, parallelPair_obj_zero, parallelPair_obj_one,
    Functor.comp_map, parallelPair_map_left, Iso.trans_inv, IsLimit.conePointsIsoOfNatIso_inv,
    Functor.mapIso_inv, Category.assoc, ← Functor.map_comp, limit.isoLimitCone_inv_π,
    Fork.app_zero_eq_ι]
  exact IsLimit.map_π _ _ _ _

@[reassoc (attr := simp)]
theorem map_π₂_snakeInputIso₀_inv_comp_ι :
    π₂.map ((snakeInputIso₀ hX).inv ≫ kernel.ι _) = ModuleCat.ofHom (Submodule.subtype _) := by
  unfold snakeInputIso₀
  simp only [Int.reduceNeg, Functor.comp_obj, parallelPair_obj_zero, parallelPair_obj_one,
    Functor.comp_map, parallelPair_map_left, Iso.trans_inv, IsLimit.conePointsIsoOfNatIso_inv,
    Functor.mapIso_inv, Category.assoc, ← Functor.map_comp, limit.isoLimitCone_inv_π,
    Fork.app_zero_eq_ι]
  exact IsLimit.map_π _ _ _ _

@[reassoc (attr := simp)]
theorem map_π₃_snakeInputIso₀_inv_comp_ι :
    π₃.map ((snakeInputIso₀ hX).inv ≫ kernel.ι _) = ModuleCat.ofHom (Submodule.subtype _) := by
  unfold snakeInputIso₀
  simp only [Int.reduceNeg, Functor.comp_obj, parallelPair_obj_zero, parallelPair_obj_one,
    Functor.comp_map, parallelPair_map_left, Iso.trans_inv, IsLimit.conePointsIsoOfNatIso_inv,
    Functor.mapIso_inv, Category.assoc, ← Functor.map_comp, limit.isoLimitCone_inv_π,
    Fork.app_zero_eq_ι]
  exact IsLimit.map_π _ _ _ _

@[reassoc (attr := simp)]
theorem map_π₁_comp_snakeInputIso₃_hom :
    π₁.map (cokernel.π _ ≫ (snakeInputIso₃ hX).hom) = ModuleCat.ofHom (Submodule.mkQ _) := by
  unfold snakeInputIso₃
  simp only [Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc, ← Functor.map_comp,
    colimit.isoColimitCocone_ι_hom]
  exact IsColimit.ι_map _ _ _ _

@[reassoc (attr := simp)]
theorem map_π₂_comp_snakeInputIso₃_hom :
    π₂.map (cokernel.π _ ≫ (snakeInputIso₃ hX).hom) = ModuleCat.ofHom (Submodule.mkQ _) := by
  unfold snakeInputIso₃
  simp only [Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc, ← Functor.map_comp,
    colimit.isoColimitCocone_ι_hom]
  exact IsColimit.ι_map _ _ _ _

@[reassoc (attr := simp)]
theorem map_π₃_comp_snakeInputIso₃_hom :
    π₃.map (cokernel.π _ ≫ (snakeInputIso₃ hX).hom) = ModuleCat.ofHom (Submodule.mkQ _) := by
  unfold snakeInputIso₃
  simp only [Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc, ← Functor.map_comp,
    colimit.isoColimitCocone_ι_hom]
  exact IsColimit.ι_map _ _ _ _
-/

noncomputable def δ₀ : TateCohomology X.X₃ 0 ⟶ groupCohomology X.X₁ 1 :=
  cokernel.desc _ ((groupCohomology.H0Iso X.X₃).inv ≫ groupCohomology.δ hX 0 1 rfl) <| by
    simp [← cancel_epi <| (coinvariantsMk _ _).app _]
    have := (snakeInput hX).L₁'
    sorry

noncomputable def δNeg₁ : TateCohomology X.X₃ (-1) ⟶ TateCohomology X.X₁ 0 := (snakeInput hX).δ
/-
theorem δNeg₁_apply (z : X.X₃) (hz : (Submodule.mkQ _ z) ∈ LinearMap.ker (liftRestrictNorm X.X₃))
    (y : X.X₂) (x : X.X₁.ρ.invariants)
    (hyz : (· - z : X.X₃ → X.X₃) (X.g.hom y) ∈ X.X₃.ρ.augmentationSubmodule)
    (hx : X.f.hom x.1 = X.X₂.norm.hom y) :
    TateCohomology.δNeg₁ hX ⟨Submodule.mkQ _ z, hz⟩ = Submodule.mkQ _ x := by
  convert congr((π₁.mapIso <| snakeInputIso₃ hX).hom $((TateCohomology.snakeInput hX).δ_apply
    ((π₃.mapIso <| snakeInputIso₀ hX).inv ⟨Submodule.mkQ _ z, hz⟩) (Submodule.mkQ _ y) x
    (((Submodule.Quotient.eq _).2 hyz).trans (congr($(map_π₃_snakeInputIso₀_inv_comp_ι hX)
      ⟨Submodule.mkQ _ z, hz⟩)).symm) (Subtype.ext hx)))
  exact congr($((map_π₁_comp_snakeInputIso₃_hom hX).symm) _)

theorem liftRestrictNorm_δ₀_apply (x : groupHomology.H1 X.X₃) :
    liftRestrictNorm X.X₁ (groupHomology.δ₀ hX x) = 0 := by
  letI : Mono X.f := hX.2
  apply_fun (invariantsFunctor k G).map X.f using (ModuleCat.mono_iff_injective _).1 <|
    (invariantsFunctor k G).map_mono X.f
  have := Subtype.ext_iff.1 (congr($((liftRestrictNormNatTrans k G).naturality X.f)
    (groupHomology.δ₀ hX x))).symm
  refine Subtype.ext ?_
  have h : coinvariantsMap X.f (groupHomology.δ₀ hX x) = 0 :=
    LinearMap.mem_ker.1 <| (H0ShortComplex₁_exact hX).moduleCat_range_eq_ker
      ▸ LinearMap.mem_range_self _ _
  simp_all [-NatTrans.naturality]
-/

noncomputable def δNeg₂ : TateCohomology X.X₃ (-2) ⟶ TateCohomology X.X₁ (-1) :=
  kernel.lift _ (groupHomology.δ hX 1 0 rfl ≫ (groupHomology.H0Iso X.X₁).hom) sorry

noncomputable def δ (n : ℤ) : TateCohomology X.X₃ n ⟶ TateCohomology X.X₁ (n + 1) :=
  match n with
  | 0 => δ₀ hX
  | (n + 1 : ℕ) => groupCohomology.δ hX (n + 1) (n + 2) rfl
  | -1 => δNeg₁ hX
  | -2 => δNeg₂ hX
  | -(_ + 3 : ℕ) => groupHomology.δ hX _ _ rfl

#exit
variable (X) in
noncomputable def shortComplex₂ (n : ℤ) : ShortComplex (ModuleCat k) :=
  X.map (tateCohomologyFunctor k G n)

theorem shortComplex₂_exact (hX : ShortExact X) (n : ℤ) : (shortComplex₂ X n).Exact :=
  match n with
  | 0 => ShortComplex.exact_of_iso (snakeInputIso₃ hX) (SnakeInput.L₃_exact _)
  | (n + 1 : ℕ) => mapShortComplex₂_exact hX (n + 1)
  | -1 => ShortComplex.exact_of_iso (snakeInputIso₀ hX) (SnakeInput.L₀_exact _)
  | -(n + 2 : ℕ) => mapShortComplex₂_exact hX (n + 1)

noncomputable def shortComplexNeg₂₃ (hX : ShortExact X) : ShortComplex (ModuleCat k) where
  X₁ := TateCohomology X.X₂ (-2)
  X₂ := TateCohomology X.X₃ (-2)
  X₃ := TateCohomology X.X₁ (-1)
  f := map X.g (-2)
  g := δNeg₂ hX
  zero := by
    rw [← cancel_mono (ModuleCat.ofHom <| Submodule.subtype _)]
    have := congr($((groupHomology.H1ShortComplex₃ hX).zero) ≫ (groupHomology.isoH0 X.X₁).inv)
    have h := (CommSq.vert_inv ⟨groupHomology.map_comp_isoH1_hom (MonoidHom.id G) X.g⟩).w
    simp_all only [groupHomology.δ₀, Category.assoc, Iso.hom_inv_id, Category.comp_id, zero_comp,
      δNeg₂_comp_subtype, Iso.hom_inv_id_assoc]
    show groupHomology.map (MonoidHom.id G) X.g 1 ≫ _ = _
    simp_all only [← Category.assoc, Preadditive.IsIso.comp_right_eq_zero]
    simp_all

theorem shortComplexNeg₂₃_exact (hX : ShortExact X) : (shortComplexNeg₂₃ hX).Exact := by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x (hx : _ = _)
  have : (groupHomology.chainsMap_shortExact hX).δ 1 0 rfl x = 0 := by
    apply_fun (groupHomology.isoH0 X.X₁).hom using (ModuleCat.mono_iff_injective _).1 inferInstance
    rw [map_zero]
    exact Subtype.ext_iff.1 hx
  exact ((moduleCat_exact_iff_ker_sub_range _).1
    (groupHomology.mapShortComplex₃_exact hX (i := 1) rfl))
    this

noncomputable def shortComplexNeg₁₁ (hX : ShortExact X) : ShortComplex (ModuleCat k) where
  X₁ := TateCohomology X.X₃ (-2)
  X₂ := TateCohomology X.X₁ (-1)
  X₃ := TateCohomology X.X₂ (-1)
  f := δNeg₂ hX
  g := map X.f (-1)
  zero := by
    refine ModuleCat.hom_ext <| LinearMap.ext fun x => Subtype.ext ?_
    have := congr(((groupHomology.isoH1 X.X₃).hom ≫ $((groupHomology.H0ShortComplex₁ hX).zero)) x)
    simp_all only [groupHomology.δ₀, Category.assoc, Iso.hom_inv_id_assoc, ModuleCat.hom_comp,
      Function.comp_apply, comp_zero, LinearMap.zero_apply]
    simpa [-zero, δNeg₂, map, -ZeroMemClass.coe_eq_zero] using this

theorem shortComplexNeg₁₁_exact (hX : ShortExact X) : (shortComplexNeg₁₁ hX).Exact := by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x (hx : _ = _)
  have h := (moduleCat_exact_iff_ker_sub_range _).1 (groupHomology.H0ShortComplex₁_exact hX)
  rcases h (Subtype.ext_iff.1 hx) with ⟨y, (hy : _ = x.1)⟩
  refine ⟨(groupHomology.isoH1 X.X₃).inv y, Subtype.ext <| hy ▸ ?_⟩
  exact congr($((Iso.inv_comp_eq _).2 (δNeg₂_comp_subtype' hX)) y)

noncomputable def shortComplexNeg₁₃ (hX : ShortExact X) : ShortComplex (ModuleCat k) where
  X₁ := TateCohomology X.X₂ (-1)
  X₂ := TateCohomology X.X₃ (-1)
  X₃ := TateCohomology X.X₁ 0
  f := map X.g (-1)
  g := δNeg₁ hX
  zero := by
    have : map X.g (-1) = (π₂.mapIso (snakeInputIso₀ hX)).inv
        ≫ (_ ≫ (π₃.mapIso (snakeInputIso₀ hX)).hom) :=
      (Iso.eq_inv_comp _).2 (snakeInputIso₀ hX).hom.comm₂₃
    have h := congr($((snakeInput hX).L₁'.zero) ≫ π₁.map (snakeInputIso₃ hX).hom)
    simp_all [δNeg₁, -π₃_map, -π₂_map, -π₁_map]

noncomputable def isoShortComplexNeg₁₃ (hX : ShortExact X) :
    (snakeInput hX).L₁' ≅ shortComplexNeg₁₃ hX :=
  ShortComplex.isoMk (π₂.mapIso (snakeInputIso₀ hX))
    (π₃.mapIso (snakeInputIso₀ hX)) (π₁.mapIso (snakeInputIso₃ hX))
    (snakeInputIso₀ hX).hom.comm₂₃ (by simp [shortComplexNeg₁₃, δNeg₁, -π₃_map])

theorem shortComplexNeg₁₃_exact (hX : ShortExact X) :
    (shortComplexNeg₁₃ hX).Exact :=
  exact_of_iso (isoShortComplexNeg₁₃ hX) (snakeInput hX).L₁'_exact

noncomputable def shortComplex₀₁ (hX : ShortExact X) : ShortComplex (ModuleCat k) where
  X₁ := TateCohomology X.X₃ (-1)
  X₂ := TateCohomology X.X₁ 0
  X₃ := TateCohomology X.X₂ 0
  f := δNeg₁ hX
  g := map X.f 0
  zero := by
    have : map X.f 0 = (π₁.mapIso (snakeInputIso₃ hX)).inv ≫
        (_ ≫ (π₂.mapIso (snakeInputIso₃ hX)).hom) :=
      (Iso.eq_inv_comp _).2 (snakeInputIso₃ hX).hom.comm₁₂
    have h := congr($((snakeInput hX).L₂'.zero) ≫ π₂.map (snakeInputIso₃ hX).hom)
    simp_all [δNeg₁, -π₃_map, -π₂_map, -π₁_map]

noncomputable def isoShortComplex₀₁ (hX : ShortExact X) :
    (snakeInput hX).L₂' ≅ shortComplex₀₁ hX :=
  ShortComplex.isoMk (π₃.mapIso (snakeInputIso₀ hX))
    (π₁.mapIso (snakeInputIso₃ hX)) (π₂.mapIso (snakeInputIso₃ hX))
    (by simp [shortComplex₀₁, δNeg₁, -π₃_map]) (snakeInputIso₃ hX).hom.comm₁₂

theorem shortComplex₀₁_exact (hX : ShortExact X) :
    (shortComplex₀₁ hX).Exact :=
  exact_of_iso (isoShortComplex₀₁ hX) (snakeInput hX).L₂'_exact

noncomputable def shortComplex₀₃ (hX : ShortExact X) : ShortComplex (ModuleCat k) where
  X₁ := TateCohomology X.X₂ 0
  X₂ := TateCohomology X.X₃ 0
  X₃ := TateCohomology X.X₁ 1
  f := map X.g 0
  g := δ₀ hX
  zero := by
    rw [← cancel_epi (ModuleCat.ofHom <| Submodule.mkQ _)]
    have := congr($((groupCohomology.H0ShortComplex₃ hX).zero) ≫ (groupCohomology.isoH1 X.X₁).inv)
    simp_all only [groupCohomology.δ₀, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, zero_comp, map, δ₀, comp_zero]
    convert this using 1

theorem shortComplex₀₃_exact (hX : ShortExact X) : (shortComplex₀₃ hX).Exact := by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x (hx : _ = _)
  induction' x using Quotient.inductionOn' with x
  have h := (moduleCat_exact_iff_ker_sub_range _).1 (groupCohomology.H0ShortComplex₃_exact hX)
  obtain ⟨y, hy⟩ := @h x <| by simpa [← (Iso.eq_comp_inv _).1 (mkQ_comp_δ₀' hX)] using
      congr((groupCohomology.isoH1 X.X₁).hom $hx)
  exact ⟨Submodule.Quotient.mk y, congr(Submodule.Quotient.mk $hy)⟩

noncomputable def shortComplex₁₁ (hX : ShortExact X) : ShortComplex (ModuleCat k) where
  X₁ := TateCohomology X.X₃ 0
  X₂ := TateCohomology X.X₁ 1
  X₃ := TateCohomology X.X₂ 1
  f := δ₀ hX
  g := map X.f 1
  zero := by
    have := (groupCohomology.map_comp_isoH1_hom (MonoidHom.id G) X.f)
    rw [← cancel_epi (ModuleCat.ofHom <| Submodule.mkQ _),
      ← cancel_mono (groupCohomology.isoH1 X.X₂).hom]
    simp_all only [δ₀, map, Category.assoc, comp_zero]
    simpa only [zero_comp] using (groupCohomology.H1ShortComplex₁ hX).zero

theorem shortComplex₁₁_exact (hX : ShortExact X) : (shortComplex₁₁ hX).Exact := by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x (hx : _ = _)
  obtain ⟨y, hy⟩ := (moduleCat_exact_iff_ker_sub_range _).1
     (groupCohomology.mapShortComplex₁_exact hX (i := 0) rfl) hx
  exact ⟨Submodule.mkQ _ ((groupCohomology.isoH0 _).hom y),
    hy ▸ congr($((Iso.eq_inv_comp _).1 (mkQ_comp_δ₀ hX)) y)⟩

noncomputable def shortComplex₁ (hX : ShortExact X) (n : ℤ) : ShortComplex (ModuleCat k) :=
  match n with
  | 0 => shortComplex₀₁ hX
  | 1 => shortComplex₁₁ hX
  | (n + 2 : ℕ) => mapShortComplex₁ hX (i := n + 1) (j := n + 2) rfl
  | -1 => shortComplexNeg₁₁ hX
  | -(n + 2 : ℕ) => mapShortComplex₁ hX (i := n + 2) (j := n + 1) rfl

theorem shortComplex₁_exact (hX : ShortExact X) (n : ℤ) : (shortComplex₁ hX n).Exact :=
  match n with
  | 0 => shortComplex₀₁_exact hX
  | 1 => shortComplex₁₁_exact hX
  | (_ + 2 : ℕ) => groupCohomology.mapShortComplex₁_exact hX rfl
  | -1 => shortComplexNeg₁₁_exact hX
  | -(_ + 2 : ℕ) => groupHomology.mapShortComplex₁_exact hX rfl

noncomputable def shortComplex₃ (hX : ShortExact X) (n : ℤ) : ShortComplex (ModuleCat k) :=
  match n with
  | 0 => shortComplex₀₃ hX
  | (n + 1 : ℕ) => mapShortComplex₃ hX (i := n) (j := n + 1) rfl
  | -1 => shortComplexNeg₁₃ hX
  | -2 => shortComplexNeg₂₃ hX
  | -(n + 3 : ℕ) => mapShortComplex₃ hX (i := n + 2) (j := n + 1) rfl

theorem shortComplex₃_exact (hX : ShortExact X) (n : ℤ) : (shortComplex₃ hX n).Exact :=
  match n with
  | 0 => shortComplex₀₃_exact hX
  | (_ + 1 : ℕ) => groupCohomology.mapShortComplex₃_exact hX rfl
  | -1 => shortComplexNeg₁₃_exact hX
  | -2 => shortComplexNeg₂₃_exact hX
  | -(_ + 3 : ℕ) => groupHomology.mapShortComplex₃_exact hX rfl

end TateCohomology
