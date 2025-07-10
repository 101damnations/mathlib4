import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Coinduced


universe v u
open CategoryTheory Limits

section
variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
variable {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

variable (C)

abbrev ShortExactProperty (C : Type*) [Category C] [HasZeroMorphisms C] :
    ObjectProperty (ShortComplex C) := fun X => X.ShortExact

abbrev ShortExactCat (C : Type*) [Category C] [HasZeroMorphisms C] :=
  ObjectProperty.FullSubcategory (ShortExactProperty C)

open HomologicalComplex

noncomputable def snakeInputFunctor (i j : ι) (hij : c.Rel i j) :
    ShortExactCat (HomologicalComplex C c) ⥤ ShortComplex.SnakeInput C where
  obj X := HomologySequence.snakeInput X.2 i j hij
  map {X Y} f := HomologySequence.mapSnakeInput f X.2 Y.2 i j hij
  map_id _ := by ext <;> simp [ObjectProperty.FullSubcategory.id_def]
  map_comp _ _ := by ext <;> simp [ObjectProperty.FullSubcategory.comp_def]

noncomputable def δFunctor : ShortComplex.SnakeInput C ⥤ Arrow C where
  obj X := X.δ
  map f := Arrow.homMk f.f₀.τ₃ f.f₃.τ₁ (ShortComplex.SnakeInput.naturality_δ f).symm
  map_id X := by ext <;> simp
  map_comp _ _ := by ext <;> simp

end
section

open ShortComplex

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

variable (F) in
def mapShortExact [Abelian C] [Abelian D] [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ShortExactCat C ⥤ ShortExactCat D :=
  ObjectProperty.lift _ (CategoryTheory.ObjectProperty.ι _ ⋙ F.mapShortComplex) fun X => by
    have := (F.exact_tfae.out 3 0).1
    exact this ⟨‹_›, ‹_›⟩ _ X.2

@[simps!]
noncomputable def unitShortExact
    [Preadditive C] [CategoryWithHomology C] [F.Faithful] [HasCokernels C] :
    C ⥤ ShortExactCat C where
  obj X := {
    obj := mk (adj.unit.app X) _ (cokernel.condition _)
    property := { exact := exact_of_g_is_cokernel _ <| cokernelIsCokernel _ }}
  map f := homMk f ((F ⋙ G).map f) (cokernel.map _ _ _ _ (w := (adj.unit.naturality f).symm))
    (by simp) (by simp)
  map_id _ := by
    apply ShortComplex.hom_ext <;>
    simp [ObjectProperty.FullSubcategory.id_def, ← cancel_epi (cokernel.π _)]
  map_comp _ _ := by
    apply ShortComplex.hom_ext <;>
    simp [ObjectProperty.FullSubcategory.comp_def, ← cancel_epi (cokernel.π _)]

@[simps!]
noncomputable def counitShortExact
    [Preadditive D] [CategoryWithHomology D] [G.Faithful] [HasKernels D] :
    D ⥤ ShortExactCat D where
  obj X := {
    obj := mk _ (adj.counit.app X) (kernel.condition _)
    property := { exact := exact_of_f_is_kernel _ <| kernelIsKernel _ }}
  map f := homMk (kernel.map _ _ _ _ (w := (adj.counit.naturality f).symm))
    ((G ⋙ F).map f) f (by simp) (by simp)
  map_id _ := by
    apply ShortComplex.hom_ext <;>
    simp [ObjectProperty.FullSubcategory.id_def, ← cancel_mono (kernel.ι _)]
  map_comp _ _ := by
    apply ShortComplex.hom_ext <;>
    simp [ObjectProperty.FullSubcategory.comp_def, ← cancel_mono (kernel.ι _)]

end

namespace Rep

open ShortComplex

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

variable (k G) in
noncomputable abbrev coindPUnit : Rep k G ⥤ Rep k G :=
  Action.res (ModuleCat k) (1 : PUnit →* G) ⋙ coindFunctor k 1

noncomputable def dimShiftingComplex :
    Rep k G ⥤ ShortExactCat (CochainComplex (ModuleCat k) ℕ) :=
  unitShortExact (resCoindAdjunction k (1 : PUnit →* G)) ⋙
    mapShortExact (groupCohomology.cochainsFunctor k G)

noncomputable def δFunctor (i j : ℕ) (hij : i + 1 = j) :
    ShortExactCat (Rep k G) ⥤ Arrow (ModuleCat k) :=
  mapShortExact (groupCohomology.cochainsFunctor k G) ⋙
    snakeInputFunctor (ModuleCat k) i j hij ⋙ _root_.δFunctor (ModuleCat k)



end Rep
