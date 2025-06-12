/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.GroupCohomology.Functoriality

/-!
# Long exact sequence in group cohomology

Given a commutative ring `k` and a group `G`, this file shows that a short exact sequence of
`k`-linear `G`-representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` induces a short exact sequence of
complexes of inhomogeneous cochains `0 ⟶ C(X₁) ⟶ C(X₂) ⟶ C(X₃) ⟶ 0`, where `Hⁿ(C(Xᵢ))`
is the `n`th group cohomology of `Xᵢ`.

This allows us to specialize API about long exact sequences to group cohomology.

## Main definitions

* `groupCohomology.δ hX i j hij`: the connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated
  to an exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.

-/

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

namespace groupCohomology

open CategoryTheory ShortComplex

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
  {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

lemma map_cochainsFunctor_shortExact :
    ShortExact (X.map (cochainsFunctor k G)) :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, LinearMap.range_compLeft,
        LinearMap.ker_compLeft, this]
    mono_f := letI := hX.2; cochainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.3; cochainsMap_id_f_map_epi X.g i }

open HomologicalComplex.HomologySequence

/-- The short complex `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)` associated to an exact
sequence of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : i + 1 = j) :=
  (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₂'

variable (X) in
/-- The short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev mapShortComplex₂ (i : ℕ) := X.map (functor k G i)

/-- The short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : i + 1 = j) :=
  (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₁'

/-- Exactness of `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)`. -/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)`. -/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₂ i

/-- Exactness of `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₃ i j hij

/-- The connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. -/
noncomputable abbrev δ (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology X.X₃ i ⟶ groupCohomology X.X₁ j :=
  (map_cochainsFunctor_shortExact hX).δ i j hij

noncomputable abbrev cocyclesMkOfCompEqD {i j : ℕ} {y : (Fin i → G) → X.X₂}
    {x : (Fin j → G) → X.X₁} (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    cocycles X.X₁ j :=
  cocyclesMk x <| by simpa using
    ((map_cochainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa [cochainsMap_id_f_hom_eq_compLeft] using hx) (j + 1))

theorem δ_apply {i j : ℕ} (hij : i + 1 = j)
    (z : (Fin i → G) → X.X₃) (hz : (inhomogeneousCochains X.X₃).d i j z = 0)
    (y : (Fin i → G) → X.X₂) (hy : (cochainsMap (MonoidHom.id G) X.g).f i y = z)
    (x : (Fin j → G) → X.X₁) (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    δ hX i j hij (groupCohomologyπ X.X₃ i <| cocyclesMk z (by subst hij; simpa using hz)) =
      groupCohomologyπ X.X₁ j (cocyclesMkOfCompEqD hX hx) := by
  exact (map_cochainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x
    (by simpa [cochainsMap_id_f_hom_eq_compLeft] using hx) (j + 1) (by simp)

theorem mem_oneCocycles_of_comp_eq_dZero
    {y : X.X₂} {x : G → X.X₁} (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    x ∈ oneCocycles X.X₁ := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1, LinearMap.compLeft]

theorem δ₀_apply (z : X.X₃.ρ.invariants) (y : X.X₂)
    (hy : X.g.hom y = z) (x : G → X.X₁) (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    δ hX 0 1 rfl ((H0Iso X.X₃).inv z) = groupCohomologyπ X.X₁ 1
      ((isoOneCocycles X.X₁).inv ⟨x, mem_oneCocycles_of_comp_eq_dZero hX hx⟩) := by
  simpa [H0Iso, ← cocyclesMk_1_eq X.X₁, ← cocyclesMk_0_eq z] using
    δ_apply hX rfl ((zeroCochainsIso X.X₃).inv z.1) (by simp) ((zeroCochainsIso X.X₂).inv y)
    (by ext; simp [← hy, zeroCochainsIso]) ((oneCochainsIso X.X₁).inv x) <| by
      ext g
      simpa [← hx] using congr_fun (congr($((CommSq.vert_inv
        ⟨cochainsMap_f_1_comp_oneCochainsIso (MonoidHom.id G) X.f⟩).w) x)) g

theorem mem_twoCocycles_of_comp_eq_dOne
    {y : G → X.X₂} {x : G × G → X.X₁} (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    x ∈ twoCocycles X.X₁ := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH2 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH2, LinearMap.compLeft]

set_option trace.profiler true in
theorem δ₁_apply (z : oneCocycles X.X₃) (y : G → X.X₂)
    (hy : X.g.hom ∘ y = z) (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    δ hX 1 2 rfl (groupCohomologyπ _ 1 <| (isoOneCocycles X.X₃).inv z) = groupCohomologyπ X.X₁ _
      ((isoTwoCocycles X.X₁).inv ⟨x, mem_twoCocycles_of_comp_eq_dOne hX hx⟩) := by
  simpa [H0Iso, ← cocyclesMk_2_eq X.X₁, ← cocyclesMk_1_eq X.X₃] using
    δ_apply hX rfl ((oneCochainsIso X.X₃).inv z) (by simp [oneCocycles.dOne_apply z])
    ((oneCochainsIso X.X₂).inv y) (by ext; simp [oneCochainsIso, ← hy])
    ((twoCochainsIso X.X₁).inv x) <| by
      ext g
      simpa [← hx] using congr_fun (congr($((CommSq.vert_inv
        ⟨cochainsMap_f_2_comp_twoCochainsIso (MonoidHom.id G) X.f⟩).w) x)) g

open Limits

theorem epi_δ_of_isZero (n : ℕ) (h : IsZero (groupCohomology X.X₂ (n + 1))) :
    Epi (δ hX n (n + 1) rfl) := SnakeInput.epi_δ _ h

end groupCohomology
