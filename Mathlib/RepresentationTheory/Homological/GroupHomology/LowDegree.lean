/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
# The low-degree homology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file will contain specialised API for
the cycles and group homology  of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.
In `RepresentationTheory/Homological/GroupHomology/Basic.lean`, we define the `n`th group homology
of `A` to be the homology of a complex `inhomogeneousChains A`, whose objects are
`(Fin n →₀ G) → A`; this is unnecessarily unwieldy in low degree. Here, meanwhile, we will define
the one and two cycles and boundaries as submodules of `G →₀ A` and `G × G →₀ A`, and provide maps
to `H1` and `H2`.

Given an additive abelian group `A` with an appropriate scalar action of `G`, we provide support
for turning a finsupp `f : G →₀ A` satisfying the 1-cycle identity into an element of the
`oneCycles` of the representation on `A` corresponding to the scalar action. We also do this for
0-boundaries, 1-boundaries, 2-cycles and 2-boundaries.

-/

universe v u

noncomputable section

open CategoryTheory Limits Representation Rep Finsupp

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

namespace groupHomology

section Chains
variable [DecidableEq G]

/-- The 0th object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `A` as a `k`-module. -/
def zeroChainsIso : (inhomogeneousChains A).X 0 ≅ A.V :=
  (LinearEquiv.finsuppUnique _ _ _).toModuleIso

/-- The 1st object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G →₀ A` as a `k`-module. -/
def oneChainsIso : (inhomogeneousChains A).X 1 ≅ ModuleCat.of k (G →₀ A) :=
  (Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)).toModuleIso

/-- The 2nd object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G² →₀ A` as a `k`-module. -/
def twoChainsIso : (inhomogeneousChains A).X 2 ≅ ModuleCat.of k (G × G →₀ A) :=
  (Finsupp.domLCongr (piFinTwoEquiv fun _ => G)).toModuleIso

/-- The 3rd object in the complex of inhomogeneous chains of `A : Rep k G` is isomorphic
to `G³ → A` as a `k`-module. -/
def threeChainsIso : (inhomogeneousChains A).X 3 ≅ ModuleCat.of k (G × G × G →₀ A) :=
  (Finsupp.domLCongr ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso

end Chains

section Differentials

/-- The 0th differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G →₀ A) → A`. It sends `single g a ↦ ρ_A(g⁻¹)(a) - a.` -/
def dZero : ModuleCat.of k (G →₀ A) ⟶ A.V :=
  ModuleCat.ofHom <| lsum k fun g => A.ρ g⁻¹ - LinearMap.id

@[simp]
theorem dZero_single (g : G) (a : A) : dZero A (single g a) = A.ρ g⁻¹ a - a := by
  simp [dZero]

theorem dZero_single_one (a : A) : dZero A (single 1 a) = 0 := by
  simp [dZero]

theorem dZero_single_inv (g : G) (a : A) :
    dZero A (single g⁻¹ a) = - dZero A (single g (A.ρ g a)) := by
  simp [dZero]

theorem range_dZero_eq_coinvariantsKer :
    LinearMap.range (dZero A).hom = Coinvariants.ker A.ρ := by
  symm
  apply Submodule.span_eq_of_le
  · rintro _ ⟨x, rfl⟩
    use single x.1⁻¹ x.2
    simp [dZero]
  · rintro x ⟨y, hy⟩
    induction' y using Finsupp.induction with _ _ _ _ _ h generalizing x
    · simp [← hy]
    · simpa [← hy, add_sub_add_comm, sum_add_index, dZero_single (G := G)]
        using Submodule.add_mem _ (Coinvariants.mem_ker_of_eq _ _ _ rfl) (h rfl)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma dZero_comp_mk : dZero A ≫ ModuleCat.ofHom (Coinvariants.mk A.ρ) = 0 := by
  ext
  simp [dZero]

/-- The 0th differential in the complex of inhomogeneous chains of a `G`-representation `A` as a
linear map into the `k`-submodule of `A` spanned by elements of the form
`ρ(g)(x) - x, g ∈ G, x ∈ A`. -/
def oneChainsToCoinvariantsKer :
    ModuleCat.of k (G →₀ A) ⟶ ModuleCat.of k (Coinvariants.ker A.ρ) :=
  ModuleCat.ofHom <| (dZero A).hom.codRestrict _ <|
    range_dZero_eq_coinvariantsKer A ▸ LinearMap.mem_range_self _

@[simp]
theorem dZero_eq_zero_of_isTrivial [A.IsTrivial] : dZero A = 0 := by
  ext
  simp [dZero]

/-- The 1st differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G² →₀ A) → (G →₀ A)`. It sends `a·(g₁, g₂) ↦ ρ_A(g₁⁻¹)(a)·g₂ - a·g₁g₂ + a·g₁`. -/
def dOne : ModuleCat.of k (G × G →₀ A) ⟶ ModuleCat.of k (G →₀ A) :=
  ModuleCat.ofHom <| lsum k fun g => lsingle g.2 ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2) + lsingle g.1

variable {A}

@[simp]
lemma dOne_single (g : G × G) (a : A) :
    dOne A (single g a) = single g.2 (A.ρ g.1⁻¹ a) - single (g.1 * g.2) a + single g.1 a := by
  simp [dOne]

lemma dOne_single_one_fst (g : G) (a : A) :
    dOne A (single (1, g) a) = single 1 a := by
  simp [dOne]

lemma dOne_single_one_snd (g : G) (a : A) :
    dOne A (single (g, 1) a) = single 1 (A.ρ g⁻¹ a) := by
  simp [dOne]

lemma dOne_single_inv_self_ρ_sub_self_inv (g : G) (a : A) :
    dOne A (single (g⁻¹, g) (A.ρ g⁻¹ a) - single (g, g⁻¹) a) =
      single 1 a - single 1 (A.ρ g⁻¹ a) := by
  simp only [map_sub, dOne_single (G := G), inv_inv, self_inv_apply, inv_mul_cancel,
    mul_inv_cancel]
  abel

lemma dOne_single_self_inv_ρ_sub_inv_self (g : G) (a : A) :
    dOne A (single (g, g⁻¹) (A.ρ g a) - single (g⁻¹, g) a) =
      single 1 a - single 1 (A.ρ g a) := by
  simp only [map_sub, dOne_single (G := G), inv_self_apply, mul_inv_cancel, inv_inv,
    inv_mul_cancel]
  abel

lemma dOne_single_ρ_add_single_inv_mul (g h : G) (a : A) :
    dOne A (single (g, h) (A.ρ g a) + single (g⁻¹, g * h) a) =
      single g (A.ρ g a) + single g⁻¹ a := by
  simp only [map_add, dOne_single (G := G), inv_self_apply, inv_inv, inv_mul_cancel_left]
  abel

lemma dOne_single_inv_mul_ρ_add_single (g h : G) (a : A) :
    dOne A (single (g⁻¹, g * h) (A.ρ g⁻¹ a) + single (g, h) a) =
      single g⁻¹ (A.ρ g⁻¹ a) + single g a := by
  simp only [map_add, dOne_single (G := G), inv_inv, self_inv_apply, inv_mul_cancel_left]
  abel

variable (A) in
/-- The 2nd differential in the complex of inhomogeneous chains of `A : Rep k G`, as a
`k`-linear map `(G³ →₀ A) → (G² →₀ A)`. It sends
`a·(g₁, g₂, g₃) ↦ ρ_A(g₁⁻¹)(a)·(g₂, g₃) - a·(g₁g₂, g₃) + a·(g₁, g₂g₃) - a·(g₁, g₂)`. -/
def dTwo : ModuleCat.of k (G × G × G →₀ A) ⟶ ModuleCat.of k (G × G →₀ A) :=
  ModuleCat.ofHom <| lsum k fun g =>
    lsingle (g.2.1, g.2.2) ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2.1, g.2.2) +
    lsingle (g.1, g.2.1 * g.2.2) - lsingle (g.1, g.2.1)

@[simp]
lemma dTwo_single (g : G × G × G) (a : A) :
    dTwo A (single g a) = single (g.2.1, g.2.2) (A.ρ g.1⁻¹ a) - single (g.1 * g.2.1, g.2.2) a +
      single (g.1, g.2.1 * g.2.2) a - single (g.1, g.2.1) a := by
  simp [dTwo]

lemma dTwo_single_one_fst (g h : G) (a : A) :
    dTwo A (single (1, g, h) a) = single (1, g * h) a - single (1, g) a := by
  simp [dTwo]

lemma dTwo_single_one_snd (g h : G) (a : A) :
    dTwo A (single (g, 1, h) a) = single (1, h) (A.ρ g⁻¹ a) - single (g, 1) a := by
  simp [dTwo]

lemma dTwo_single_one_thd (g h : G) (a : A) :
    dTwo A (single (g, h, 1) a) = single (h, 1) (A.ρ g⁻¹ a) - single (g * h, 1) a := by
  simp [dTwo]

variable (A) [DecidableEq G]

/-- Let `C(G, A)` denote the complex of inhomogeneous chains of `A : Rep k G`. This lemma
says `dZero` gives a simpler expression for the 0th differential: that is, the following
square commutes:
```
  C₁(G, A) ---d₀---> C₀(G, A)
    |                  |
    |                  |
    |                  |
    v                  v
  (G →₀ A) --dZero --> A
```
where the vertical arrows are `oneChainsIso` and `zeroChainsIso` respectively.
-/
theorem comp_dZero_eq :
    (oneChainsIso A).hom ≫ dZero A = (inhomogeneousChains A).d 1 0 ≫ (zeroChainsIso A).hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simp [inhomogeneousChains.d_def, zeroChainsIso, oneChainsIso, dZero_single (G := G),
      Unique.eq_default (α := Fin 0 → G), sub_eq_add_neg, inhomogeneousChains.d_single (G := G)]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_dZero_comp_inv :
    (oneChainsIso A).inv ≫ (inhomogeneousChains A).d 1 0 = dZero A ≫ (zeroChainsIso A).inv :=
  (CommSq.horiz_inv ⟨comp_dZero_eq A⟩).w

/-- Let `C(G, A)` denote the complex of inhomogeneous chains of `A : Rep k G`. This lemma
says `dOne` gives a simpler expression for the 1st differential: that is, the following
square commutes:
```
  C₂(G, A) ---d₁-----> C₁(G, A)
    |                      |
    |                      |
    |                      |
    v                      v
  (G² →₀ A) --dOne--->  (G →₀ A)
```
where the vertical arrows are `twoChainsIso` and `oneChainsIso` respectively.
-/

theorem comp_dOne_eq :
    (twoChainsIso A).hom ≫ dOne A = (inhomogeneousChains A).d 2 1 ≫ (oneChainsIso A).hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simp [inhomogeneousChains.d_def, oneChainsIso, add_assoc, twoChainsIso, dOne_single (G := G),
      -Finsupp.domLCongr_apply, domLCongr_single, sub_eq_add_neg, Fin.contractNth,
      inhomogeneousChains.d_single (G := G)]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_dOne_comp_inv :
    (twoChainsIso A).inv ≫ (inhomogeneousChains A).d 2 1 = dOne A ≫ (oneChainsIso A).inv :=
  (CommSq.horiz_inv ⟨comp_dOne_eq A⟩).w

/-- Let `C(G, A)` denote the complex of inhomogeneous chains of `A : Rep k G`. This lemma
says `dTwo` gives a simpler expression for the 2nd differential: that is, the following
square commutes:
```
   C₃(G, A) -----d₂---> C₂(G, A)
    |                      |
    |                      |
    |                      |
    v                      v
  (G³ →₀ A) --dTwo--> (G² →₀ A)
```
where the vertical arrows are `threeChainsIso` and `twoChainsIso` respectively.
-/
theorem comp_dTwo_eq :
    (threeChainsIso A).hom ≫ dTwo A = (inhomogeneousChains A).d 3 2 ≫ (twoChainsIso A).hom :=
  ModuleCat.hom_ext <| lhom_ext fun _ _ => by
    simp [inhomogeneousChains.d_def, twoChainsIso, pow_succ, threeChainsIso,
      -domLCongr_apply, domLCongr_single, dTwo, Fin.sum_univ_three,
      Fin.contractNth, Fin.tail_def, sub_eq_add_neg, add_assoc,
      inhomogeneousChains.d_single (G := G), add_rotate' (-(single (_ * _, _) _)),
      add_left_comm (single (_, _ * _) _)]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_dTwo_comp_inv :
    (threeChainsIso A).inv ≫ (inhomogeneousChains A).d 3 2 = dTwo A ≫ (twoChainsIso A).inv :=
  (CommSq.horiz_inv ⟨comp_dTwo_eq A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem dOne_comp_dZero : dOne A ≫ dZero A = 0 := by
  ext x g
  simp [dZero, dOne, sum_add_index, sum_sub_index, sub_sub_sub_comm, add_sub_add_comm]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem dTwo_comp_dOne : dTwo A ≫ dOne A = 0 := by
  simp [← cancel_mono (oneChainsIso A).inv, ← eq_dOne_comp_inv, ← eq_dTwo_comp_inv_assoc]

end Differentials

section Cycles

/-- The 1-cycles `Z₁(G, A)` of `A : Rep k G`, defined as the kernel of the map
`(G →₀ A) → A` sending `single g a ↦ ρ_A(g⁻¹)(a) - a`. -/
def oneCycles : Submodule k (G →₀ A) := LinearMap.ker (dZero A).hom

/-- The 2-cycles `Z₂(G, A)` of `A : Rep k G`, defined as the kernel of the map
`(G² →₀ A) → (G →₀ A)` sending `a·(g₁, g₂) ↦ ρ_A(g₁⁻¹)(a)·g₂ - a·g₁g₂ + a·g₁`. -/
def twoCycles : Submodule k (G × G →₀ A) := LinearMap.ker (dOne A).hom

variable {A}

theorem mem_oneCycles_iff (x : G →₀ A) :
    x ∈ oneCycles A ↔ x.sum (fun g a => A.ρ g⁻¹ a) = x.sum (fun _ a => a) := by
  show x.sum (fun g a => A.ρ g⁻¹ a - a) = 0 ↔ _
  rw [sum_sub, sub_eq_zero]

theorem single_mem_oneCycles_iff (g : G) (a : A) :
    single g a ∈ oneCycles A ↔ A.ρ g a = a := by
  simp [mem_oneCycles_iff, ← (A.ρ.apply_bijective g).1.eq_iff (a := A.ρ g⁻¹ a), eq_comm]

theorem single_mem_oneCycles_of_mem_invariants (g : G) (a : A) (ha : a ∈ A.ρ.invariants) :
    single g a ∈ oneCycles A :=
  (single_mem_oneCycles_iff g a).2 (ha g)

theorem dOne_apply_mem_oneCycles [DecidableEq G] (x : G × G →₀ A) :
    dOne A x ∈ oneCycles A :=
  congr($(dOne_comp_dZero A) x)

variable (A) in
theorem oneCycles_eq_top_of_isTrivial [A.IsTrivial] : oneCycles A = ⊤ := by
  rw [oneCycles, dZero_eq_zero_of_isTrivial, ModuleCat.hom_zero, LinearMap.ker_zero]

variable (A) in
/-- The natural inclusion `Z₁(G, A) ≅ C₁(G, A)` is an isomorphism when the representation
on `A` is trivial. -/
abbrev oneCyclesIsoOfIsTrivial [A.IsTrivial] :
    ModuleCat.of k (oneCycles A) ≅ ModuleCat.of k (G →₀ A) :=
  (LinearEquiv.ofTop _ (oneCycles_eq_top_of_isTrivial A)).toModuleIso

theorem mem_twoCycles_iff (x : G × G →₀ A) :
    x ∈ twoCycles A ↔ x.sum (fun g a => single g.2 (A.ρ g.1⁻¹ a) + single g.1 a) =
      x.sum (fun g a => single (g.1 * g.2) a) := by
  show x.sum (fun g a => _) = 0 ↔ _
  simp [sub_add_eq_add_sub, sum_sub_index, sub_eq_zero]

theorem single_mem_twoCycles_iff_inv (g : G × G) (a : A) :
    single g a ∈ twoCycles A ↔ single g.2 (A.ρ g.1⁻¹ a) + single g.1 a = single (g.1 * g.2) a := by
  simp [mem_twoCycles_iff]

theorem single_mem_twoCycles_iff (g : G × G) (a : A) :
    single g a ∈ twoCycles A ↔
      single (g.1 * g.2) (A.ρ g.1 a) = single g.2 a + single g.1 (A.ρ g.1 a) := by
  rw [← (mapRange_injective (α := G) _ (map_zero _) (A.ρ.apply_bijective g.1⁻¹).1).eq_iff]
  simp [mem_twoCycles_iff, mapRange_add, eq_comm]

theorem dTwo_apply_mem_twoCycles [DecidableEq G] (x : G × G × G →₀ A) :
    dTwo A x ∈ twoCycles A :=
  congr($(dTwo_comp_dOne A) x)

end Cycles

section Boundaries

/-- The 1-boundaries `B₁(G, A)` of `A : Rep k G`, defined as the image of the map
`(G² →₀ A) → (G →₀ A)` sending `a·(g₁, g₂) ↦ ρ_A(g₁⁻¹)(a)·g₂ - a·g₁g₂ + a·g₁`. -/
def oneBoundaries : Submodule k (G →₀ A) :=
  LinearMap.range (dOne A).hom

/-- The 2-boundaries `B₂(G, A)` of `A : Rep k G`, defined as the image of the map
`(G³ →₀ A) → (G² →₀ A)` sending
`a·(g₁, g₂, g₃) ↦ ρ_A(g₁⁻¹)(a)·(g₂, g₃) - a·(g₁g₂, g₃) + a·(g₁, g₂g₃) - a·(g₁, g₂)`. -/
def twoBoundaries : Submodule k (G × G →₀ A) :=
  LinearMap.range (dTwo A).hom

variable {A}

section

variable [DecidableEq G]

lemma mem_oneCycles_of_mem_oneBoundaries (f : G →₀ A) (h : f ∈ oneBoundaries A) :
    f ∈ oneCycles A := by
  rcases h with ⟨x, rfl⟩
  exact dOne_apply_mem_oneCycles x

variable (A) in
lemma oneBoundaries_le_oneCycles : oneBoundaries A ≤ oneCycles A :=
  mem_oneCycles_of_mem_oneBoundaries

variable (A) in
/-- Natural inclusion `B₁(G, A) →ₗ[k] Z₁(G, A)`. -/
abbrev oneBoundariesToOneCycles : oneBoundaries A →ₗ[k] oneCycles A :=
  Submodule.inclusion (oneBoundaries_le_oneCycles A)

@[simp]
lemma oneBoundariesToOneCycles_apply (x : oneBoundaries A) :
    (oneBoundariesToOneCycles A x).1 = x.1 := rfl

end

theorem single_one_mem_oneBoundaries (a : A) :
    single 1 a ∈ oneBoundaries A := by
  use single (1, 1) a
  simp [dOne]

theorem single_ρ_self_add_single_inv_mem_oneBoundaries (g : G) (a : A) :
    single g (A.ρ g a) + single g⁻¹ a ∈ oneBoundaries A := by
  rw [← dOne_single_ρ_add_single_inv_mul g 1]
  exact Set.mem_range_self _

theorem single_inv_ρ_self_add_single_mem_oneBoundaries (g : G) (a : A) :
    single g⁻¹ (A.ρ g⁻¹ a) + single g a ∈ oneBoundaries A := by
  rw [← dOne_single_inv_mul_ρ_add_single g 1]
  exact Set.mem_range_self _

section

variable [DecidableEq G]

lemma mem_twoCycles_of_mem_twoBoundaries (x : G × G →₀ A) (h : x ∈ twoBoundaries A) :
    x ∈ twoCycles A := by
  rcases h with ⟨x, rfl⟩
  exact dTwo_apply_mem_twoCycles x

variable (A) in
lemma twoBoundaries_le_twoCycles : twoBoundaries A ≤ twoCycles A :=
  mem_twoCycles_of_mem_twoBoundaries

variable (A) in
/-- Natural inclusion `B₂(G, A) →ₗ[k] Z₂(G, A)`. -/
abbrev twoBoundariesToTwoCycles [DecidableEq G] : twoBoundaries A →ₗ[k] twoCycles A :=
  Submodule.inclusion (twoBoundaries_le_twoCycles A)

@[simp]
lemma twoBoundariesToTwoCycles_apply (x : twoBoundaries A) :
    (twoBoundariesToTwoCycles A x).1 = x.1 := rfl

end

lemma single_one_fst_sub_single_one_fst_mem_twoBoundaries (g h : G) (a : A) :
    single (1, g * h) a - single (1, g) a ∈ twoBoundaries A := by
  use single (1, g, h) a
  simp [dTwo]

lemma single_one_fst_sub_single_one_snd_mem_twoBoundaries (g h : G) (a : A) :
    single (1, h) (A.ρ g⁻¹ a) - single (g, 1) a ∈ twoBoundaries A := by
  use single (g, 1, h) a
  simp [dTwo]

lemma single_one_snd_sub_single_one_fst_mem_twoBoundaries (g h : G) (a : A) :
    single (g, 1) (A.ρ g a) - single (1, h) a ∈ twoBoundaries A := by
  use single (g, 1, h) (A.ρ g (-a))
  simp [dTwo_single (G := G)]

lemma single_one_snd_sub_single_one_snd_mem_twoBoundaries (g h : G) (a : A) :
    single (h, 1) (A.ρ g⁻¹ a) - single (g * h, 1) a ∈ twoBoundaries A := by
  use single (g, h, 1) a
  simp [dTwo]

end Boundaries

section IsCycle

section

variable {G A : Type*} [Mul G] [Inv G] [AddCommGroup A] [SMul G A]

/-- A finsupp `∑ aᵢ·gᵢ : G →₀ A` satisfies the 1-cycle condition if `∑ gᵢ⁻¹ • aᵢ = ∑ aᵢ`. -/
def IsOneCycle (x : G →₀ A) : Prop := x.sum (fun g a => g⁻¹ • a) = x.sum (fun _ a => a)

/-- A finsupp `∑ aᵢ·(gᵢ, hᵢ) : G × G →₀ A` satisfies the 2-cycle condition if
`∑ (gᵢ⁻¹ • aᵢ)·hᵢ + aᵢ·gᵢ = ∑ aᵢ·gᵢhᵢ`. -/
def IsTwoCycle (x : G × G →₀ A) : Prop :=
  x.sum (fun g a => single g.2 (g.1⁻¹ • a) + single g.1 a) =
    x.sum (fun g a => single (g.1 * g.2) a)

end

section

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

@[simp]
theorem single_isOneCycle_iff (g : G) (a : A) :
    IsOneCycle (single g a) ↔ g • a = a := by
  rw [← (MulAction.bijective g⁻¹).1.eq_iff]
  simp [IsOneCycle, eq_comm]

theorem single_isOneCycle_of_mem_fixedPoints
    (g : G) (a : A) (ha : a ∈ MulAction.fixedPoints G A) :
    IsOneCycle (single g a) := by
  simp_all [IsOneCycle]

theorem single_isTwoCycle_iff_inv (g : G × G) (a : A) :
    IsTwoCycle (single g a) ↔
      single g.2 (g.1⁻¹ • a) + single g.1 a = single (g.1 * g.2) a := by
  simp [IsTwoCycle]

@[simp]
theorem single_isTwoCycle_iff (g : G × G) (a : A) :
    IsTwoCycle (single g a) ↔
      single g.2 a + single g.1 (g.1 • a) = single (g.1 * g.2) (g.1 • a) := by
  rw [← (Finsupp.mapRange_injective (α := G) _ (smul_zero _) (MulAction.bijective g.1⁻¹).1).eq_iff]
  simp [mapRange_add, IsTwoCycle]

end

end IsCycle

section IsBoundary

section

variable {G A : Type*} [Mul G] [Inv G] [AddCommGroup A] [SMul G A]

variable (G) in
/-- A term `x : A` satisfies the 0-boundary condition if there exists a finsupp
`∑ aᵢ·gᵢ : G →₀ A` such that `∑ gᵢ⁻¹ • aᵢ - aᵢ = x`. -/
def IsZeroBoundary (a : A) : Prop :=
  ∃ (x : G →₀ A), x.sum (fun g a => g⁻¹ • a - a) = a

/-- A finsupp `x : G →₀ A` satisfies the 1-boundary condition if there's a finsupp
`∑ aᵢ·(gᵢ, hᵢ) : G × G →₀ A` such that `∑ (gᵢ⁻¹ • aᵢ)·hᵢ - aᵢ·gᵢhᵢ + aᵢ·gᵢ = x`. -/
def IsOneBoundary (x : G →₀ A) : Prop :=
  ∃ y : G × G →₀ A, y.sum
    (fun g a => single g.2 (g.1⁻¹ • a) - single (g.1 * g.2) a + single g.1 a) = x

/-- A finsupp `x : G × G →₀ A` satsfies the 2-boundary condition if there's a finsupp
`∑ aᵢ·(gᵢ, hᵢ, jᵢ) : G × G × G →₀ A` such that
`∑ (gᵢ⁻¹ • aᵢ)·(hᵢ, jᵢ) - aᵢ·(gᵢhᵢ, jᵢ) + aᵢ·(gᵢ, hᵢjᵢ) - aᵢ·(gᵢ, hᵢ) = x.` -/
def IsTwoBoundary (x : G × G →₀ A) : Prop :=
  ∃ y : G × G × G →₀ A, y.sum (fun g a => single (g.2.1, g.2.2) (g.1⁻¹ • a) -
    single (g.1 * g.2.1, g.2.2) a + single (g.1, g.2.1 * g.2.2) a - single (g.1, g.2.1) a) = x

end
section

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

variable (G) in
theorem isZeroBoundary_iff (a : A) :
    IsZeroBoundary G a ↔ ∃ x : G →₀ A, x.sum (fun g a => g • a - a) = a := by
  constructor
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (- (g⁻¹ • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (- (g • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]

theorem isOneBoundary_iff (x : G →₀ A) :
    IsOneBoundary x ↔ ∃ y : G × G →₀ A, y.sum
      (fun g a => single g.2 a - single (g.1 * g.2) (g.1 • a) + single g.1 (g.1 • a)) = x := by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]

theorem isTwoBoundary_iff (x : G × G →₀ A) :
    IsTwoBoundary x ↔ ∃ y : G × G × G →₀ A, y.sum
      (fun g a => single (g.2.1, g.2.2) a - single (g.1 * g.2.1, g.2.2) (g.1 • a) +
        single (g.1, g.2.1 * g.2.2) (g.1 • a) - single (g.1, g.2.1) (g.1 • a)) = x := by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]

end
end IsBoundary

section ofDistribMulAction

variable {k G A : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a term
`x : A` satisfying the 0-boundary condition, produces an element of the kernel of the quotient map
`A → A_G` for the representation on `A` induced by the `DistribMulAction`. -/
@[simps]
def coinvariantsKerOfIsZeroBoundary (x : A) (hx : IsZeroBoundary G x) :
    Coinvariants.ker (Representation.ofDistribMulAction k G A) :=
  ⟨x, by
    rcases (isZeroBoundary_iff G x).1 hx with ⟨y, rfl⟩
    exact Submodule.finsuppSum_mem _ _ _ _ fun g _ => Coinvariants.mem_ker_of_eq g (y g) _ rfl⟩

theorem isZeroBoundary_of_mem_coinvariantsKer [DecidableEq G]
    (x : A) (hx : x ∈ Coinvariants.ker (Representation.ofDistribMulAction k G A)) :
    IsZeroBoundary G x :=
  Submodule.span_induction (fun _ ⟨g, hg⟩ => ⟨single g.1⁻¹ g.2, by simp_all⟩) ⟨0, by simp⟩
    (fun _ _ _ _ ⟨X, hX⟩ ⟨Y, hY⟩ => ⟨X + Y, by simp_all [sum_add_index, add_sub_add_comm]⟩)
    (fun r _ _ ⟨X, hX⟩ => ⟨r • X, by simp [← hX, sum_smul_index', smul_comm, smul_sub, smul_sum]⟩)
    hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G →₀ A` satisfying the 1-cycle condition, produces a 1-cycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
def oneCyclesOfIsOneCycle (x : G →₀ A) (hx : IsOneCycle x) :
    oneCycles (Rep.ofDistribMulAction k G A) :=
  ⟨x, (mem_oneCycles_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

theorem isOneCycle_of_mem_oneCycles
    (x : G →₀ A) (hx : x ∈ oneCycles (Rep.ofDistribMulAction k G A)) :
    IsOneCycle x := by
  simpa using (mem_oneCycles_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G →₀ A` satisfying the 1-boundary condition, produces a 1-boundary for the representation
on `A` induced by the `DistribMulAction`. -/
@[simps]
def oneBoundariesOfIsOneBoundary (x : G →₀ A) (hx : IsOneBoundary x) :
    oneBoundaries (Rep.ofDistribMulAction k G A) :=
  ⟨x, hx⟩

theorem isOneBoundary_of_mem_oneBoundaries
    (x : G →₀ A) (hx : x ∈ oneBoundaries (Rep.ofDistribMulAction k G A)) :
    IsOneBoundary x := hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G × G →₀ A` satisfying the 2-cycle condition, produces a 2-cycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
def twoCyclesOfIsTwoCycle (x : G × G →₀ A) (hx : IsTwoCycle x) :
    twoCycles (Rep.ofDistribMulAction k G A) :=
  ⟨x, (mem_twoCycles_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

theorem isTwoCycle_of_mem_twoCycles
    (x : G × G →₀ A) (hx : x ∈ twoCycles (Rep.ofDistribMulAction k G A)) :
    IsTwoCycle x := (mem_twoCycles_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G × G →₀ A` satisfying the 2-boundary condition, produces a 2-boundary for the
representation on `A` induced by the `DistribMulAction`. -/
@[simps]
def twoBoundariesOfIsTwoBoundary (x : G × G →₀ A) (hx : IsTwoBoundary x) :
    twoBoundaries (Rep.ofDistribMulAction k G A) :=
  ⟨x, hx⟩

theorem isTwoBoundary_of_mem_twoBoundaries
    (x : G × G →₀ A) (hx : x ∈ twoBoundaries (Rep.ofDistribMulAction k G A)) :
    IsTwoBoundary x := hx

end ofDistribMulAction
end groupHomology
