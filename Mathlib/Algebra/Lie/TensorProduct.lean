/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Abelian
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensor products of Lie modules

Tensor products of Lie modules carry natural Lie module structures.

## Tags

lie module, tensor product, universal property
-/

universe u v w w₁ w₂ w₃

variable {R : Type u} [CommRing R]

open LieModule

namespace TensorProduct

open scoped TensorProduct

namespace LieModule

variable {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} {Q : Type w₃}
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]
variable [AddCommGroup Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]

attribute [local ext] TensorProduct.ext

/-- It is useful to define the bracket via this auxiliary function so that we have a type-theoretic
expression of the fact that `L` acts by linear endomorphisms. It simplifies the proofs in
`lieRingModule` below. -/
def hasBracketAux (x : L) : Module.End R (M ⊗[R] N) :=
  (toEnd R L M x).rTensor N + (toEnd R L N x).lTensor M

/-- The tensor product of two Lie modules is a Lie ring module. -/
instance lieRingModule : LieRingModule L (M ⊗[R] N) where
  bracket x := hasBracketAux x
  add_lie x y t := by
    simp only [hasBracketAux, LinearMap.lTensor_add, LinearMap.rTensor_add, LieHom.map_add,
      LinearMap.add_apply]
    abel
  lie_add _ := LinearMap.map_add _
  leibniz_lie x y t := by
    suffices (hasBracketAux x).comp (hasBracketAux y) =
        hasBracketAux ⁅x, y⁆ + (hasBracketAux y).comp (hasBracketAux x) by
      rw [← LinearMap.comp_apply, this]; rfl
    ext m n
    simp only [hasBracketAux, AlgebraTensorModule.curry_apply, curry_apply, sub_tmul, tmul_sub,
      LinearMap.coe_restrictScalars, Function.comp_apply, LinearMap.coe_comp,
      LinearMap.rTensor_tmul, LieHom.map_lie, toEnd_apply_apply, LinearMap.add_apply,
      LinearMap.map_add, LieHom.lie_apply, Module.End.lie_apply, LinearMap.lTensor_tmul]
    abel

/-- The tensor product of two Lie modules is a Lie module. -/
instance lieModule : LieModule R L (M ⊗[R] N) where
  smul_lie c x t := by
    change hasBracketAux (c • x) _ = c • hasBracketAux _ _
    simp only [hasBracketAux, smul_add, LinearMap.rTensor_smul, LinearMap.smul_apply,
      LinearMap.lTensor_smul, LieHom.map_smul, LinearMap.add_apply]
  lie_smul c _ := LinearMap.map_smul _ c

@[simp]
theorem lie_tmul_right (x : L) (m : M) (n : N) : ⁅x, m ⊗ₜ[R] n⁆ = ⁅x, m⁆ ⊗ₜ n + m ⊗ₜ ⁅x, n⁆ :=
  show hasBracketAux x (m ⊗ₜ[R] n) = _ by
    simp only [hasBracketAux, LinearMap.rTensor_tmul, toEnd_apply_apply,
      LinearMap.add_apply, LinearMap.lTensor_tmul]

variable (R L M N P Q)

/-- The universal property for tensor product of modules of a Lie algebra: the `R`-linear
tensor-hom adjunction is equivariant with respect to the `L` action. -/
def lift : (M →ₗ[R] N →ₗ[R] P) ≃ₗ⁅R,L⁆ M ⊗[R] N →ₗ[R] P :=
  { TensorProduct.lift.equiv R M N P with
    map_lie' := fun {x f} => by
      ext m n
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        lift.equiv_apply, LieHom.lie_apply, LinearMap.sub_apply, lie_tmul_right, map_add]
      abel }

@[simp]
theorem lift_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) : lift R L M N P f (m ⊗ₜ n) = f m n :=
  rfl

/-- A weaker form of the universal property for tensor product of modules of a Lie algebra.

Note that maps `f` of type `M →ₗ⁅R,L⁆ N →ₗ[R] P` are exactly those `R`-bilinear maps satisfying
`⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆` for all `x, m, n` (see e.g, `LieModuleHom.map_lie₂`). -/
def liftLie : (M →ₗ⁅R,L⁆ N →ₗ[R] P) ≃ₗ[R] M ⊗[R] N →ₗ⁅R,L⁆ P :=
  maxTrivLinearMapEquivLieModuleHom.symm ≪≫ₗ ↑(maxTrivEquiv (lift R L M N P)) ≪≫ₗ
    maxTrivLinearMapEquivLieModuleHom

@[simp]
theorem coe_liftLie_eq_lift_coe (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) :
    ⇑(liftLie R L M N P f) = lift R L M N P f := by
  tauto

theorem liftLie_apply (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (m : M) (n : N) :
    liftLie R L M N P f (m ⊗ₜ n) = f m n := by
  simp only [coe_liftLie_eq_lift_coe, LieModuleHom.coe_toLinearMap, lift_apply]

variable {R L M N P Q}

/-- A pair of Lie module morphisms `f : M → P` and `g : N → Q`, induce a Lie module morphism:
`M ⊗ N → P ⊗ Q`. -/
nonrec def map (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) : M ⊗[R] N →ₗ⁅R,L⁆ P ⊗[R] Q :=
  { map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) with
    map_lie' := fun {x t} => by
      simp only [LinearMap.toFun_eq_coe]
      refine t.induction_on ?_ ?_ ?_
      · simp only [LinearMap.map_zero, lie_zero]
      · intro m n
        simp only [LieModuleHom.coe_toLinearMap, lie_tmul_right, LieModuleHom.map_lie, map_tmul,
          LinearMap.map_add]
      · intro t₁ t₂ ht₁ ht₂; simp only [ht₁, ht₂, lie_add, LinearMap.map_add] }

@[simp]
theorem toLinearMap_map (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) :
    (map f g : M ⊗[R] N →ₗ[R] P ⊗[R] Q) = TensorProduct.map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :=
  rfl

@[deprecated (since := "2024-12-30")] alias coe_linearMap_map := toLinearMap_map

@[simp]
nonrec theorem map_tmul (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) (m : M) (n : N) :
    map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  map_tmul _ _ _ _

/-- Given Lie submodules `M' ⊆ M` and `N' ⊆ N`, this is the natural map: `M' ⊗ N' → M ⊗ N`. -/
def mapIncl (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) : M' ⊗[R] N' →ₗ⁅R,L⁆ M ⊗[R] N :=
  map M'.incl N'.incl

@[simp]
theorem mapIncl_def (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) :
    mapIncl M' N' = map M'.incl N'.incl :=
  rfl

end LieModule

end TensorProduct

namespace LieModule

open scoped TensorProduct

variable (R) (L : Type v) (M : Type w)
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The action of the Lie algebra on one of its modules, regarded as a morphism of Lie modules. -/
def toModuleHom : L ⊗[R] M →ₗ⁅R,L⁆ M :=
  TensorProduct.LieModule.liftLie R L L M M
    { (toEnd R L M : L →ₗ[R] M →ₗ[R] M) with
      map_lie' := fun {x m} => by ext n; simp [LieRing.of_associative_ring_bracket] }

@[simp]
theorem toModuleHom_apply (x : L) (m : M) : toModuleHom R L M (x ⊗ₜ m) = ⁅x, m⁆ := by
  simp only [toModuleHom, TensorProduct.LieModule.liftLie_apply, LieModuleHom.coe_mk,
    LieHom.coe_toLinearMap, toEnd_apply_apply]

end LieModule

namespace LieSubmodule

open scoped TensorProduct

open TensorProduct.LieModule

open LieModule

variable {L : Type v} {M : Type w}
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable (I : LieIdeal R L) (N : LieSubmodule R L M)

/-- A useful alternative characterisation of Lie ideal operations on Lie submodules.

Given a Lie ideal `I ⊆ L` and a Lie submodule `N ⊆ M`, by tensoring the inclusion maps and then
applying the action of `L` on `M`, we obtain morphism of Lie modules `f : I ⊗ N → L ⊗ M → M`.

This lemma states that `⁅I, N⁆ = range f`. -/
theorem lieIdeal_oper_eq_tensor_map_range :
    ⁅I, N⁆ = ((toModuleHom R L M).comp (mapIncl I N : I ⊗[R] N →ₗ⁅R,L⁆ L ⊗[R] M)).range := by
  rw [← toSubmodule_inj, lieIdeal_oper_eq_linear_span, LieModuleHom.toSubmodule_range,
    LieModuleHom.toLinearMap_comp, LinearMap.range_comp, mapIncl_def, toLinearMap_map,
    TensorProduct.map_range_eq_span_tmul, Submodule.map_span]
  congr; ext m; constructor
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩; use x ⊗ₜ n; constructor
    · use ⟨x, hx⟩, ⟨n, hn⟩; rfl
    · simp
  · rintro ⟨t, ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩, h⟩; rw [← h]; use ⟨x, hx⟩, ⟨n, hn⟩; rfl

end LieSubmodule
