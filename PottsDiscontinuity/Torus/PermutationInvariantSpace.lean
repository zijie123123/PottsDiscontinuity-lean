module

public import PottsDiscontinuity.Torus.PermutationCycles
public import PottsDiscontinuity.Torus.LoopOrientation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Cycle counts as dimensions of invariant functions

Functions invariant under a permutation are exactly functions on its cyclic orbits.
For a transposition surgery, the subspace whose two marked values agree is the same
before and after surgery. Its codimension is at most one on either side.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

open Equiv Equiv.Perm Module

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Rational functions invariant on the cycles of a permutation. -/
def cycleFunctions (p : Perm α) : Submodule ℚ (α → ℚ) where
  carrier := {f | ∀ x, f (p x) = f x}
  zero_mem' := by intro x; rfl
  add_mem' := by intro f g hf hg x; change f (p x) + g (p x) = _; rw [hf, hg]; rfl
  smul_mem' := by intro c f hf x; change c • f (p x) = _; rw [hf]; rfl

/-- An invariant function is precisely a function on the actual orbit quotient. -/
def cycleFunctionEquiv (p : Perm α) :
    (PermutationCycle p → ℚ) ≃ₗ[ℚ] cycleFunctions p where
  toFun f := ⟨fun x => f (Quotient.mk _ x), by
    intro x
    exact congrArg f (Quotient.sound ((SameCycle.refl p x).apply_left))⟩
  invFun f := Quotient.lift f.val (fun _ _ h => sameCycle_invariant p f.val f.property h)
  left_inv f := by
    funext q
    exact Quotient.inductionOn q (fun _ => rfl)
  right_inv f := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

omit [DecidableEq α] in
theorem finrank_cycleFunctions (p : Perm α) :
    finrank ℚ (cycleFunctions p) = permutationCycleCount p := by
  let : Fintype (PermutationCycle p) := Fintype.ofFinite _
  rw [← (cycleFunctionEquiv p).finrank_eq, Module.finrank_pi]
  exact Nat.card_eq_fintype_card.symm

/-- The difference of the two marked values on invariant functions. -/
def cycleDifference (p : Perm α) (a b : α) : cycleFunctions p →ₗ[ℚ] ℚ :=
  ((LinearMap.proj a : (α → ℚ) →ₗ[ℚ] ℚ) - LinearMap.proj b).comp (cycleFunctions p).subtype

omit [Fintype α] [DecidableEq α] in
@[simp] theorem cycleDifference_apply (p : Perm α) (a b : α) (f : cycleFunctions p) :
    cycleDifference p a b f = f.val a - f.val b := rfl

omit [Fintype α] in
theorem function_swap_eq_of_eq (f : α → ℚ) {a b : α} (hab : f a = f b) (x : α) :
    f (swap a b x) = f x := by
  by_cases ha : x = a
  · subst x; rw [swap_apply_left, hab]
  · by_cases hb : x = b
    · subst x; rw [swap_apply_right, hab]
    · rw [swap_apply_of_ne_of_ne ha hb]

omit [Fintype α] in
theorem cycleFunctions_swap_mul_iff (p : Perm α) (a b : α) (f : α → ℚ)
    (hab : f a = f b) : f ∈ cycleFunctions (swap a b * p) ↔ f ∈ cycleFunctions p := by
  change (∀ x, f (swap a b (p x)) = f x) ↔ ∀ x, f (p x) = f x
  simp only [function_swap_eq_of_eq f hab]

/-- The common equal-value invariant space on the two sides of a transposition surgery. -/
def cycleDifferenceKernelEquiv (p : Perm α) (a b : α) :
    LinearMap.ker (cycleDifference p a b) ≃ₗ[ℚ]
      LinearMap.ker (cycleDifference (swap a b * p) a b) where
  toFun f := ⟨⟨f.val.val, (cycleFunctions_swap_mul_iff p a b f.val.val
    (sub_eq_zero.mp f.property)).mpr f.val.property⟩, f.property⟩
  invFun f := ⟨⟨f.val.val, (cycleFunctions_swap_mul_iff p a b f.val.val
    (sub_eq_zero.mp f.property)).mp f.val.property⟩, f.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

omit [Fintype α] [DecidableEq α] in
theorem finrank_cycleDifference_range_le (p : Perm α) (a b : α) :
    finrank ℚ (LinearMap.range (cycleDifference p a b)) ≤ 1 := by
  simpa only [finrank_self] using
    (Submodule.finrank_le (LinearMap.range (cycleDifference p a b)))

/-- A transposition can change the number of cyclic orbits by at most one. -/
theorem permutationCycleCount_swap_bounds (p : Perm α) (a b : α) :
    permutationCycleCount (swap a b * p) ≤ permutationCycleCount p + 1 ∧
      permutationCycleCount p ≤ permutationCycleCount (swap a b * p) + 1 := by
  have hp := LinearMap.finrank_range_add_finrank_ker (cycleDifference p a b)
  have hq := LinearMap.finrank_range_add_finrank_ker (cycleDifference (swap a b * p) a b)
  have he := (cycleDifferenceKernelEquiv p a b).finrank_eq
  have hpr := finrank_cycleDifference_range_le p a b
  have hqr := finrank_cycleDifference_range_le (swap a b * p) a b
  rw [finrank_cycleFunctions] at hp hq
  omega

end PottsDiscontinuity.Torus
