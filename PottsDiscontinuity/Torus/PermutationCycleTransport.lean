module

public import PottsDiscontinuity.Torus.PermutationCycles
public import PottsDiscontinuity.Torus.LoopOrientation

/-!
# Transport of cyclic orbits under reversed traversal

A bijection intertwining one path step with the inverse step on another carrier
induces an explicit equivalence of cyclic orbits. No orbit representative is selected.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

open Equiv Equiv.Perm

variable {α β : Type*}

theorem inverseIntertwining_symm (p : Perm α) (q : Perm β) (e : α ≃ β)
    (he : ∀ x, e (p x) = q.symm (e x)) (y : β) :
    e.symm (q y) = p.symm (e.symm y) := by
  apply e.injective
  rw [Equiv.apply_symm_apply]
  have h := congrArg q (he (p.symm (e.symm y)))
  simpa only [Equiv.apply_symm_apply] using h

variable [Finite α] [Finite β]

/-- Reversed-step transport of the actual cyclic-orbit quotients. -/
def permutationCycleEquivOfInverseIntertwining (p : Perm α) (q : Perm β) (e : α ≃ β)
    (he : ∀ x, e (p x) = q.symm (e x)) : PermutationCycle p ≃ PermutationCycle q where
  toFun := Quotient.lift (fun x => Quotient.mk _ (e x)) (fun _ _ h =>
    sameCycle_invariant p (fun x => (Quotient.mk _ (e x) : PermutationCycle q)) (fun x => by
      rw [he]
      exact Quotient.sound SameCycle.rfl.symm_apply_left) h)
  invFun := Quotient.lift (fun y => Quotient.mk _ (e.symm y)) (fun _ _ h =>
    sameCycle_invariant q (fun y => (Quotient.mk _ (e.symm y) : PermutationCycle p)) (fun y => by
      rw [inverseIntertwining_symm p q e he]
      exact Quotient.sound SameCycle.rfl.symm_apply_left) h)
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro a
    change Quotient.mk _ (e.symm (e a)) = Quotient.mk _ a
    rw [Equiv.symm_apply_apply]
  right_inv y := by
    refine Quotient.inductionOn y ?_
    intro b
    change Quotient.mk _ (e (e.symm b)) = Quotient.mk _ b
    rw [Equiv.apply_symm_apply]

@[simp] theorem permutationCycleEquivOfInverseIntertwining_mk
    (p : Perm α) (q : Perm β) (e : α ≃ β) (he : ∀ x, e (p x) = q.symm (e x)) (x : α) :
    permutationCycleEquivOfInverseIntertwining p q e he (Quotient.mk _ x) =
      Quotient.mk _ (e x) := rfl

end PottsDiscontinuity.Torus
