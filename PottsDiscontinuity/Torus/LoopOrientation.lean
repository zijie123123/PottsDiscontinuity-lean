module

public import PottsDiscontinuity.Torus.EdgeIndex

/-!
# Orientation of a smoothed loop is one Boolean per cyclic orbit

A fixed compatible arrow field is used solely to select a canonical direction on each
loop. Every dart has a canonical loop class, invariant under both local strand pairing
and edge reversal. Any other compatible arrow field has a well-defined orientation
on those classes. The checkerboard module supplies such a reference field for every
smoothing of an even torus.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- A function invariant under one permutation step has equal values on each cyclic orbit. -/
theorem sameCycle_invariant {α β : Type*} [Finite α] (P : Equiv.Perm α) (f : α → β)
    (hf : ∀ d, f (P d) = f d) {d e : α} (h : P.SameCycle d e) : f d = f e := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  clear hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, hf]
    exact ih

variable (ω₀ : ArrowConfig N M) (s : Smoothing N M) (h₀ : CompatibleConfig ω₀ s)

/-- Canonical loop class of an arbitrary dart, aligning its edge with the reference arrows. -/
def loopOfDart (d : Dart N M) : DirectedLoop ω₀ s h₀ :=
  directedLoopOf ω₀ s h₀ (edgeDirectedEquiv ω₀ (dartEdge d))

theorem loopOfDart_of_out (d : Dart N M) (hd : dartOut ω₀ d = true) :
    loopOfDart ω₀ s h₀ d = directedLoopOf ω₀ s h₀ ⟨d, hd⟩ := by
  apply congrArg (directedLoopOf ω₀ s h₀)
  exact Subtype.ext (arrowDart_dartEdge ω₀ ⟨d, hd⟩)

@[simp] theorem loopOfDart_edgeReverse (d : Dart N M) :
    loopOfDart ω₀ s h₀ (edgeReverse d) = loopOfDart ω₀ s h₀ d := by
  unfold loopOfDart
  rw [dartEdge_edgeReverse]

theorem directedLoopOf_symm_step (d : DirectedDart ω₀) :
    directedLoopOf ω₀ s h₀ ((directedStep ω₀ s h₀).symm d) =
      directedLoopOf ω₀ s h₀ d := by
  have h := directedLoopOf_step ω₀ s h₀ ((directedStep ω₀ s h₀).symm d)
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- The two edge slots of a strand belong to the same canonical loop. -/
theorem loopOfDart_strandReverse (d : Dart N M) :
    loopOfDart ω₀ s h₀ (strandReverse s d) = loopOfDart ω₀ s h₀ d := by
  by_cases hd : dartOut ω₀ d = true
  · let x : DirectedDart ω₀ := ⟨d, hd⟩
    let y := (directedStep ω₀ s h₀).symm x
    have hy : y.val = edgeReverse (strandReverse s d) := rfl
    calc
      loopOfDart ω₀ s h₀ (strandReverse s d) =
          loopOfDart ω₀ s h₀ (edgeReverse (strandReverse s d)) :=
        (loopOfDart_edgeReverse ω₀ s h₀ _).symm
      _ = directedLoopOf ω₀ s h₀ y := by
        rw [← hy]
        exact loopOfDart_of_out ω₀ s h₀ y.val y.property
      _ = directedLoopOf ω₀ s h₀ x := directedLoopOf_symm_step ω₀ s h₀ x
      _ = loopOfDart ω₀ s h₀ d := (loopOfDart_of_out ω₀ s h₀ d hd).symm
  · have hd' : dartOut ω₀ (edgeReverse d) = true := by
      rw [dartOut_edgeReverse, Bool.eq_false_iff.mpr hd]
      rfl
    let x : DirectedDart ω₀ := ⟨edgeReverse d, hd'⟩
    let y := directedStep ω₀ s h₀ x
    have hy : y.val = strandReverse s d := by
      change strandReverse s (edgeReverse (edgeReverse d)) = strandReverse s d
      rw [edgeReverse_involutive]
    calc
      loopOfDart ω₀ s h₀ (strandReverse s d) = directedLoopOf ω₀ s h₀ y := by
        rw [← hy]
        exact loopOfDart_of_out ω₀ s h₀ y.val y.property
      _ = directedLoopOf ω₀ s h₀ x := directedLoopOf_step ω₀ s h₀ x
      _ = loopOfDart ω₀ s h₀ (edgeReverse d) :=
        (loopOfDart_of_out ω₀ s h₀ _ hd').symm
      _ = loopOfDart ω₀ s h₀ d := loopOfDart_edgeReverse ω₀ s h₀ d

@[simp] theorem loopOfDart_step (d : Dart N M) :
    loopOfDart ω₀ s h₀ (stepPerm s d) = loopOfDart ω₀ s h₀ d := by
  rw [stepPerm_apply, loopOfDart_strandReverse, loopOfDart_edgeReverse]

/-- The orientation of another compatible arrow field on each reference-oriented loop. -/
def loopOrientation (ω : ArrowConfig N M) (h : CompatibleConfig ω s) :
    DirectedLoop ω₀ s h₀ → Bool :=
  Quotient.lift (fun d : DirectedDart ω₀ => dartOut ω d.val) (by
    intro d e hde
    exact sameCycle_invariant (directedStep ω₀ s h₀) (fun x => dartOut ω x.val)
      (fun x => dartOut_step h x.val) hde)

@[simp] theorem loopOrientation_apply (ω : ArrowConfig N M) (h : CompatibleConfig ω s)
    (d : DirectedDart ω₀) :
    loopOrientation ω₀ s h₀ ω h (directedLoopOf ω₀ s h₀ d) = dartOut ω d.val := rfl

/-- The Boolean orientation on the loop recovers the arrow on every dart. -/
theorem dartOut_eq_loopOrientation (ω : ArrowConfig N M) (h : CompatibleConfig ω s)
    (d : Dart N M) :
    dartOut ω d = if dartOut ω₀ d then loopOrientation ω₀ s h₀ ω h (loopOfDart ω₀ s h₀ d)
      else !loopOrientation ω₀ s h₀ ω h (loopOfDart ω₀ s h₀ d) := by
  by_cases hd : dartOut ω₀ d = true
  · simp only [hd, ite_true]
    rw [loopOfDart_of_out ω₀ s h₀ d hd, loopOrientation_apply]
  · have hd' : dartOut ω₀ (edgeReverse d) = true := by
      rw [dartOut_edgeReverse, Bool.eq_false_iff.mpr hd]
      rfl
    simp only [Bool.eq_false_iff.mpr hd, Bool.false_eq_true, ite_false]
    rw [← loopOfDart_edgeReverse ω₀ s h₀ d,
      loopOfDart_of_out ω₀ s h₀ _ hd', loopOrientation_apply,
      dartOut_edgeReverse, Bool.not_not]

end PottsDiscontinuity.Torus
