module

public import PottsDiscontinuity.Torus.SmoothingSum

/-!
# The finite dart permutation of a smoothed medial torus

A dart is an incident edge slot at a vertex, directed away from that vertex.
Edge reversal and the local smoothing are fixed-point-free involutions. Their
composition follows a smoothed path. Restricting to the darts following a compatible
arrow field gives a finite permutation whose cycles are the oriented loops.

This is a direct combinatorial construction from the definitions above.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

/-- The four incident edge slots, in the coordinate convention of `ArrowConfig`. -/
inductive Port
  | west | east | south | north
  deriving DecidableEq

instance : Fintype Port :=
  ⟨{.west, .east, .south, .north}, by intro p; cases p <;> simp⟩

/-- An incident edge slot at a medial vertex. -/
abbrev Dart (N M : ℕ) := (Fin N × Fin M) × Port

/-- The two turning pairings. Straight-through strands are excluded. -/
def pairedPort : Bool → Port → Port
  | false, .west => .north
  | false, .north => .west
  | false, .east => .south
  | false, .south => .east
  | true, .west => .south
  | true, .south => .west
  | true, .east => .north
  | true, .north => .east

theorem pairedPort_involutive (b : Bool) : Function.Involutive (pairedPort b) := by
  cases b <;> intro p <;> cases p <;> rfl

variable {N M : ℕ}

/-- Reverse a dart along its indexed torus edge. -/
def edgeReverse : Dart N M → Dart N M
  | ((i, j), .west) => ((prv i, j), .east)
  | ((i, j), .east) => ((nxt i, j), .west)
  | ((i, j), .south) => ((i, prv j), .north)
  | ((i, j), .north) => ((i, nxt j), .south)

@[simp] theorem edgeReverse_involutive : Function.Involutive (@edgeReverse N M) := by
  rintro ⟨⟨i, j⟩, p⟩
  cases p <;> simp only [edgeReverse, prv, nxt,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The edge-reversal permutation. -/
def edgePerm (N M : ℕ) : Equiv.Perm (Dart N M) :=
  ⟨edgeReverse, edgeReverse, edgeReverse_involutive, edgeReverse_involutive⟩

/-- Reverse direction along the local strand, without crossing a torus edge. -/
def strandReverse (s : Smoothing N M) (d : Dart N M) : Dart N M :=
  (d.1, pairedPort (s d.1) d.2)

@[simp] theorem strandReverse_involutive (s : Smoothing N M) :
    Function.Involutive (strandReverse s) := by
  rintro ⟨v, p⟩
  exact Prod.ext rfl (pairedPort_involutive (s v) p)

/-- The local strand-reversal permutation. -/
def strandPerm (s : Smoothing N M) : Equiv.Perm (Dart N M) :=
  ⟨strandReverse s, strandReverse s,
    strandReverse_involutive s, strandReverse_involutive s⟩

/-- Traverse one torus edge and then turn along the chosen strand at its endpoint. -/
def stepPerm (s : Smoothing N M) : Equiv.Perm (Dart N M) :=
  (edgePerm N M).trans (strandPerm s)

@[simp] theorem stepPerm_apply (s : Smoothing N M) (d : Dart N M) :
    stepPerm s d = strandReverse s (edgeReverse d) := rfl

@[simp] theorem stepPerm_symm_apply (s : Smoothing N M) (d : Dart N M) :
    (stepPerm s).symm d = edgeReverse (strandReverse s d) := rfl

/-- Edge reversal conjugates a path step into its inverse. -/
theorem edgeReverse_step (s : Smoothing N M) (d : Dart N M) :
    edgeReverse (stepPerm s d) = (stepPerm s).symm (edgeReverse d) := by
  simp

/-- Whether a local edge slot points out of its vertex. -/
def localOut (l r d u : Bool) : Port → Bool
  | .west => !l
  | .east => r
  | .south => !d
  | .north => u

/-- Whether a dart agrees with the arrow carried by its edge. -/
def dartOut (ω : ArrowConfig N M) (d : Dart N M) : Bool :=
  localOut (ω.left d.1) (ω.right d.1) (ω.below d.1) (ω.above d.1) d.2

@[simp] theorem dartOut_edgeReverse (ω : ArrowConfig N M) (d : Dart N M) :
    dartOut ω (edgeReverse d) = !dartOut ω d := by
  rcases d with ⟨⟨i, j⟩, p⟩
  cases p <;> simp only [dartOut, localOut, edgeReverse, ArrowConfig.left,
    ArrowConfig.right, ArrowConfig.below, ArrowConfig.above, prv, nxt,
    Equiv.symm_apply_apply, Bool.not_not]

theorem localOut_pairedPort (s l r d u : Bool) (h : Compatible s l r d u) (p : Port) :
    localOut l r d u (pairedPort s p) = !localOut l r d u p := by
  revert s l r d u p
  decide

theorem dartOut_strandReverse {ω : ArrowConfig N M} {s : Smoothing N M}
    (h : CompatibleConfig ω s) (d : Dart N M) :
    dartOut ω (strandReverse s d) = !dartOut ω d :=
  localOut_pairedPort _ _ _ _ _ (h d.1) d.2

/-- Compatible arrows are preserved when following a full smoothed-path step. -/
theorem dartOut_step {ω : ArrowConfig N M} {s : Smoothing N M}
    (h : CompatibleConfig ω s) (d : Dart N M) :
    dartOut ω (stepPerm s d) = dartOut ω d := by
  rw [stepPerm_apply, dartOut_strandReverse h, dartOut_edgeReverse, Bool.not_not]

/-- One directed representative of every edge, selected by its arrow. -/
abbrev DirectedDart (ω : ArrowConfig N M) := {d : Dart N M // dartOut ω d = true}

/-- Following the arrows and smoothing gives a permutation of directed edges. -/
def directedStep (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) : Equiv.Perm (DirectedDart ω) :=
  (stepPerm s).subtypeEquiv (fun d => by rw [dartOut_step h])

@[simp] theorem directedStep_val (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) :
    (directedStep ω s h d).val = stepPerm s d.val := rfl

/-- Cyclic reindexing of a directed smoothed loop is precisely the same-cycle relation. -/
abbrev DirectedLoop (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) :=
  Quotient (Equiv.Perm.SameCycle.setoid (directedStep ω s h))

noncomputable instance (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) : Fintype (DirectedLoop ω s h) :=
  Fintype.ofFinite _

/-- The loop containing a directed edge. Every directed edge has exactly one such class. -/
def directedLoopOf (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) : DirectedLoop ω s h :=
  Quotient.mk _ d

/-- A full path step stays on the same loop. -/
theorem directedLoopOf_step (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) :
    directedLoopOf ω s h (directedStep ω s h d) = directedLoopOf ω s h d := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl (directedStep ω s h) d).apply_left

end PottsDiscontinuity.Torus
