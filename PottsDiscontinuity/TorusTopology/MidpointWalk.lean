module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.LoopMidpoints

/-! Actual square-lattice walks traversing the lifted midpoint polygons. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops FK
variable {N M : ℕ}

lemma squareLattice_adj_portVector (z : ℤ × ℤ) (p : Port) :
    squareLattice.Adj z (z + portVector p) := by
  rw [squareLattice_adj_iff]
  cases p <;> simp [portVector]

lemma loopMidpointPosition_adj (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) (n : ℕ) :
    squareLattice.Adj (loopMidpointPosition ω s h d n)
      (loopMidpointPosition ω s h d (n+1)) := by
  obtain ⟨p,hp⟩ := loopMidpointPosition_step ω s h d n
  rw [hp]
  exact squareLattice_adj_portVector _ _

/-- Traverse the first n edges of the actual midpoint polygon. -/
noncomputable def loopMidpointWalk (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) :
    (n : ℕ) → squareLattice.Walk (loopMidpointPosition ω s h d 0)
      (loopMidpointPosition ω s h d n)
  | 0 => .nil
  | n+1 => (loopMidpointWalk ω s h d n).concat (loopMidpointPosition_adj ω s h d n)

lemma loopMidpointWalk_length (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) (n : ℕ) :
    (loopMidpointWalk ω s h d n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [loopMidpointWalk,ih]

lemma loopMidpointWalk_support (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) (n : ℕ) :
    (loopMidpointWalk ω s h d n).support =
      (List.range (n+1)).map (loopMidpointPosition ω s h d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [loopMidpointWalk,SimpleGraph.Walk.support_concat,ih,List.range_succ,
      List.map_append,List.map_singleton]

end PottsDiscontinuity.TorusTopology
