/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.Lattice
public import PottsDiscontinuity.FK.Model

/-!
# The actual finite-box FK laws on the whole-lattice configuration carrier

Every finite box is its genuine induced square-lattice graph. A sampled box
configuration is extended by closed edges outside that graph, with no change to
its original finite free FK law. These are finite-box laws on a common carrier;
no infinite-volume limit or convergence is assumed or defined here.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

/-- One open/closed state for each original unordered square-lattice edge. -/
abbrev LatticeConfiguration := squareLattice.edgeSet → Bool

noncomputable section

/-- Inclusion of the genuine box-induced graph into the original lattice. -/
def boxGraphEmbedding (c : LatticeVertex) (r : ℕ) : boxGraph c r ↪g squareLattice where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

/-- Each original box edge is retained as that same unordered lattice edge. -/
def boxEdgeEmbedding (c : LatticeVertex) (r : ℕ) :
    (boxGraph c r).edgeSet ↪ squareLattice.edgeSet :=
  (boxGraphEmbedding c r).mapEdgeSet

/-- Literal closed extension of the sampled box configuration to all lattice edges. -/
def boxConfiguration (c : LatticeVertex) (r : ℕ) (A : Configuration (boxGraph c r)) :
    LatticeConfiguration := by
  classical
  exact fun e => decide (e ∈ A.map (boxEdgeEmbedding c r))

theorem boxConfiguration_open_iff (c : LatticeVertex) (r : ℕ)
    (A : Configuration (boxGraph c r)) (e : squareLattice.edgeSet) :
    boxConfiguration c r A e = true ↔ e ∈ A.map (boxEdgeEmbedding c r) := by
  classical
  simp only [boxConfiguration, decide_eq_true_eq]

@[simp] theorem boxConfiguration_at (c : LatticeVertex) (r : ℕ)
    (A : Configuration (boxGraph c r)) (e : (boxGraph c r).edgeSet) :
    boxConfiguration c r A (boxEdgeEmbedding c r e) = decide (e ∈ A) := by
  classical
  simp [boxConfiguration]

/-- No edge outside the original induced box edge set is artificially opened. -/
theorem boxConfiguration_outside (c : LatticeVertex) (r : ℕ)
    (A : Configuration (boxGraph c r)) (e : squareLattice.edgeSet)
    (he : e ∉ Set.range (boxEdgeEmbedding c r)) : boxConfiguration c r A e = false := by
  classical
  simp only [boxConfiguration, decide_eq_false_iff_not]
  intro h
  obtain ⟨a, ha, hmap⟩ := Finset.mem_map.mp h
  exact he ⟨a,hmap⟩

/-- The actual free finite-box FK law, pushed to a common whole-lattice carrier. -/
def boxLaw (q : Parameters) (c : LatticeVertex) (r : ℕ) : PMF LatticeConfiguration :=
  (law (boxGraph c r) q (BoundaryCondition.free ∅)).map (boxConfiguration c r)

end
end PottsDiscontinuity.FK
