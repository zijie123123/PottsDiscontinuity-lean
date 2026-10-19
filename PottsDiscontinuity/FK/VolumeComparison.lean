/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.Disintegration
public import PottsDiscontinuity.FK.Expectation
public import PottsDiscontinuity.FK.RemainingComparison

/-!
# Comparison of the original FK marginal with a graph with edges deleted

Conditioning on the deleted edges induces a coarser partition than the original
one. The proved conditional law and wiring comparison give the stochastic
comparison after averaging over the actual frozen marginal. All original
vertices are retained here. Passing between different box vertex carriers is
a separate obligation, not an assumption in these theorems.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open FiniteProbability
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance volumeComparisonEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance volumeComparisonEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance volumeComparisonRemainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _
local instance volumeComparisonFrozenFintype (R : Configuration G) :
    Fintype (RemovedConfiguration G R) := Fintype.ofFinite _

omit [Finite V] in
/-- The frozen open paths only add identifications to the original partition. -/
theorem boundary_le_frozenBoundary (ξ : BoundaryCondition V) (H : Configuration G) :
    ξ.partition ≤ (frozenBoundary ξ H).partition := le_sup_right

/-- Deleting edges while keeping the original partition decreases every
nonnegative increasing observable of the edges that remain. -/
theorem remainingLaw_le_original_marginal (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (f : RemainingConfiguration G R → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    expectation (remainingLaw G q ξ R) f ≤
      expectation ((law G q ξ).map (fun C => (configurationSplitEquiv G R C).1)) f := by
  rw [law_map_remaining_eq_bind_frozen]
  apply le_expectation_bind
  intro H
  exact remainingLaw_boundary_comparison G q ξ (frozenBoundary ξ H.val)
    (boundary_le_frozenBoundary ξ H.val) R f hf0 hf

/-- The comparison expressed directly as an observable of the full original
configuration, without replacing the genuine marginal by a new model. -/
theorem remainingLaw_le_original_expectation (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (f : RemainingConfiguration G R → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    expectation (remainingLaw G q ξ R) f ≤
      expectation (law G q ξ) (fun C => f (configurationSplitEquiv G R C).1) := by
  simpa only [expectation_map] using remainingLaw_le_original_marginal q ξ R f hf0 hf

end
end PottsDiscontinuity.FK
