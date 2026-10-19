/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: import/namespace relocation; existing FK.Parameters replaces ClusterWeight, permitting all q >= 1 and 0 < p < 1. -/
module

public import PottsDiscontinuity.FK.DomainMarkov

@[expose] public section

namespace PottsDiscontinuity.FK

open FiniteProbability

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance adaptiveDomainMarkovEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance adaptiveDomainMarkovEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The record produced by a revealed edge set stores both which edges were
revealed and their open/closed states. -/
def revealRecordEvent (reveal : Configuration G → Configuration G)
    (C₀ : Configuration G) : Set (Configuration G) :=
  {C | reveal C = reveal C₀ ∧ C ∩ reveal C₀ = C₀ ∩ reveal C₀}

def revealRecordConfiguration (reveal : Configuration G → Configuration G)
    (C₀ : Configuration G) : RemovedConfiguration G (reveal C₀) :=
  ⟨C₀ ∩ reveal C₀, Finset.inter_subset_right⟩

omit [Finite V] in
/-- A stopping-set consistency condition makes the record event exactly the
actual event fixing the revealed set and its open/closed state. -/
theorem revealRecordEvent_eq_frozenStateEvent
    (reveal : Configuration G → Configuration G)
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration G) :
    revealRecordEvent G reveal C₀ =
      frozenStateEvent (reveal C₀) (revealRecordConfiguration G reveal C₀) := by
  ext C
  constructor
  · intro h
    exact h.2
  · intro h
    have hrevealed := hstable C₀ C (by simpa [h])
    exact ⟨hrevealed, h⟩

end

end PottsDiscontinuity.FK
