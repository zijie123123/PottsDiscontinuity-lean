/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Only bond states and actual primal graphs are retained. -/
module

public import PottsDiscontinuity.Duality.LatticePorts
public import PottsDiscontinuity.FK.BoxLaw

@[expose] public section

namespace PottsDiscontinuity.FK.Medial

/-- The square-lattice edge underlying a normalized actual lattice bond. -/
def latticeBondEdge (b : LatticeBond) : squareLattice.edgeSet :=
  ⟨b.toSym2, b.toSym2_mem_edgeSet⟩

/-- Read the actual original-edge state at a bond, without introducing a second
configuration carrier. -/
def latticeConfigurationBondState (ω : LatticeConfiguration) (b : LatticeBond) : Bool :=
  ω (latticeBondEdge b)

@[simp] theorem latticeConfigurationBondState_eq (ω : LatticeConfiguration) (b : LatticeBond) :
    latticeConfigurationBondState ω b = ω ⟨b.toSym2, b.toSym2_mem_edgeSet⟩ := rfl

/-- The literal open primal graph read from the existing unordered edge-state
carrier. -/
def wholePlaneOpenPrimalGraph (ω : LatticeConfiguration) : SimpleGraph LatticeVertex where
  Adj u v := ∃ h : squareLattice.Adj u v,
    ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true
  symm := ⟨by
    intro u v h
    rcases h with ⟨h, hopen⟩
    refine ⟨h.symm, ?_⟩
    have hedge : (⟨s(v, u), squareLattice.mem_edgeSet.mpr h.symm⟩ : squareLattice.edgeSet) =
        ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ := by
      apply Subtype.ext
      exact Sym2.eq_swap
    rw [hedge]
    exact hopen⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨h, _⟩
    exact squareLattice.loopless.irrefl u h⟩

def wholePlaneOpenCluster (ω : LatticeConfiguration) (u : LatticeVertex) : Set LatticeVertex :=
  {v | Relation.EqvGen (wholePlaneOpenPrimalGraph ω).Adj u v}

theorem wholePlaneOpenPrimalGraph_adj_bond (ω : LatticeConfiguration) (b : LatticeBond) :
    (wholePlaneOpenPrimalGraph ω).Adj b.source b.target ↔
      latticeConfigurationBondState ω b = true := by
  constructor
  · rintro ⟨_, h⟩
    simpa [latticeConfigurationBondState, latticeBondEdge, LatticeBond.toSym2] using h
  · intro h
    exact ⟨b.adjacent, by simpa [latticeConfigurationBondState, latticeBondEdge,
      LatticeBond.toSym2] using h⟩

end PottsDiscontinuity.FK.Medial
