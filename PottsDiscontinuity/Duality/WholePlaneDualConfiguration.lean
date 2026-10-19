/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.WholePlaneDualGraph
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace PottsDiscontinuity.FK.Medial

open PottsDiscontinuity.FK

noncomputable section

def dualEdgeFirst (e : squareLattice.edgeSet) : LatticeVertex := e.1.out.1
def dualEdgeSecond (e : squareLattice.edgeSet) : LatticeVertex := e.1.out.2

 theorem edgeSet_out_adj (e : squareLattice.edgeSet) :
    squareLattice.Adj (dualEdgeFirst e) (dualEdgeSecond e) := by
  have hrepr : s(dualEdgeFirst e, dualEdgeSecond e) = e.1 := Quot.out_eq _
  exact squareLattice.mem_edgeSet.mp (hrepr ▸ e.2)

def wholePlaneBondEdgeEquiv : LatticeBond ≃ squareLattice.edgeSet where
  toFun := latticeBondEdge
  invFun e := Classical.choose
    (LatticeBond.existsUnique_of_adj (edgeSet_out_adj e))
  left_inv b := by
    change Classical.choose
      (LatticeBond.existsUnique_of_adj (edgeSet_out_adj (latticeBondEdge b))) = b
    have hout := Classical.choose_spec
      (LatticeBond.existsUnique_of_adj (edgeSet_out_adj (latticeBondEdge b)))
    have hb : b.toSym2 = s(dualEdgeFirst (latticeBondEdge b),
        dualEdgeSecond (latticeBondEdge b)) := by
      change b.toSym2 = s((latticeBondEdge b).1.out.1,
        (latticeBondEdge b).1.out.2)
      exact (Quot.out_eq (latticeBondEdge b).1).symm
    exact (hout.2 b hb).symm
  right_inv e := by
    apply Subtype.ext
    have hout := Classical.choose_spec
      (LatticeBond.existsUnique_of_adj (edgeSet_out_adj e))
    exact hout.1.trans (Quot.out_eq e.1)

def wholePlaneDualCrossingEdgeEquiv : squareLattice.edgeSet ≃ squareLattice.edgeSet where
  toFun e := wholePlaneBondEdgeEquiv (primalBondOfDual (wholePlaneBondEdgeEquiv.symm e))
  invFun e := wholePlaneBondEdgeEquiv (dualBondOfPrimal (wholePlaneBondEdgeEquiv.symm e))
  left_inv e := by
    change wholePlaneBondEdgeEquiv (dualBondOfPrimal (wholePlaneBondEdgeEquiv.symm
      (wholePlaneBondEdgeEquiv (primalBondOfDual (wholePlaneBondEdgeEquiv.symm e))))) = e
    simp only [Equiv.symm_apply_apply, dualBondOfPrimal_primalBondOfDual,
      Equiv.apply_symm_apply]
  right_inv e := by
    change wholePlaneBondEdgeEquiv (primalBondOfDual (wholePlaneBondEdgeEquiv.symm
      (wholePlaneBondEdgeEquiv (dualBondOfPrimal (wholePlaneBondEdgeEquiv.symm e))))) = e
    simp only [Equiv.symm_apply_apply, primalBondOfDual_dualBondOfPrimal,
      Equiv.apply_symm_apply]

def boolComplementEquiv : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

def boolComplementHomeomorph : Bool ≃ₜ Bool where
  toEquiv := boolComplementEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The actual edge-state dual transform: each dual edge receives the
complement of its crossing primal edge state. -/
def wholePlaneDualConfigurationHomeomorph :
    LatticeConfiguration ≃ₜ LatticeConfiguration := by
  let hindices : squareLattice.edgeSet ≃ squareLattice.edgeSet :=
    wholePlaneDualCrossingEdgeEquiv.symm
  exact (Homeomorph.piCongrLeft (Y := fun _ : squareLattice.edgeSet => Bool) hindices).trans
    (Homeomorph.piCongrRight fun _ : squareLattice.edgeSet => boolComplementHomeomorph)

@[simp] theorem wholePlaneDualConfigurationHomeomorph_apply
    (ω : LatticeConfiguration) (e : squareLattice.edgeSet) :
    wholePlaneDualConfigurationHomeomorph ω e =
      Bool.not (ω (wholePlaneDualCrossingEdgeEquiv e)) := by
  simp [wholePlaneDualConfigurationHomeomorph, boolComplementHomeomorph,
    boolComplementEquiv, Homeomorph.piCongrLeft, Homeomorph.piCongrRight,
    Equiv.piCongrLeft, Equiv.piCongrRight]

@[simp] theorem wholePlaneDualConfigurationHomeomorph_bondState
    (ω : LatticeConfiguration) (d : LatticeBond) :
    latticeConfigurationBondState (wholePlaneDualConfigurationHomeomorph ω) d =
      Bool.not (latticeConfigurationBondState ω (primalBondOfDual d)) := by
  change wholePlaneDualConfigurationHomeomorph ω (latticeBondEdge d) =
    Bool.not (ω (latticeBondEdge (primalBondOfDual d)))
  rw [wholePlaneDualConfigurationHomeomorph_apply]
  have hidx : wholePlaneDualCrossingEdgeEquiv (latticeBondEdge d) =
      latticeBondEdge (primalBondOfDual d) := by
    unfold wholePlaneDualCrossingEdgeEquiv
    change wholePlaneBondEdgeEquiv (primalBondOfDual
      (wholePlaneBondEdgeEquiv.symm (wholePlaneBondEdgeEquiv d))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [hidx]

@[simp] theorem wholePlaneDualConfigurationHomeomorph_symm_apply
    (ω : LatticeConfiguration) (e : squareLattice.edgeSet) :
    wholePlaneDualConfigurationHomeomorph.symm ω e =
      Bool.not (ω (wholePlaneDualCrossingEdgeEquiv.symm e)) := by
  simp [wholePlaneDualConfigurationHomeomorph,
    Homeomorph.piCongrLeft, Homeomorph.piCongrRight, Equiv.piCongrLeft,
    Equiv.piCongrRight, boolComplementHomeomorph, boolComplementEquiv]

private theorem bond_endpoints_of_toSym2_eq (b : LatticeBond) (u v : LatticeVertex)
    (h : b.toSym2 = s(u, v)) :
    (b.source = u ∧ b.target = v) ∨ (b.source = v ∧ b.target = u) := by
  change s(b.source, b.target) = s(u, v) at h
  exact Sym2.eq_iff.mp h

/-- The open primal graph after the actual dual transform is exactly the
closed-dual graph of the original configuration. -/
theorem wholePlaneOpenPrimalGraph_dualConfiguration_eq (ω : LatticeConfiguration) :
    wholePlaneOpenPrimalGraph (wholePlaneDualConfigurationHomeomorph ω) =
      wholePlaneClosedDualGraph ω := by
  ext u v
  constructor
  · intro h
    change ∃ hadj : squareLattice.Adj u v,
      wholePlaneDualConfigurationHomeomorph ω
        ⟨s(u, v), squareLattice.mem_edgeSet.mpr hadj⟩ = true at h
    rcases h with ⟨hadj, hopen⟩
    obtain ⟨d, hd, _⟩ := LatticeBond.existsUnique_of_adj hadj
    have hedge : latticeBondEdge d =
        ⟨s(u, v), squareLattice.mem_edgeSet.mpr hadj⟩ := by
      apply Subtype.ext
      exact hd
    rw [← hedge] at hopen
    change latticeConfigurationBondState
      (wholePlaneDualConfigurationHomeomorph ω) d = true at hopen
    rw [wholePlaneDualConfigurationHomeomorph_bondState] at hopen
    have hclosed : latticeConfigurationBondState ω (primalBondOfDual d) = false := by
      cases hs : latticeConfigurationBondState ω (primalBondOfDual d) <;> simp_all
    obtain hdir | hdir := bond_endpoints_of_toSym2_eq d u v hd
    · exact (wholePlaneClosedDualGraph_adj_iff_dualBond ω u v).mpr
        ⟨d, hclosed, Or.inl ⟨hdir.1.symm, hdir.2.symm⟩⟩
    · exact (wholePlaneClosedDualGraph_adj_iff_dualBond ω u v).mpr
        ⟨d, hclosed, Or.inr ⟨hdir.2.symm, hdir.1.symm⟩⟩
  · intro h
    obtain ⟨d, hclosed, hdir⟩ :=
      (wholePlaneClosedDualGraph_adj_iff_dualBond ω u v).mp h
    have hclosed' : ω (latticeBondEdge (primalBondOfDual d)) = false := by
      simpa [latticeConfigurationBondState] using hclosed
    have hopen : latticeConfigurationBondState
        (wholePlaneDualConfigurationHomeomorph ω) d = true := by
      rw [wholePlaneDualConfigurationHomeomorph_bondState]
      change Bool.not (ω (latticeBondEdge (primalBondOfDual d))) = true
      simp [hclosed']
    have hbond := (wholePlaneOpenPrimalGraph_adj_bond
      (wholePlaneDualConfigurationHomeomorph ω) d).2 hopen
    rcases hdir with huv | huv
    · simpa [huv.1, huv.2] using hbond
    · simpa [huv.1, huv.2] using hbond.symm

@[simp] theorem wholePlaneOpenCluster_dualConfiguration (ω : LatticeConfiguration)
    (u : LatticeVertex) :
    wholePlaneOpenCluster (wholePlaneDualConfigurationHomeomorph ω) u =
      wholePlaneClosedDualCluster ω u := by
  change {v | Relation.EqvGen
      (wholePlaneOpenPrimalGraph (wholePlaneDualConfigurationHomeomorph ω)).Adj u v} =
    {v | Relation.EqvGen (wholePlaneClosedDualGraph ω).Adj u v}
  rw [wholePlaneOpenPrimalGraph_dualConfiguration_eq]

theorem wholePlaneDualConfigurationHomeomorph_measurable :
    Measurable wholePlaneDualConfigurationHomeomorph :=
  wholePlaneDualConfigurationHomeomorph.continuous_toFun.measurable

end
end PottsDiscontinuity.FK.Medial
