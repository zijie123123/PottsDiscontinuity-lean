module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.Duality.FiniteSupportEvenEdgeCycle
public import PottsDiscontinuity.Duality.LatticeCellBoundaryFiniteEdges
public import PottsDiscontinuity.Duality.LatticeCellBoundaryParity
public import PottsDiscontinuity.Duality.ScreenBridge
public import PottsDiscontinuity.Duality.WholePlaneDualGraph

/-! Actual finite-cluster dual boundary and simple cycles. These results do not
yet assert that the selected cycle has nonzero winding about the marked vertex. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK FK.Medial
noncomputable section

/-- Cell bases representing primal vertices, with the dual face-base convention. -/
def vertexCellBases (C : Finset LatticeVertex) : Finset LatticeVertex :=
  C.image fun v => (v.1 - 1, v.2 - 1)

lemma mem_vertexCellBases (C : Finset LatticeVertex) (x : LatticeVertex) :
    x ∈ vertexCellBases C ↔ (x.1 + 1, x.2 + 1) ∈ C := by
  constructor
  · rintro hx
    obtain ⟨v, hv, h⟩ := Finset.mem_image.1 hx
    have hvx : v = (x.1 + 1, x.2 + 1) := by
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      ext <;> dsimp at h₁ h₂ ⊢ <;> omega
    simpa only [← hvx] using hv
  · intro hx
    apply Finset.mem_image.2
    exact ⟨(x.1 + 1, x.2 + 1), hx, by ext <;> simp⟩

/-- The literal cell boundary of a finite actual cluster consists of closed-dual edges. -/
theorem clusterCellBoundary_le_closedDual (ω : LatticeConfiguration) (v : LatticeVertex)
    (C : Finset LatticeVertex) (hC : ∀ x, x ∈ C ↔ x ∈ cluster ω v) :
    latticeCellBoundaryGraph (vertexCellBases C) ≤ wholePlaneClosedDualGraph ω := by
  intro x y hxy
  obtain ⟨_, d, hd, hfaces⟩ := (latticeCellBoundaryGraph_adj_iff _ x y).1 hxy
  have hsource : ((d.faceBase false).1 + 1, (d.faceBase false).2 + 1) =
      (primalBondOfDual d).source := by
    rcases d with ⟨⟨a, b⟩, ax⟩
    cases ax <;> simp [LatticeBond.faceBase, primalBondOfDual, LatticeBond.source]
  have htarget : ((d.faceBase true).1 + 1, (d.faceBase true).2 + 1) =
      (primalBondOfDual d).target := by
    rcases d with ⟨⟨a, b⟩, ax⟩
    cases ax <;> simp [LatticeBond.faceBase, primalBondOfDual, LatticeBond.target]
  have hclosed : latticeConfigurationBondState ω (primalBondOfDual d) = false := by
    cases hs : latticeConfigurationBondState ω (primalBondOfDual d)
    · rfl
    · have ha := (wholePlaneOpenPrimalGraph_adj_bond ω (primalBondOfDual d)).2 hs
      rw [wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph] at ha
      have hi : (primalBondOfDual d).target ∈ C ↔ (primalBondOfDual d).source ∈ C := by
        rw [hC, hC]
        exact ⟨fun h => h.trans ha.symm.reachable, fun h => h.trans ha.reachable⟩
      rw [mem_vertexCellBases, mem_vertexCellBases, htarget, hsource] at hfaces
      exact (hfaces (propext hi)).elim
  apply (wholePlaneClosedDualGraph_adj_iff_dualBond ω x y).2
  refine ⟨d, hclosed, ?_⟩
  have hp : s(d.source, d.target) = s(x, y) := hd
  rcases Sym2.eq_iff.1 hp with h | h
  · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · exact Or.inr ⟨h.2.symm, h.1.symm⟩

/-- Every nonempty finite cell set has a genuine simple boundary cycle through
an edge immediately to the right of a rightmost cell. -/
theorem finite_cell_boundary_has_outerEdge_simpleCycle
    (S : Finset LatticeVertex) (hS : S.Nonempty) :
    ∃ x ∈ S, (∀ y ∈ S, y.1 ≤ x.1) ∧
      ∃ z : LatticeVertex, ∃ p : (latticeCellBoundaryGraph S).Walk z z,
        p.IsCycle ∧ s((x.1 + 1, x.2), (x.1 + 1, x.2 + 1)) ∈ p.edges := by
  classical
  obtain ⟨x, hx, hmax⟩ := S.exists_max_image (fun v => v.1) hS
  let d : LatticeBond := ⟨(x.1 + 1, x.2), .vertical⟩
  have heast : (x.1 + 1, x.2) ∉ S := by
    intro h
    have hm := hmax (x.1 + 1, x.2) h
    dsimp at hm
    omega
  have hdiff : (d.faceBase true ∈ S) ≠ (d.faceBase false ∈ S) := by
    have ht : d.faceBase true = (x.1 + 1, x.2) := rfl
    have hf : d.faceBase false = x := by ext <;> simp [d, LatticeBond.faceBase]
    rw [ht, hf]
    intro heq
    exact heast (heq.mpr hx)
  have hadj : (latticeCellBoundaryGraph S).Adj d.source d.target :=
    (latticeCellBoundaryGraph_adj_iff _ _ _).2 ⟨d.adjacent, d, rfl, hdiff⟩
  let : DecidableRel (latticeCellBoundaryGraph S).Adj := Classical.decRel _
  obtain ⟨z, p, hp, he⟩ := edge_mem_some_isCycle_of_even_degree_of_finite_edgeSet
    (latticeCellBoundaryGraph S) (latticeCellBoundaryGraph_edgeSet_finite S)
    (latticeCellBoundaryGraph_even_degree S) hadj
  exact ⟨x, hx, hmax, z, p, hp, he⟩

end
end PottsDiscontinuity.Duality
