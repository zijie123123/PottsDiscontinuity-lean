module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.FiniteClusterBoundary
public import PottsDiscontinuity.Duality.RayIndexSeparation

/-! Discrete enclosure of the marked vertex by a genuine closed dual simple circuit.
Separation is stated using the full primal lattice after only circuit-crossing
edges are removed, independently of the original open cluster. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK FK.Medial
noncomputable section

lemma closedDual_bond_state (ω : LatticeConfiguration) (d : LatticeBond)
    (h : (wholePlaneClosedDualGraph ω).Adj d.source d.target) :
    latticeConfigurationBondState ω (primalBondOfDual d) = false := by
  obtain ⟨e, he, hd⟩ := (wholePlaneClosedDualGraph_adj_iff_dualBond ω _ _).1 h
  have heq : e = d := by
    apply LatticeBond.toSym2_injective
    change s(e.source,e.target) = s(d.source,d.target)
    rcases hd with h | h
    · exact Sym2.eq_iff.2 (Or.inl ⟨h.1.symm,h.2.symm⟩)
    · exact Sym2.eq_iff.2 (Or.inr ⟨h.2.symm,h.1.symm⟩)
  simpa only [heq] using he

/-- All actual open primal edges avoid any closed-dual circuit's crossing edges. -/
theorem openGraph_le_circuitAvoidance (ω : LatticeConfiguration) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hclosed : ∀ u w, s(u,w) ∈ p.edges → (wholePlaneClosedDualGraph ω).Adj u w) :
    rcInfiniteOpenGraph ω ≤ circuitAvoidanceGraph p := by
  intro u w huw
  rw [← wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph] at huw
  obtain ⟨hadj, hopen⟩ := huw
  refine ⟨hadj, ?_⟩
  intro b hb he
  have hbopen : latticeConfigurationBondState ω b = true := by
    change ω (latticeBondEdge b) = true
    have heq : latticeBondEdge b =
        (⟨s(u,w), squareLattice.mem_edgeSet.2 hadj⟩ : squareLattice.edgeSet) :=
      Subtype.ext hb
    rw [heq]
    exact hopen
  have hd := hclosed (dualBondOfPrimal b).source (dualBondOfPrimal b).target he
  have hc := closedDual_bond_state ω (dualBondOfPrimal b) hd
  rw [primalBondOfDual_dualBondOfPrimal, hbopen] at hc
  cases hc

/-- The two endpoints of a boundary edge lie no further right than one plus
the maximum coordinate of the selected cell set. -/
lemma cellBoundary_adj_fst_le (S : Finset LatticeVertex) (M : ℤ)
    (hM : ∀ x ∈ S, x.1 ≤ M) {u w : LatticeVertex}
    (h : (latticeCellBoundaryGraph S).Adj u w) : u.1 ≤ M+1 ∧ w.1 ≤ M+1 := by
  obtain ⟨_, d, hd, hdiff⟩ := (latticeCellBoundaryGraph_adj_iff _ _ _).1 h
  have hf : d.faceBase true ∈ S ∨ d.faceBase false ∈ S := by
    by_cases ht : d.faceBase true ∈ S
    · exact Or.inl ht
    · right
      by_contra hn
      exact hdiff (propext (by simp [ht, hn]))
  have hend : (u = d.source ∧ w = d.target) ∨ (u = d.target ∧ w = d.source) := by
    rcases Sym2.eq_iff.1 hd with h | h
    · exact Or.inl ⟨h.1.symm,h.2.symm⟩
    · exact Or.inr ⟨h.2.symm,h.1.symm⟩
  rcases hf with hf | hf
  · have hm := hM _ hf
    rcases d with ⟨⟨a,b⟩, ax⟩
    cases ax <;> rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      dsimp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at hm ⊢ <;> omega
  · have hm := hM _ hf
    rcases d with ⟨⟨a,b⟩, ax⟩
    cases ax <;> rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      dsimp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at hm ⊢ <;> omega

lemma walk_support_fst_le {G : SimpleGraph LatticeVertex} {z w : LatticeVertex}
    (p : G.Walk z w) (M : ℤ) (hz : z.1 ≤ M)
    (hG : ∀ u v, G.Adj u v → v.1 ≤ M) : ∀ x ∈ p.support, x.1 ≤ M := by
  induction p with
  | nil =>
    intro x hx
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    subst x
    exact hz
  | @cons u v w h p ih =>
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hz
    · exact ih (hG u v h) x hx

/-- A nonempty cell set has a simple boundary circuit with nonzero ray index
at a rightmost cell center (in primal-vertex coordinates). -/
theorem cellBoundary_outer_cycle_nonzero (S : Finset LatticeVertex) (hS : S.Nonempty) :
    ∃ x ∈ S, ∃ z : LatticeVertex, ∃ p : (latticeCellBoundaryGraph S).Walk z z,
      p.IsCycle ∧ rayIndex (x.1+1,x.2+1) (p.mapLe (latticeCellBoundaryGraph_le S)) ≠ 0 := by
  classical
  obtain ⟨x, hx, hmax, z, p, hp, he⟩ := finite_cell_boundary_has_outerEdge_simpleCycle S hS
  let q := p.mapLe (latticeCellBoundaryGraph_le S)
  have hstart : z.1 ≤ x.1+1 := by
    cases p with
    | nil => exact (hp.not_nil SimpleGraph.Walk.Nil.nil).elim
    | @cons u v w h tail => exact (cellBoundary_adj_fst_le S x.1 hmax h).1
  have hbound : ∀ t ∈ q.support, t.1 ≤ x.1+1 := by
    rw [SimpleGraph.Walk.support_mapLe_eq_support]
    exact walk_support_fst_le p (x.1+1) hstart
      (fun _ _ h => (cellBoundary_adj_fst_le S x.1 hmax h).2)
  have hr : rayIndex (x.1+1+1,x.2+1) q = 0 :=
    rayIndex_zero_of_right _ q (fun t ht => by have := hbound t ht; dsimp; omega)
  have he' : s((x.1+1,(x.2+1)-1),(x.1+1,x.2+1)) ∈ q.edges := by
    change s((x.1+1,(x.2+1)-1),(x.1+1,x.2+1)) ∈
      (p.mapLe (latticeCellBoundaryGraph_le S)).edges
    simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges, add_sub_cancel_right] using he
  have hj := rayIndex_jump_of_vertical_edge (x.1+1) (x.2+1) q (hp.isTrail.mapLe _) he'
  rw [hr] at hj
  exact ⟨x,hx,z,p,hp,hj⟩

/-- Every finite marked cluster is enclosed by a genuine closed-dual simple
circuit. The nonzero ray index certifies discrete enclosure, and the stated
finite component uses only the circuit's crossing edges as the barrier. -/
theorem finite_cluster_has_surrounding_closedDual_circuit
    (ω : LatticeConfiguration) (v : LatticeVertex) (hf : (cluster ω v).Finite) :
    ∃ z : LatticeVertex, ∃ p : squareLattice.Walk z z, p.IsCycle ∧
      (∀ u w, s(u,w) ∈ p.edges → (wholePlaneClosedDualGraph ω).Adj u w) ∧
      rayIndex v p ≠ 0 ∧ {w | (circuitAvoidanceGraph p).Reachable v w}.Finite := by
  classical
  let C := hf.toFinset
  have hC : ∀ x, x ∈ C ↔ x ∈ cluster ω v := fun x => hf.mem_toFinset
  have hv : v ∈ C := (hC v).2 (SimpleGraph.Reachable.refl v)
  obtain ⟨x,hx,z,p,hp,hxidx⟩ := cellBoundary_outer_cycle_nonzero (vertexCellBases C)
    (Finset.Nonempty.image ⟨v,hv⟩ _)
  let q := p.mapLe (latticeCellBoundaryGraph_le (vertexCellBases C))
  have hclosed : ∀ u w, s(u,w) ∈ q.edges → (wholePlaneClosedDualGraph ω).Adj u w := by
    intro u w he
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at he
    exact clusterCellBoundary_le_closedDual ω v C hC (p.adj_of_mem_edges he)
  have hreach : (rcInfiniteOpenGraph ω).Reachable v (x.1+1,x.2+1) :=
    (hC _).1 ((mem_vertexCellBases C x).1 hx)
  have hidx : rayIndex v q ≠ 0 := by
    rw [rayIndex_eq_of_avoidance_reachable q
      (hreach.mono (openGraph_le_circuitAvoidance ω q hclosed))]
    exact hxidx
  exact ⟨z,q,hp.mapLe _,hclosed,hidx,
    finite_avoidance_component_of_rayIndex_ne_zero q v hidx⟩

end
end PottsDiscontinuity.Duality
