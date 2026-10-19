/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverPrimalCycleDirections
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleFaceIndecomposable

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph
open Classical

/-- The support of the actual boundary graph of the named filling is exactly
the original lifted cycle support. -/
theorem parafermionicCoverSimpleCycleFillingSet_boundarySupport_eq_walkSupport
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    (parafermionicCoverFiniteFaceSetBoundaryGraph
      (parafermionicCoverSimpleCycleFillingSet hn p hp)).support =
      {v | v ∈ p.support} := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let B := parafermionicCoverFiniteFaceSetBoundaryGraph S
  have hB : B = p.toSubgraph.spanningCoe :=
    parafermionicCoverSimpleCycleFillingSet_boundary_eq hn p hp
  have hsupport : B.support = {v | v ∈ p.support} := by
    ext v
    constructor
    · rintro ⟨w, hvw⟩
      have hvw' : p.toSubgraph.Adj v w := by
        simpa [hB, SimpleGraph.Subgraph.spanningCoe_adj] using hvw
      exact p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hvw')
    · intro hv
      rcases (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil).mp hv with
        ⟨e, he, hve⟩
      induction e using Sym2.inductionOn with
      | hf a b =>
          have hab : p.toSubgraph.Adj a b :=
            SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr he
          rcases Sym2.mem_iff.mp hve with hva | hvb
          · subst a
            exact ⟨b, by simpa [hB, SimpleGraph.Subgraph.spanningCoe_adj] using hab⟩
          · subst b
            exact ⟨a, by simpa [hB, SimpleGraph.Subgraph.spanningCoe_adj] using hab.symm⟩
  simpa [B, S] using hsupport

/-- As a finite set, the actual boundary vertices are the original cycle
support, with the same lifted vertices. -/
theorem parafermionicCoverSimpleCycleFillingSet_boundarySupport_toFinset
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    (Finset.univ.filter fun v : ParafermionicCoverBoxVertex n =>
      v ∈ (parafermionicCoverFiniteFaceSetBoundaryGraph
        (parafermionicCoverSimpleCycleFillingSet hn p hp)).support) =
      p.support.toFinset := by
  classical
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  rw [parafermionicCoverSimpleCycleFillingSet_boundarySupport_eq_walkSupport hn p hp]
  simp only [Set.mem_ofPred_eq]

/-- The original primal quarter-turn total, summed once over the actual
vertices of the closed simple cycle. -/
noncomputable def parafermionicCoverPrimalCycleTurnSum {n : ℕ}
    {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) : ℤ := by
  classical
  exact Finset.sum p.support.toFinset.attach fun v =>
    parafermionicCoverPrimalCycleQuarterTurn p hp v.1
      (List.mem_toFinset.mp v.2)

/-- If a local function agrees with the actual quarter-turn at each cycle
vertex, its support-finite sum is the original quarter-turn total. -/
theorem parafermionicCoverPrimalCycleTurnSum_eq_support_sum_of_local_eq
    {n : ℕ} {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
    (f : ParafermionicCoverBoxVertex n → ℤ)
    (hf : ∀ v (hv : v ∈ p.support),
      parafermionicCoverPrimalCycleQuarterTurn p hp v hv = f v) :
    parafermionicCoverPrimalCycleTurnSum p hp =
      Finset.sum p.support.toFinset f := by
  classical
  unfold parafermionicCoverPrimalCycleTurnSum
  apply Finset.sum_bij (fun v hv => v.1)
  · intro v hv
    exact v.2
  · intro v hv w hw h
    exact Subtype.ext h
  · intro v hv
    exact ⟨⟨v, hv⟩, by simp⟩
  · intro v hv
    exact hf v (List.mem_toFinset.mp v.2)

/-- Since the closed walk's initial vertex also occurs at its final endpoint,
its support-finite sum agrees with the sum over the traversed tail list. -/
theorem parafermionicCoverPrimalCycle_support_sum_eq_tail_map_sum
    {n : ℕ} {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
    (f : ParafermionicCoverBoxVertex n → ℤ) :
    Finset.sum p.support.toFinset f = (p.support.tail.map f).sum := by
  classical
  have htailNodup : p.support.tail.Nodup := by
    exact hp.support_nodup
  have huTail : u ∈ p.support.tail := p.end_mem_tail_support hp.not_nil
  have hsupportFin : p.support.toFinset = p.support.tail.toFinset := by
    calc
      p.support.toFinset = (u :: p.support.tail).toFinset :=
        congrArg List.toFinset p.cons_tail_support.symm
      _ = p.support.tail.toFinset := by
        rw [List.toFinset_cons]
        exact Finset.insert_eq_of_mem (List.mem_toFinset.mpr huTail)
  rw [hsupportFin]
  exact List.sum_toFinset f htailNodup

end PottsDiscontinuity.TorusTopology.Planar.Medial
