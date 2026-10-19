/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph

private theorem cycleFlow_zero_sum_on_neighborPair
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u : V} (p : G.Walk u u) (v a b : V)
    (c : V → V → ℤ)
    (hsupport : ∀ x y, s(x, y) ∉ p.edges → c x y = 0)
    (hbalance : ∑ w : V, c v w = 0)
    (hneighbors : p.toSubgraph.neighborSet v = {a, b})
    (hab : a ≠ b) :
    c v a + c v b = 0 := by
  classical
  let ambient := Finset.univ.filter (fun w => G.Adj v w)
  let cycle := Finset.univ.filter (fun w => p.toSubgraph.Adj v w)
  have hsub : cycle ⊆ ambient := by
    intro w hw
    simp only [cycle, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [ambient, Finset.mem_filter, Finset.mem_univ, true_and]
    exact p.adj_of_mem_edges ((p.adj_toSubgraph_iff_mem_edges).1 hw)
  have hout : ∀ w ∈ ambient, w ∉ cycle → c v w = 0 := by
    intro w hw hnot
    have hG : G.Adj v w := by simpa [ambient] using hw
    have hnotAdj : ¬p.toSubgraph.Adj v w := by simpa [cycle] using hnot
    apply hsupport
    intro hedge
    exact hnotAdj ((p.adj_toSubgraph_iff_mem_edges).2 hedge)
  have hsumEq :
      (∑ w ∈ cycle, c v w) = (∑ w ∈ ambient, c v w) :=
    Finset.sum_subset hsub hout
  have houtside : ∀ w ∈ Finset.univ, w ∉ ambient → c v w = 0 := by
    intro w _ hnot
    have hnotG : ¬ G.Adj v w := by simpa [ambient] using hnot
    apply hsupport
    intro hedge
    exact hnotG (p.adj_of_mem_edges hedge)
  have hall : (∑ w : V, c v w) = (∑ w ∈ ambient, c v w) := by
    symm
    exact Finset.sum_subset (by intro w hw; simp) houtside
  have hcycle : (∑ w ∈ cycle, c v w) = 0 := by
    rw [hsumEq, ← hall]
    exact hbalance
  have hcycleEq : cycle = ({a, b} : Finset V) := by
    ext w
    simp only [cycle, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← SimpleGraph.Subgraph.mem_neighborSet]
    rw [hneighbors]
    simp
  simpa [hcycleEq, hab] using hcycle

theorem cycleSupportedFlow_constantOnDarts
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u : V} (p : G.Walk u u)
    (hpc : p.IsCycle) (c : V → V → ℤ)
    (hanti : ∀ x y, c x y = -c y x)
    (hbalance : ∀ v, ∑ w : V, c v w = 0)
    (hsupport : ∀ x y, s(x, y) ∉ p.edges → c x y = 0) :
    ∃ k : ℤ, ∀ d ∈ p.darts, c d.fst d.snd = k := by
  classical
  let k := c (p.getVert 0) (p.getVert 1)
  have hstep : ∀ i, 0 < i → i + 1 < p.length →
      c (p.getVert (i - 1)) (p.getVert i) =
        c (p.getVert i) (p.getVert (i + 1)) := by
    intro i hi hlen
    have hneighbors := hpc.neighborSet_toSubgraph_internal
      (by omega : i ≠ 0) (by omega : i < p.length)
    have hsum := cycleFlow_zero_sum_on_neighborPair G p (p.getVert i)
      (p.getVert (i - 1)) (p.getVert (i + 1)) c hsupport (hbalance _)
      hneighbors (hpc.getVert_sub_one_ne_getVert_add_one (by omega))
    have hanti' := hanti (p.getVert (i - 1)) (p.getVert i)
    omega
  have hconst : ∀ i, i + 1 < p.length →
      c (p.getVert i) (p.getVert (i + 1)) = k := by
    intro i
    induction i with
    | zero => intro _; simp [k]
    | succ i ih =>
      intro hlen
      have hrec := hstep (i + 1) (by omega) (by omega)
      have hrec' : c (p.getVert i) (p.getVert (i + 1)) =
          c (p.getVert (i + 1)) (p.getVert (i + 1 + 1)) := by
        simpa using hrec
      rw [← hrec']
      exact ih (by omega)
  have hlast : c (p.getVert (p.length - 1)) (p.getVert p.length) = k := by
    have hend := hpc.neighborSet_toSubgraph_endpoint
    have hsum := cycleFlow_zero_sum_on_neighborPair G p (p.getVert 0)
      (p.getVert 1) (p.getVert (p.length - 1)) c hsupport (hbalance _)
      (by simpa [p.getVert_zero, p.getVert_length] using hend)
      (by simpa using hpc.snd_ne_penultimate)
    have hstart : c u (p.getVert 1) = k := by
      have hstart' := hconst 0 (by
        have := hpc.three_le_length
        omega)
      simpa [p.getVert_zero] using hstart' 
    have hanti' := hanti (p.getVert (p.length - 1)) (p.getVert p.length)
    rw [p.getVert_length] at hanti'
    rw [p.getVert_zero] at hsum
    rw [p.getVert_length]
    linear_combination hanti' - hsum + hstart
  refine ⟨k, ?_⟩
  intro d hd
  obtain ⟨i, hi, hdeq⟩ := List.mem_iff_getElem.mp hd
  subst d
  rw [p.darts_getElem_eq_getVert i (by simpa [p.length_darts] using hi)]
  by_cases hnotLast : i + 1 < p.length
  · exact hconst i hnotLast
  · have hiL : i < p.length := by simpa [p.length_darts] using hi
    have hiLast : i = p.length - 1 := by omega
    subst i
    simpa only [show p.length - 1 + 1 = p.length by omega] using hlast

theorem cycleSupportedFlow_constantOnDarts_sign
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u : V} (p : G.Walk u u)
    (hpc : p.IsCycle) (c : V → V → ℤ)
    (hanti : ∀ x y, c x y = -c y x)
    (hbalance : ∀ v, ∑ w : V, c v w = 0)
    (hsupport : ∀ x y, s(x, y) ∉ p.edges → c x y = 0)
    (hnonzero : ∀ x y, s(x, y) ∈ p.edges → c x y ≠ 0)
    (hbound : ∀ x y, c x y = -1 ∨ c x y = 0 ∨ c x y = 1) :
    ∃ k : ℤ, (k = -1 ∨ k = 1) ∧ ∀ d ∈ p.darts, c d.fst d.snd = k := by
  classical
  obtain ⟨k, hk⟩ := cycleSupportedFlow_constantOnDarts G p hpc c hanti
    hbalance hsupport
  have hnotnil := hpc.not_nil
  let d := p.firstDart hnotnil
  have hd : d ∈ p.darts := by simp [d]
  have hedge : s(d.fst, d.snd) ∈ p.edges := by
    have hhead : p.edges.head (Walk.edges_eq_nil.not.mpr hnotnil) ∈ p.edges :=
      List.head_mem _
    rw [p.head_edges_eq_mk_start_snd (Walk.edges_eq_nil.not.mpr hnotnil)] at hhead
    simpa [d, p.edge_firstDart hnotnil] using hhead
  have hne : c d.fst d.snd ≠ 0 := hnonzero d.fst d.snd hedge
  have hv := hbound d.fst d.snd
  have hsign : k = -1 ∨ k = 1 := by
    rw [hk d hd] at hv hne
    rcases hv with h | h | h
    · exact Or.inl h
    · exact (hne h).elim
    · exact Or.inr h
  exact ⟨k, hsign, hk⟩

end PottsDiscontinuity.TorusTopology.Planar.Medial
