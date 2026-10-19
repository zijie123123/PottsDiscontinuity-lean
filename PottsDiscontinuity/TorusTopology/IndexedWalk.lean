module

public import PottsDiscontinuity.Torus.DiamondClusterProjection
public import PottsDiscontinuity.Torus.DiamondSeamWinding

/-! Indexed diamond walks and their integral conserved-chain witnesses.
Parallel indexed edges are retained, and either traversal direction is allowed. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus
variable {N M : ℕ}

/-- A walk retaining the index and direction of every traversed primal edge. -/
inductive IndexedWalk (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    FaceVertex N M true → FaceVertex N M true → Type
  | nil (u) : IndexedWalk hN hM A u u
  | forward (e : OpenDiamondEdge A) {v}
      (p : IndexedWalk hN hM A (faceEndpoint hN hM true e.val true) v) :
      IndexedWalk hN hM A (faceEndpoint hN hM true e.val false) v
  | backward (e : OpenDiamondEdge A) {v}
      (p : IndexedWalk hN hM A (faceEndpoint hN hM true e.val false) v) :
      IndexedWalk hN hM A (faceEndpoint hN hM true e.val true) v

namespace IndexedWalk
variable {hN : Even N} {hM : Even M} {A : RCConfig N M}
variable {u v : FaceVertex N M true}
noncomputable section
open scoped Classical

/-- The integral signed indexed one-chain of a walk, embedded in Q. -/
def chain : {u v : FaceVertex N M true} → IndexedWalk hN hM A u v → OpenDiamondEdge A → ℚ
  | _,_,.nil _ => 0
  | _,_,.forward e p => Pi.single e 1 + chain p
  | _,_,.backward e p => -Pi.single e 1 + chain p

/-- The integer signed horizontal-seam intersection of the walk. -/
def winding : {u v : FaceVertex N M true} → IndexedWalk hN hM A u v → ℤ
  | _,_,.nil _ => 0
  | _,_,.forward e p => (if e.val.2.val=0 then -1 else 0) + winding p
  | _,_,.backward e p => -(if e.val.2.val=0 then -1 else 0) + winding p

/-- Every coordinate of the rational chain is an actual integer. -/
theorem chain_integral (p : IndexedWalk hN hM A u v) (e : OpenDiamondEdge A) :
    ∃ z : ℤ, chain p e = z := by
  induction p with
  | nil => exact ⟨0,rfl⟩
  | forward d p ih =>
    obtain ⟨z,hz⟩ := ih
    refine ⟨(if e=d then 1 else 0)+z,?_⟩
    simp only [chain,Pi.add_apply,Pi.single_apply,hz]
    split_ifs <;> push_cast <;> rfl
  | backward d p ih =>
    obtain ⟨z,hz⟩ := ih
    refine ⟨-(if e=d then 1 else 0)+z,?_⟩
    simp only [chain,Pi.add_apply,Pi.neg_apply,Pi.single_apply,hz]
    split_ifs <;> push_cast <;> rfl

/-- Boundary telescopes to terminal vertex minus initial vertex. -/
theorem boundary_chain (p : IndexedWalk hN hM A u v) :
    diamondBoundary hN hM A (chain p) = Pi.single v 1 - Pi.single u 1 := by
  induction p with
  | nil => simp [chain]
  | forward e p ih =>
    rw [chain,map_add,diamondBoundary_single,ih]
    ext w
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  | backward e p ih =>
    rw [chain,map_add,map_neg,diamondBoundary_single,ih]
    ext w
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply]
    ring

/-- The rational seam functional is exactly the embedded integer walk winding. -/
theorem winding_chain (p : IndexedWalk hN hM A u v) :
    diamondWindingY A (chain p) = (winding p : ℚ) := by
  induction p with
  | nil => simp [chain,winding,diamondWindingY]
  | forward e p ih =>
    change (∑ d, diamondSeamCrossY d.val * ((Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d + chain p d)) = _
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    change (∑ d, diamondSeamCrossY d.val * (Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d) +
      diamondWindingY A (chain p) = _
    rw [ih]
    simp [Pi.single_apply,mul_ite,diamondSeamCrossY,winding]
  | backward e p ih =>
    change (∑ d, diamondSeamCrossY d.val * (-((Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d) + chain p d)) = _
    simp_rw [mul_add,mul_neg]
    rw [Finset.sum_add_distrib,Finset.sum_neg_distrib]
    change -(∑ d, diamondSeamCrossY d.val * (Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d) +
      diamondWindingY A (chain p) = _
    rw [ih]
    simp [Pi.single_apply,mul_ite,diamondSeamCrossY,winding]

/-- The indexed walk connects its two finite primal vertices. -/
theorem reachable (p : IndexedWalk hN hM A u v) :
    (diamondOpenGraph hN hM true A).Reachable u v := by
  induction p with
  | nil => rfl
  | forward e p ih => exact (diamond_endpoints_reachable hN hM A e.val e.property).trans ih
  | backward e p ih => exact (diamond_endpoints_reachable hN hM A e.val e.property).symm.trans ih

/-- Every nonzero chain coefficient belongs to the initial vertex's cluster. -/
theorem chain_supported (p : IndexedWalk hN hM A u v) :
    ∀ e : OpenDiamondEdge A,
      diamondEdgeCluster hN hM A e ≠ (diamondOpenGraph hN hM true A).connectedComponentMk u →
        chain p e = 0 := by
  induction p with
  | nil => intro e _; rfl
  | @forward e v p ih =>
    intro d hd
    have hcomp := SimpleGraph.ConnectedComponent.sound
      (diamond_endpoints_reachable hN hM A e.val e.property)
    have hde : d ≠ e := by intro he; subst d; exact hd rfl
    have hdt : diamondEdgeCluster hN hM A d ≠
        (diamondOpenGraph hN hM true A).connectedComponentMk (faceEndpoint hN hM true e.val true) := by
      rwa [← hcomp]
    simp only [chain,Pi.add_apply,Pi.single_apply,hde,ite_false,zero_add,ih d hdt]
  | @backward e v p ih =>
    intro d hd
    have hcomp := SimpleGraph.ConnectedComponent.sound
      (diamond_endpoints_reachable hN hM A e.val e.property)
    have hde : d ≠ e := by intro he; subst d; exact hd hcomp
    have hdf : diamondEdgeCluster hN hM A d ≠
        (diamondOpenGraph hN hM true A).connectedComponentMk (faceEndpoint hN hM true e.val false) := by
      rwa [hcomp]
    simp only [chain,Pi.add_apply,Pi.neg_apply,Pi.single_apply,hde,ite_false,neg_zero,zero_add,ih d hdf]

end
end IndexedWalk

/-- Every finite open connectivity witness can be lifted to an indexed walk. -/
theorem exists_indexedWalk_of_reachable (hN : Even N) (hM : Even M) (A : RCConfig N M)
    {u v : FaceVertex N M true} (h : (diamondOpenGraph hN hM true A).Reachable u v) :
    Nonempty (IndexedWalk hN hM A u v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ⟨.nil _⟩
  | @cons u v w hadj p ih =>
    obtain ⟨p'⟩ := ih
    rw [diamondOpenGraph,SimpleGraph.fromEdgeSet_adj] at hadj
    obtain ⟨⟨e,he,hep⟩,_⟩ := hadj
    rcases Sym2.eq_iff.1 hep with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨.forward ⟨e,he⟩ p'⟩
    · exact ⟨.backward ⟨e,he⟩ p'⟩

end PottsDiscontinuity.TorusTopology
