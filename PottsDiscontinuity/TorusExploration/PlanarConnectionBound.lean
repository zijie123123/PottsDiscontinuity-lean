module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.TorusExploration.FiniteFreeComparison

/-! A uniform diagonal bound for a finite free FK connection in any planar
unrolling, independent of the horizontal displacement of its endpoints. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK CorrLength MeasureTheory
variable {V : Type*} [Finite V] (G : SimpleGraph V)
noncomputable section
local instance planarConnectionBoundEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

lemma rotatedVertexEquiv_sum (v : RotatedVertex) :
    (rotatedVertexEquiv v).1+(rotatedVertexEquiv v).2=v.val.2 := by
  have h := congrArg (fun w : RotatedVertex => w.val.2) (squareToRotated_rotatedToSquare v)
  exact h

/-- The free connection cost between endpoints of vertical separation k in
any embedded finite rotated graph is at most the square root of the diagonal
probability at the exact frozen index 2k. -/
theorem finiteFree_connectivity_sq_le_diagonal (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (f : V ↪ RotatedVertex) (hG : G.map f ≤ rotatedLattice)
    (u v : V) (k : ℕ) (hk : (f v).val.2-(f u).val.2=(k : ℤ)) :
    (measure G θ (BoundaryCondition.free ∅) (connectivityEvent G u v)).toReal ^ 2 ≤
      μ.real (CorrLength.connectionEvent (0,0) (diagonalSite (2*k))) := by
  let g : V ↪ LatticeVertex := f.trans rotatedVertexEquiv.toEmbedding
  have hg : G.map g ≤ squareLattice := by
    intro a b hab
    obtain ⟨c,d,hcd,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 hab
    exact (rotatedLattice_adj_iff_square (f c) (f d)).1
      (hG ((SimpleGraph.map_adj _ _ _ _).2 ⟨c,d,hcd,rfl,rfl⟩))
  have hc := finiteFree_connectivity_le_freeLimit G θ μ hμ g hg u v
  let x : LatticeVertex := g v-g u
  have ht := isRCInfiniteVolumeLimit_connection_translation_invariant θ.toP θ.toQ
    θ.property μ hμ (-(g u)) (g u) (g v)
  have heq : μ.real (CorrLength.connectionEvent (g u) (g v)) =
      μ.real (CorrLength.connectionEvent (0,0) x) := by
    have hzero : latticeTranslate (-(g u)) (g u) = (0,0) := by
      ext <;> simp [latticeTranslate]
    have hdiff : latticeTranslate (-(g u)) (g v) = x := by
      ext <;> simp [x,latticeTranslate,sub_eq_add_neg]
    rw [hzero,hdiff] at ht
    exact ht.symm
  rw [heq] at hc
  have hx : x.1+x.2=(k : ℤ) := by
    have hu := rotatedVertexEquiv_sum (f u)
    have hv := rotatedVertexEquiv_sum (f v)
    change ((rotatedVertexEquiv (f v)).1-(rotatedVertexEquiv (f u)).1)+
      ((rotatedVertexEquiv (f v)).2-(rotatedVertexEquiv (f u)).2)=_
    omega
  exact (pow_le_pow_left₀ ENNReal.toReal_nonneg hc 2).trans
    (connection_sq_le_diagonalSite_of_sum θ μ hμ x k hx)

end
end PottsDiscontinuity.TorusExploration
