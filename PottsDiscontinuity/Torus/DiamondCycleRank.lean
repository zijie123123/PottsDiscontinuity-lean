module

public import PottsDiscontinuity.Torus.DiamondChains
public import PottsDiscontinuity.Torus.DiamondCounts
public import PottsDiscontinuity.Torus.RibbonConnectivity

/-!
# Dimension of the actual indexed cycle space

Zero edge differences mean a potential has one value on each open cluster. The
transpose incidence matrix has the same rank, giving the indexed cycle-rank formula.
-/

@[expose] public section

open Finset Matrix Module

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem diamondPotential_eq_of_adj (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : LinearMap.ker (diamondCoboundary hN hM A)) {u v : FaceVertex N M true}
    (h : (diamondOpenGraph hN hM true A).Adj u v) : f.val u = f.val v := by
  rw [diamondOpenGraph, SimpleGraph.fromEdgeSet_adj] at h
  obtain ⟨⟨w, hw, he⟩, _⟩ := h
  have hd := congrFun f.property (⟨w, hw⟩ : OpenDiamondEdge A)
  change f.val (faceEndpoint hN hM true w true) -
    f.val (faceEndpoint hN hM true w false) = 0 at hd
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (sub_eq_zero.mp hd).symm
  · exact sub_eq_zero.mp hd

theorem diamondPotential_eq_of_reachable (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : LinearMap.ker (diamondCoboundary hN hM A)) {u v : FaceVertex N M true}
    (h : (diamondOpenGraph hN hM true A).Reachable u v) : f.val u = f.val v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ ha ih => exact ih.trans (diamondPotential_eq_of_adj hN hM A f ha)

/-- Zero-difference potentials are precisely functions on the actual open clusters. -/
def diamondPotentialEquiv (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    ((diamondOpenGraph hN hM true A).ConnectedComponent → ℚ) ≃ₗ[ℚ]
      LinearMap.ker (diamondCoboundary hN hM A) where
  toFun f := ⟨fun v => f ((diamondOpenGraph hN hM true A).connectedComponentMk v), by
    apply funext
    intro e
    apply sub_eq_zero.mpr
    apply congrArg f
    exact (SimpleGraph.ConnectedComponent.sound
      (diamond_endpoints_reachable hN hM A e.val e.property)).symm⟩
  invFun f := Quot.lift f.val (fun _ _ h => diamondPotential_eq_of_reachable hN hM A f h)
  left_inv f := by
    funext q
    exact Quot.inductionOn q (fun _ => rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem finrank_ker_diamondCoboundary (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    finrank ℚ (LinearMap.ker (diamondCoboundary hN hM A)) = clusterCount hN hM true A := by
  let : Fintype (diamondOpenGraph hN hM true A).ConnectedComponent := Fintype.ofFinite _
  rw [← (diamondPotentialEquiv hN hM A).finrank_eq, Module.finrank_pi]
  exact Nat.card_eq_fintype_card.symm

theorem diamondCoboundary_eq_transpose (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    diamondCoboundary hN hM A = Matrix.toLin' (diamondIncidence hN hM A).transpose := by
  apply LinearMap.ext
  intro f
  funext e
  change f (faceEndpoint hN hM true e.val true) - f (faceEndpoint hN hM true e.val false) =
    ∑ u, diamondIncidence hN hM A u e * f u
  simp only [diamondIncidence, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem finrank_range_diamondBoundary_eq_coboundary (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    finrank ℚ (LinearMap.range (diamondBoundary hN hM A)) =
      finrank ℚ (LinearMap.range (diamondCoboundary hN hM A)) := by
  rw [diamondCoboundary_eq_transpose]
  change (diamondIncidence hN hM A).rank = (diamondIncidence hN hM A).transpose.rank
  exact (Matrix.rank_transpose _).symm

/-- The cycle-rank identity counts indexed edges, not distinct endpoint pairs. -/
theorem finrank_diamondCycleSpace (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    finrank ℚ (diamondCycleSpace hN hM A) + N * M / 2 =
      openCount A + clusterCount hN hM true A := by
  have hb := LinearMap.finrank_range_add_finrank_ker (diamondBoundary hN hM A)
  have hc := LinearMap.finrank_range_add_finrank_ker (diamondCoboundary hN hM A)
  rw [Module.finrank_pi, card_openDiamondEdge,
    finrank_range_diamondBoundary_eq_coboundary] at hb
  rw [Module.finrank_pi, card_faceVertex hN, finrank_ker_diamondCoboundary] at hc
  change finrank ℚ (LinearMap.ker (diamondBoundary hN hM A)) + N * M / 2 = _
  omega

end PottsDiscontinuity.Torus
