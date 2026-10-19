/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteEdgeCount
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaceCount

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- The actual finite vertex, ordinary-face, and edge counts satisfy this integer
identity for the literal parafermionic cover carriers. This is a numerical count
identity only. -/
theorem parafermionicCoverFiniteEulerCount (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (ParafermionicCoverBoxVertex n) +
        (parafermionicCoverFiniteOrdinaryFaces n).card =
      (parafermionicCoverBoxGraph n).edgeFinset.card + 1 := by
  let S : ℕ := 2*n^5+1
  let V : ℕ := Fintype.card (ParafermionicCoverBoxVertex n)
  let F : ℕ := (parafermionicCoverFiniteOrdinaryFaces n).card
  let E : ℕ := (parafermionicCoverBoxGraph n).edgeFinset.card
  have hV : V = (2*n+1)^2*S := by
    dsimp [V,S]
    exact parafermionicCoverBoxVertex_card n
  have hF : F + S + (n-1) = (2*n)^2*S := by
    dsimp [F,S]
    exact parafermionicCoverFiniteOrdinaryFaces_card n hn
  have hE : E+n = 4*n*(2*n+1)*S := by
    dsimp [E,S]
    have hn0 : 0 < n := by omega
    exact parafermionicCoverBoxGraph_edgeFinset_card_add_n n hn0
  have hF' : F+S+n = (2*n)^2*S+1 := by omega
  have hpoly : V+(2*n)^2*S = 4*n*(2*n+1)*S+S := by
    rw [hV]
    ring
  have hsum : V+F+S+n = E+n+S+1 := by
    calc
      V+F+S+n = V+(F+S+n) := by omega
      _ = V+((2*n)^2*S+1) := by rw [hF']
      _ = (4*n*(2*n+1)*S+S)+1 := by omega
      _ = E+n+S+1 := by rw [hE]
  omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
