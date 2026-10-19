/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedCorners
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceCornerCompass
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

theorem parafermionicCoverFiniteFaceSelectedCorner_neighbors_mem_box
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) (c : Fin 4)
    (hc : c ∈ parafermionicCoverFiniteFaceSelectedCorners S v) :
    parafermionicCoverCompassNeighbor v.1 c ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverCompassNeighbor v.1 (c + 1) ∈
        parafermionicCoverBoxVertices n := by
  rcases (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v c).mp hc with
    ⟨i, hi, hcv⟩
  have hnext :
      parafermionicCoverCompassNeighbor v.1 c =
        parafermionicCoverFaceCorner i.1 (c + 1) := by
    have h := (parafermionicCoverFiniteFaceCorner_next_compass i c).symm
    rw [hcv] at h
    exact h
  have hprev :
      parafermionicCoverCompassNeighbor v.1 (c + 1) =
        parafermionicCoverFaceCorner i.1 (c - 1) := by
    have h := (parafermionicCoverFiniteFaceCorner_prev_compass i c).symm
    rw [hcv] at h
    exact h
  constructor
  · rw [hnext]
    exact parafermionicCoverFiniteFaceCorner_mem_box i (c + 1)
  · rw [hprev]
    exact parafermionicCoverFiniteFaceCorner_mem_box i (c - 1)

theorem parafermionicCoverFiniteFaceSelectedCorners_missing_of_outside_neighbor
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) (d : Fin 4)
    (hnot : parafermionicCoverCompassNeighbor v.1 d ∉
      parafermionicCoverBoxVertices n) :
    d ∉ parafermionicCoverFiniteFaceSelectedCorners S v ∧
      d - 1 ∉ parafermionicCoverFiniteFaceSelectedCorners S v := by
  have hidx : (d - 1) + 1 = d := by
    fin_cases d <;> decide
  constructor
  · intro hd
    exact hnot
      (parafermionicCoverFiniteFaceSelectedCorner_neighbors_mem_box S v d hd).1
  · intro hprev
    have hmem :=
      (parafermionicCoverFiniteFaceSelectedCorner_neighbors_mem_box S v (d - 1)
        hprev).2
    rw [hidx] at hmem
    exact hnot hmem

end PottsDiscontinuity.TorusTopology.Planar.Medial
