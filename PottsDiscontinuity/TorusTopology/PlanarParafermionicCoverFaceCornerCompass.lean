/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceCorners
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverCompass
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

private theorem parafermionicCoverFiniteFaceCorner_next_adjacent
    {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n) (c : Fin 4) :
    (parafermionicCoverFaceCorner i.1 c,
      parafermionicCoverFaceCorner i.1 (c + 1)) ∈
      parafermionicCoverFiniteFaceDarts i.1 := by
  fin_cases c <;>
    simp [parafermionicCoverFiniteFaceDarts, parafermionicCoverFaceCorner]

private theorem parafermionicCoverFiniteFaceCorner_next_base
    {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n) (c : Fin 4) :
    parafermionicCoverCompassBaseNeighbor
      (parafermionicCoverFaceCorner i.1 c) c =
        (parafermionicCoverFaceCorner i.1 (c + 1)).1 := by
  rcases i with ⟨⟨⟨x,y⟩,k⟩,hi⟩
  fin_cases c <;>
    simp [parafermionicCoverCompassBaseNeighbor,
      parafermionicCoverFaceCorner,
      parafermionicCoverFaceRightLift_formula,
      parafermionicCoverFaceRightUpLift_formula,
      parafermionicCoverFaceRightUpLeftLift_formula]

/-- Along an actual retained face, each next corner is the true lifted
compass neighbor. The final step uses the non-branch condition of the finite
ordinary face. -/
theorem parafermionicCoverFiniteFaceCorner_next_compass
    {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n) (c : Fin 4) :
    parafermionicCoverFaceCorner i.1 (c + 1) =
      parafermionicCoverCompassNeighbor
        (parafermionicCoverFaceCorner i.1 c) c := by
  have hbase := parafermionicCoverFiniteFaceCorner_next_base i c
  have hadj := parafermionicCoverFiniteFaceDart_adjacent n i.1 i.2
    (parafermionicCoverFiniteFaceCorner_next_adjacent i c)
  unfold parafermionicCoverCompassNeighbor
  exact parafermionicCoverNeighborLift_unique
    (parafermionicCoverFaceCorner i.1 c)
    (parafermionicCoverCompassBaseNeighbor
      (parafermionicCoverFaceCorner i.1 c) c)
    (parafermionicCoverFaceCorner i.1 (c + 1)) hbase.symm hadj

/-- The preceding corner is the actual opposite compass neighbor. -/
theorem parafermionicCoverFiniteFaceCorner_prev_compass
    {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n) (c : Fin 4) :
    parafermionicCoverFaceCorner i.1 (c - 1) =
      parafermionicCoverCompassNeighbor
        (parafermionicCoverFaceCorner i.1 c) (c + 1) := by
  have hidx : (c - 1) + 1 = c := by fin_cases c <;> decide
  have hdir : (c - 1) + 2 = c + 1 := by fin_cases c <;> decide
  have hnext := parafermionicCoverFiniteFaceCorner_next_compass i (c - 1)
  rw [hidx] at hnext
  calc
    parafermionicCoverFaceCorner i.1 (c - 1) =
        parafermionicCoverCompassNeighbor
          (parafermionicCoverCompassNeighbor
            (parafermionicCoverFaceCorner i.1 (c - 1)) (c - 1))
          ((c - 1) + 2) :=
      (parafermionicCoverCompassNeighbor_reverse
        (parafermionicCoverFaceCorner i.1 (c - 1)) (c - 1)).symm
    _ = parafermionicCoverCompassNeighbor
        (parafermionicCoverFaceCorner i.1 c) (c + 1) := by rw [← hnext, hdir]

/-- The positive raw darts of a retained ordinary face are exactly the
successive corner-to-compass-neighbor steps, including the closed final step. -/
theorem parafermionicCoverFiniteFaceDart_iff_corner_compass
    {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n)
    (u w : ParafermionicCoverVertex) :
    (u,w) ∈ parafermionicCoverFiniteFaceDarts i.1 ↔
      ∃ c : Fin 4, u = parafermionicCoverFaceCorner i.1 c ∧
        w = parafermionicCoverCompassNeighbor u c := by
  constructor
  · intro h
    simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert,
      Finset.mem_singleton] at h
    rcases h with h0 | h1 | h2 | h3
    · rcases Prod.mk.inj h0 with ⟨hu, hw⟩
      refine ⟨0, hu, ?_⟩
      rw [hw, hu]
      simpa [parafermionicCoverFaceCorner] using
        (parafermionicCoverFiniteFaceCorner_next_compass i 0)
    · rcases Prod.mk.inj h1 with ⟨hu, hw⟩
      refine ⟨1, hu, ?_⟩
      rw [hw, hu]
      simpa [parafermionicCoverFaceCorner] using
        (parafermionicCoverFiniteFaceCorner_next_compass i 1)
    · rcases Prod.mk.inj h2 with ⟨hu, hw⟩
      refine ⟨2, hu, ?_⟩
      rw [hw, hu]
      simpa [parafermionicCoverFaceCorner] using
        (parafermionicCoverFiniteFaceCorner_next_compass i 2)
    · rcases Prod.mk.inj h3 with ⟨hu, hw⟩
      refine ⟨3, hu, ?_⟩
      rw [hw, hu]
      simpa [parafermionicCoverFaceCorner] using
        (parafermionicCoverFiniteFaceCorner_next_compass i 3)
  · rintro ⟨c, rfl, rfl⟩
    fin_cases c <;>
      simp only <;>
      rw [← parafermionicCoverFiniteFaceCorner_next_compass i _] <;>
      simp [parafermionicCoverFiniteFaceDarts]

end PottsDiscontinuity.TorusTopology.Planar.Medial
