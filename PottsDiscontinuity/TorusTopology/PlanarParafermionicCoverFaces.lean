/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

/-- The actual lift after taking the right edge of a positively oriented unit face. -/
def parafermionicCoverFaceRightLift (x y k : ℤ) : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift ((x,y),k) (x+1,y)

/-- Continue the same lifted face traversal upward. -/
def parafermionicCoverFaceRightUpLift (x y k : ℤ) : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift (parafermionicCoverFaceRightLift x y k) (x+1,y+1)

/-- Continue the same lifted face traversal to the left. -/
def parafermionicCoverFaceRightUpLeftLift (x y k : ℤ) : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift (parafermionicCoverFaceRightUpLift x y k) (x,y+1)

/-- The endpoint after the four actual lifts around a unit square. -/
def parafermionicCoverFaceLiftEndpoint (x y k : ℤ) : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift (parafermionicCoverFaceRightUpLeftLift x y k) (x,y)

private theorem coverFace_base_right (x y : ℤ) :
    squareLattice.Adj (x,y) (x+1,y) := by
  rw [squareLattice_adj_iff]
  exact Or.inl ⟨Or.inl (by omega), rfl⟩

private theorem coverFace_base_up (x y : ℤ) :
    squareLattice.Adj (x+1,y) (x+1,y+1) := by
  rw [squareLattice_adj_iff]
  exact Or.inr ⟨rfl, Or.inl (by omega)⟩

private theorem coverFace_base_left (x y : ℤ) :
    squareLattice.Adj (x+1,y+1) (x,y+1) := by
  rw [squareLattice_adj_iff]
  exact Or.inl ⟨Or.inr (by omega), rfl⟩

private theorem coverFace_base_down (x y : ℤ) :
    squareLattice.Adj (x,y+1) (x,y) := by
  rw [squareLattice_adj_iff]
  exact Or.inr ⟨rfl, Or.inr (by omega)⟩

/-- The four successive lifts are actual edges of the cover graph in the stated
right/up/left/down order. -/
theorem parafermionicCoverFaceLift_steps_adj (x y k : ℤ) :
    parafermionicCoverGraph.Adj ((x,y),k) (parafermionicCoverFaceRightLift x y k) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverFaceRightLift x y k)
      (parafermionicCoverFaceRightUpLift x y k) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverFaceRightUpLift x y k)
      (parafermionicCoverFaceRightUpLeftLift x y k) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverFaceRightUpLeftLift x y k)
      (parafermionicCoverFaceLiftEndpoint x y k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact parafermionicCoverNeighborLift_adj ((x,y),k) (x+1,y)
      (coverFace_base_right x y)
  · exact parafermionicCoverNeighborLift_adj
      (parafermionicCoverFaceRightLift x y k) (x+1,y+1)
      (coverFace_base_up x y)
  · exact parafermionicCoverNeighborLift_adj
      (parafermionicCoverFaceRightUpLift x y k) (x,y+1)
      (coverFace_base_left x y)
  · exact parafermionicCoverNeighborLift_adj
      (parafermionicCoverFaceRightUpLeftLift x y k) (x,y)
      (coverFace_base_down x y)

theorem parafermionicCoverFaceLiftEndpoint_formula (x y k : ℤ) :
    parafermionicCoverFaceLiftEndpoint x y k =
      ((x,y), k + if (x,y) = (0,-1) then 1 else 0) := by
  simp [parafermionicCoverFaceLiftEndpoint,
    parafermionicCoverFaceRightUpLeftLift,
    parafermionicCoverFaceRightUpLift,
    parafermionicCoverFaceRightLift,
    parafermionicCoverNeighborLift,
    parafermionicCoverSheetShift]
  split_ifs <;> omega

theorem parafermionicCoverFaceLiftEndpoint_eq_start_of_not_branch
    (x y k : ℤ) (h : (x,y) ≠ (0,-1)) :
    parafermionicCoverFaceLiftEndpoint x y k = ((x,y),k) := by
  rw [parafermionicCoverFaceLiftEndpoint_formula]
  simp [h]

end PottsDiscontinuity.TorusTopology.Planar.Medial
