/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleDualPotential

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

/-- The actual finite dual configuration is the open complement of the primal
configuration, transported across the true labelled-edge/graph-edge bijection. -/
noncomputable def rectangleDualConfigurationEquiv (a : LatticeVertex) (w h : ℕ) :
    Finset (rectanglePrimalEdgeCarrier a w h) ≃ Configuration (rectangleDualGraph a w h) := by
  exact (rectangleDualComplementEquiv a w h).trans
    (Equiv.finsetCongr (rectangleDualGraphEdgeEquiv a w h))

@[simp] theorem rectangleDualConfigurationEquiv_apply (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    rectangleDualConfigurationEquiv a w h A = rectangleDualConfiguration a w h A := by
  simp [rectangleDualConfigurationEquiv, rectangleDualConfiguration,
    Equiv.finsetCongr_apply]

@[simp] theorem rectangleDualConfigurationEquiv_card (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    (rectangleDualConfigurationEquiv a w h A).card =
      (rectangleDualComplementEquiv a w h A).card := by
  simp [rectangleDualConfigurationEquiv, Equiv.finsetCongr_apply, Finset.card_map]

theorem rectangleDualConfiguration_card_add (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    A.card + (rectangleDualConfigurationEquiv a w h A).card =
      Nat.card (rectangleDualGraph a w h).edgeSet := by
  classical
  rw [rectangleDualConfigurationEquiv_card]
  have hcard := rectangleDualComplement_card_add a w h A
  calc
    A.card + (rectangleDualComplementEquiv a w h A).card =
        Fintype.card (rectanglePrimalEdgeCarrier a w h) := hcard
    _ = Nat.card (rectangleDualGraph a w h).edgeSet := by
      calc
        Fintype.card (rectanglePrimalEdgeCarrier a w h) =
            Nat.card (rectanglePrimalEdgeCarrier a w h) := (Nat.card_eq_fintype_card (α := rectanglePrimalEdgeCarrier a w h)).symm
        _ = Nat.card (rectangleDualGraph a w h).edgeSet :=
          (Nat.card_congr ((rectangleDualGraphEdgeEquiv a w h).symm.trans
            (rectanglePrimalDualEdgeEquiv a w h).symm)).symm
  

theorem rectangleDualGraph_edgeSet_card_eq_primal_edgeSet (a : LatticeVertex)
    (w h : ℕ) :
    Nat.card (rectangleDualGraph a w h).edgeSet =
      Nat.card (rectangleGraph a w h).edgeSet := by
  exact Nat.card_congr ((rectangleDualGraphEdgeEquiv a w h).symm.trans
    (rectanglePrimalDualEdgeEquiv a w h).symm)

theorem rectangleDualConfiguration_card_add_eq_primal_edgeSet
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    A.card + (rectangleDualConfiguration a w h A).card =
      Nat.card (rectangleGraph a w h).edgeSet := by
  rw [← rectangleDualConfigurationEquiv_apply]
  rw [rectangleDualConfiguration_card_add]
  exact rectangleDualGraph_edgeSet_card_eq_primal_edgeSet a w h

end PottsDiscontinuity.FK
