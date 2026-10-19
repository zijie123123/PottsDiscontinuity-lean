/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.BondStates

@[expose] public section

namespace PottsDiscontinuity.FK.Medial

open PottsDiscontinuity.FK

noncomputable section

/-- The normalized dual bond crossing a primal bond, with lower/left endpoint
as its base. -/
def dualBondOfPrimal (b : LatticeBond) : LatticeBond :=
  match b.axis with
  | .horizontal => ⟨(b.base.1, b.base.2 - 1), .vertical⟩
  | .vertical => ⟨(b.base.1 - 1, b.base.2), .horizontal⟩

/-- The primal bond crossing a normalized dual bond. This is the shifted
inverse of `dualBondOfPrimal`. -/
def primalBondOfDual (d : LatticeBond) : LatticeBond :=
  match d.axis with
  | .horizontal => ⟨(d.base.1 + 1, d.base.2), .vertical⟩
  | .vertical => ⟨(d.base.1, d.base.2 + 1), .horizontal⟩

@[simp] theorem primalBondOfDual_dualBondOfPrimal (b : LatticeBond) :
    primalBondOfDual (dualBondOfPrimal b) = b := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;> simp [dualBondOfPrimal, primalBondOfDual]

@[simp] theorem dualBondOfPrimal_primalBondOfDual (d : LatticeBond) :
    dualBondOfPrimal (primalBondOfDual d) = d := by
  rcases d with ⟨⟨x,y⟩, ax⟩
  cases ax <;> simp [dualBondOfPrimal, primalBondOfDual]

@[simp] theorem dualBondOfPrimal_source (b : LatticeBond) :
    (dualBondOfPrimal b).source = b.faceBase false := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;> rfl

@[simp] theorem dualBondOfPrimal_target (b : LatticeBond) :
    (dualBondOfPrimal b).target = b.faceBase true := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;> simp [dualBondOfPrimal, LatticeBond.target, LatticeBond.faceBase]

/-- The literal whole-plane closed-dual graph on face bases. -/
def wholePlaneClosedDualGraph (ω : LatticeConfiguration) : SimpleGraph LatticeVertex where
  Adj u v := ∃ b : LatticeBond,
    latticeConfigurationBondState ω b = false ∧
      (u = b.faceBase false ∧ v = b.faceBase true ∨
       u = b.faceBase true ∧ v = b.faceBase false)
  symm := ⟨by
    intro u v h
    rcases h with ⟨b, hc, huv | huv⟩
    · exact ⟨b, hc, Or.inr ⟨huv.2, huv.1⟩⟩
    · exact ⟨b, hc, Or.inl ⟨huv.2, huv.1⟩⟩⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨b, _, huv | huv⟩
    · have hne := LatticePort.closedPair_faceBase_ne (⟨b, false, false⟩ : LatticePort)
      exact hne (by simpa [LatticePort.closedPair, LatticePort.faceBase] using (huv.1.symm.trans huv.2).symm)
    · have hne := LatticePort.closedPair_faceBase_ne (⟨b, false, false⟩ : LatticePort)
      exact hne (by simpa [LatticePort.closedPair, LatticePort.faceBase] using (huv.2.symm.trans huv.1).symm)⟩

def wholePlaneClosedDualCluster (ω : LatticeConfiguration) (u : LatticeVertex) :
    Set LatticeVertex :=
  {v | Relation.EqvGen (wholePlaneClosedDualGraph ω).Adj u v}

theorem wholePlaneClosedDualGraph_adj_iff (ω : LatticeConfiguration)
    (u v : LatticeVertex) :
    (wholePlaneClosedDualGraph ω).Adj u v ↔
      ∃ b : LatticeBond, latticeConfigurationBondState ω b = false ∧
        (u = b.faceBase false ∧ v = b.faceBase true ∨
         u = b.faceBase true ∧ v = b.faceBase false) := Iff.rfl

/-- Dual graph steps are exactly the normalized nearest-neighbor edges whose
crossing primal bond is closed. -/
theorem wholePlaneClosedDualGraph_adj_iff_dualBond (ω : LatticeConfiguration)
    (u v : LatticeVertex) :
    (wholePlaneClosedDualGraph ω).Adj u v ↔
      ∃ d : LatticeBond,
        latticeConfigurationBondState ω (primalBondOfDual d) = false ∧
        (u = d.source ∧ v = d.target ∨ u = d.target ∧ v = d.source) := by
  constructor
  · rintro ⟨b, hclosed, huv | huv⟩
    · refine ⟨dualBondOfPrimal b, ?_, ?_⟩
      · simpa using hclosed
      · simpa using Or.inl huv
    · refine ⟨dualBondOfPrimal b, ?_, ?_⟩
      · simpa using hclosed
      · simpa using Or.inr huv
  · rintro ⟨d, hclosed, huv | huv⟩
    · refine ⟨primalBondOfDual d, ?_, ?_⟩
      · simpa using hclosed
      · have hs : (primalBondOfDual d).faceBase false = d.source := by
          rw [← dualBondOfPrimal_source, dualBondOfPrimal_primalBondOfDual]
        have ht : (primalBondOfDual d).faceBase true = d.target := by
          rw [← dualBondOfPrimal_target, dualBondOfPrimal_primalBondOfDual]
        exact Or.inl ⟨huv.1.trans hs.symm, huv.2.trans ht.symm⟩
    · refine ⟨primalBondOfDual d, ?_, ?_⟩
      · simpa using hclosed
      · have hs : (primalBondOfDual d).faceBase false = d.source := by
          rw [← dualBondOfPrimal_source, dualBondOfPrimal_primalBondOfDual]
        have ht : (primalBondOfDual d).faceBase true = d.target := by
          rw [← dualBondOfPrimal_target, dualBondOfPrimal_primalBondOfDual]
        exact Or.inr ⟨huv.1.trans ht.symm, huv.2.trans hs.symm⟩

end
end PottsDiscontinuity.FK.Medial
