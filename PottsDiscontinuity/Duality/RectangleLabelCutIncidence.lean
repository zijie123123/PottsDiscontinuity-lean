/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleLabelCut

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

def rectangleCutDualEdgeOfBond (a : LatticeVertex) (w h : ℕ)
    (b : LatticeBond) (hs : b.source ∈ latticeRectangle a w h)
    (ht : b.target ∈ latticeRectangle a w h) : RectangleDualEdgeCarrier a w h :=
  rectanglePrimalDualEdgeEquiv a w h (rectangleCutEdgeOfBond a w h b hs ht)

theorem rectangleCutEdgeOfBond_mem_cut_iff (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (b : LatticeBond)
    (hs : b.source ∈ latticeRectangle a w h) (ht : b.target ∈ latticeRectangle a w h) :
    rectangleCutEdgeOfBond a w h b hs ht ∈ rectangleLabelCutEdgeCarrier a w h σ ↔
      σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ := by
  rw [mem_rectangleLabelCutEdgeCarrier]
  simp [rectangleLabelCutEndpointStates,
    rectanglePrimalEdgeBond_of_rectangleCutEdgeOfBond]

theorem rectangleCutDualEdgeOfBond_adj_iff (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (b : LatticeBond)
    (hs : b.source ∈ latticeRectangle a w h) (ht : b.target ∈ latticeRectangle a w h) :
    (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleDualEdgeSource a w h (rectangleCutDualEdgeOfBond a w h b hs ht))
      (rectangleDualEdgeTarget a w h (rectangleCutDualEdgeOfBond a w h b hs ht)) ↔
        σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ := by
  constructor
  · intro hadj
    obtain ⟨e, hcut, hpair⟩ :=
      (rectangleLabelCutDual_adj_iff a w h σ _ _).mp hadj
    have hpair' : (rectangleCutDualEdgeOfBond a w h b hs ht).crossingBond.toSym2 =
        e.crossingBond.toSym2 := by
      have h := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.1)) hpair
      simpa [rectangleDualCarrierPair, LatticeBond.toSym2,
        rectangleDualEdgeSource_val, rectangleDualEdgeTarget_val] using h
    have hcross := LatticeBond.toSym2_injective hpair'
    have hbond : rectanglePrimalEdgeBond a w h e.primalEdge = b := by
      have hd := congrArg primalBondOfDual hcross
      have hleft : primalBondOfDual
          (rectangleCutDualEdgeOfBond a w h b hs ht).crossingBond = b := by
        rw [rectangleDualEdge_crossedPrimalBond]
        change rectanglePrimalEdgeBond a w h
          (rectangleCutEdgeOfBond a w h b hs ht) = b
        exact rectanglePrimalEdgeBond_of_rectangleCutEdgeOfBond a w h b hs ht
      rw [hleft, rectangleDualEdge_crossedPrimalBond] at hd
      exact hd.symm
    have hcut' := (mem_rectangleLabelCutEdgeCarrier a w h σ e.primalEdge).mp hcut
    simpa [rectangleLabelCutEndpointStates, hbond] using hcut'
  · intro hdiff
    have hcut := (rectangleCutEdgeOfBond_mem_cut_iff a w h σ b hs ht).2 hdiff
    apply (rectangleLabelCutDual_adj_iff a w h σ _ _).2
    refine ⟨rectangleCutDualEdgeOfBond a w h b hs ht, ?_, ?_⟩
    · simpa [rectangleCutDualEdgeOfBond, rectanglePrimalDualEdgeEquiv] using hcut
    · simp [rectangleDualCarrierPair, rectangleCutDualEdgeOfBond]

theorem rectangleCutDualEdgeOfBond_crossingBond (a : LatticeVertex) (w h : ℕ)
    (b : LatticeBond) (hs : b.source ∈ latticeRectangle a w h)
    (ht : b.target ∈ latticeRectangle a w h) :
    (rectangleCutDualEdgeOfBond a w h b hs ht).crossingBond = dualBondOfPrimal b := by
  change rectangleCrossingDualBond a w h
    (rectangleCutEdgeOfBond a w h b hs ht) = dualBondOfPrimal b
  simp [rectangleCrossingDualBond, rectanglePrimalEdgeBond_of_rectangleCutEdgeOfBond]

theorem rectangleCutDualEdgeOfBond_source_val (a : LatticeVertex) (w h : ℕ)
    (b : LatticeBond) (hs : b.source ∈ latticeRectangle a w h)
    (ht : b.target ∈ latticeRectangle a w h) :
    (rectangleDualEdgeSource a w h
      (rectangleCutDualEdgeOfBond a w h b hs ht)).val = b.faceBase false := by
  rw [rectangleDualEdgeSource_val, rectangleCutDualEdgeOfBond_crossingBond,
    dualBondOfPrimal_source]

theorem rectangleCutDualEdgeOfBond_target_val (a : LatticeVertex) (w h : ℕ)
    (b : LatticeBond) (hs : b.source ∈ latticeRectangle a w h)
    (ht : b.target ∈ latticeRectangle a w h) :
    (rectangleDualEdgeTarget a w h
      (rectangleCutDualEdgeOfBond a w h b hs ht)).val = b.faceBase true := by
  rw [rectangleDualEdgeTarget_val, rectangleCutDualEdgeOfBond_crossingBond,
    dualBondOfPrimal_target]

theorem rectangleLabelCutDual_adj_iff_bond (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (u v : RectangleDualVertex a w h) :
    (rectangleLabelCutDualGraph a w h σ).Adj u v ↔
      ∃ b : LatticeBond, ∃ hs : b.source ∈ latticeRectangle a w h,
        ∃ ht : b.target ∈ latticeRectangle a w h,
          σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ ∧
            ((u.val = b.faceBase false ∧ v.val = b.faceBase true) ∨
              (u.val = b.faceBase true ∧ v.val = b.faceBase false)) := by
  constructor
  · intro hadj
    obtain ⟨e, hcut, hpair⟩ :=
      (rectangleLabelCutDual_adj_iff a w h σ u v).mp hadj
    let b := rectanglePrimalEdgeBond a w h e.primalEdge
    have hs : b.source ∈ latticeRectangle a w h :=
      rectanglePrimalEdgeBond_endpoints_mem_public a w h e.primalEdge |>.1
    have ht : b.target ∈ latticeRectangle a w h :=
      rectanglePrimalEdgeBond_endpoints_mem_public a w h e.primalEdge |>.2
    have hdiff : σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ := by
      have hh := (mem_rectangleLabelCutEdgeCarrier a w h σ e.primalEdge).mp hcut
      simpa [b, rectangleLabelCutEndpointStates] using hh
    have hcross : e.crossingBond = dualBondOfPrimal b := by
      rw [e.crossingBond_eq]
      rfl
    have hpair' : s(u.val, v.val) = s(b.faceBase false, b.faceBase true) := by
      have hh := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.1)) hpair
      simpa [rectangleDualCarrierPair, LatticeBond.toSym2, hcross,
        dualBondOfPrimal_source, dualBondOfPrimal_target] using hh
    rcases Sym2.eq_iff.mp hpair' with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact ⟨b, hs, ht, hdiff, Or.inl ⟨hu, hv⟩⟩
    · exact ⟨b, hs, ht, hdiff, Or.inr ⟨hu, hv⟩⟩
  · rintro ⟨b, hs, ht, hdiff, huv | huv⟩
    · have hadj := (rectangleCutDualEdgeOfBond_adj_iff a w h σ b hs ht).2 hdiff
      have hs' : (rectangleDualEdgeSource a w h
          (rectangleCutDualEdgeOfBond a w h b hs ht)).val = b.faceBase false :=
        rectangleCutDualEdgeOfBond_source_val a w h b hs ht
      have ht' : (rectangleDualEdgeTarget a w h
          (rectangleCutDualEdgeOfBond a w h b hs ht)).val = b.faceBase true :=
        rectangleCutDualEdgeOfBond_target_val a w h b hs ht
      have hu : u = rectangleDualEdgeSource a w h
          (rectangleCutDualEdgeOfBond a w h b hs ht) := by
        apply Subtype.ext
        exact huv.1.trans hs'.symm
      have hv : v = rectangleDualEdgeTarget a w h
          (rectangleCutDualEdgeOfBond a w h b hs ht) := by
        apply Subtype.ext
        exact huv.2.trans ht'.symm
      rw [hu, hv]
      exact hadj
    · have hadj := (rectangleCutDualEdgeOfBond_adj_iff a w h σ b hs ht).2 hdiff
      have hs' : (rectangleDualEdgeSource a w h
          (rectangleCutDualEdgeOfBond a w h b hs ht)).val = b.faceBase false :=
        rectangleCutDualEdgeOfBond_source_val a w h b hs ht
      have ht' : (rectangleDualEdgeTarget a w h
          (rectangleCutDualEdgeOfBond a w h b hs ht)).val = b.faceBase true :=
        rectangleCutDualEdgeOfBond_target_val a w h b hs ht
      have hu : u = rectangleDualEdgeTarget a w h
          (rectangleCutDualEdgeOfBond a w h b hs ht) := by
        apply Subtype.ext
        exact huv.1.trans ht'.symm
      have hv : v = rectangleDualEdgeSource a w h
          (rectangleCutDualEdgeOfBond a w h b hs ht) := by
        apply Subtype.ext
        exact huv.2.trans hs'.symm
      rw [hu, hv]
      exact hadj.symm

end

end PottsDiscontinuity.FK
