module

public import PottsDiscontinuity.TorusExploration.WalkClosure
public import PottsDiscontinuity.TorusRC.CylinderEvents

/-! The closure of a bottom-to-top cylinder path winds once vertically. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus TorusTopology Finset
variable {N M : ℕ}

lemma windingY_fullChainExtension (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ) :
    diamondWindingY (openRCConfig N M) (fullDiamondChainExtension A f) =
      diamondWindingY A f := sum_fullDiamondChainExtension A f diamondSeamCrossY

lemma windingY_seamClosed (A : RCConfig N M)
    (f : OpenDiamondEdge (TorusRC.torusRCSeamClosed A) → ℚ) :
    diamondWindingY (TorusRC.torusRCSeamClosed A) f = 0 := by
  apply sum_eq_zero
  intro e _
  have he : e.val.2.val ≠ 0 := by
    intro h
    have := e.property
    simp [TorusRC.torusRCSeamClosed,h] at this
  simp [diamondSeamCrossY,he]

lemma seamOnly_row (e : OpenDiamondEdge (seamOnlyConfig N M)) : e.val.2.val=0 := by
  simpa only [seamOnlyConfig,decide_eq_true_eq] using e.property

/-- A seam-only return from the top to the bottom has signed winding one. -/
theorem seamReturn_windingY (hN : Even N) (hM : Even M) (hMlarge : 1 < M)
    {u v : FaceVertex N M true} (hu : u.val.2.val=0) (hv : v.val.2.val+1=M)
    (s : IndexedWalk hN hM (seamOnlyConfig N M) v u) :
    diamondWindingY (seamOnlyConfig N M) s.chain = 1 := by
  classical
  have hb := diamondBoundary_pairing hN hM (seamOnlyConfig N M)
    (fun w => (w.val.2.val : ℚ)) s.chain
  rw [IndexedWalk.boundary_chain] at hb
  simp only [Pi.sub_apply,mul_sub,sum_sub_distrib,Pi.single_apply,mul_ite,mul_one,
    mul_zero,sum_ite_eq',mem_univ,ite_true] at hb
  have hc (e : OpenDiamondEdge (seamOnlyConfig N M)) :
      diamondCoboundary hN hM (seamOnlyConfig N M) (fun w => (w.val.2.val : ℚ)) e =
        (M : ℚ)-1 := by
    rw [diamondCoordinateY_coboundary]
    simp only [diamondSeamCrossY,seamOnly_row,ite_true]
    ring
  simp_rw [hc] at hb
  rw [← mul_sum] at hb
  have hyv : (v.val.2.val : ℚ)+1=M := by exact_mod_cast hv
  have hMu : (M : ℚ)-1 ≠ 0 := by exact_mod_cast (show (M : ℤ)-1 ≠ 0 by omega)
  have hs : (∑ e, s.chain e) = -1 := by
    rw [hu,Nat.cast_zero] at hb
    apply (mul_left_cancel₀ hMu)
    linarith
  unfold diamondWindingY
  simp_rw [diamondSeamCrossY,seamOnly_row,ite_true,neg_one_mul]
  rw [sum_neg_distrib,hs]
  norm_num

/-- The closed chain winds once, independently of the horizontal meander of
both the cylinder path and the seam return. -/
theorem closedWalkPair_windingY (hN : Even N) (hM : Even M) (hMlarge : 1 < M)
    {A : RCConfig N M} {u v : FaceVertex N M true}
    (hu : u.val.2.val=0) (hv : v.val.2.val+1=M)
    (p : IndexedWalk hN hM (TorusRC.torusRCSeamClosed A) u v)
    (s : IndexedWalk hN hM (seamOnlyConfig N M) v u) :
    diamondWindingY (openRCConfig N M) (closedWalkPair hN hM p s).val = 1 := by
  change (∑ e : OpenDiamondEdge (openRCConfig N M), diamondSeamCrossY e.val *
    (fullDiamondChainExtension _ p.chain e + fullDiamondChainExtension _ s.chain e)) = 1
  simp_rw [mul_add]
  rw [sum_add_distrib]
  change diamondWindingY _ (fullDiamondChainExtension _ p.chain) +
    diamondWindingY _ (fullDiamondChainExtension _ s.chain) = 1
  rw [windingY_fullChainExtension,windingY_fullChainExtension,windingY_seamClosed,
    seamReturn_windingY hN hM hMlarge hu hv s,zero_add]

end PottsDiscontinuity.TorusExploration
