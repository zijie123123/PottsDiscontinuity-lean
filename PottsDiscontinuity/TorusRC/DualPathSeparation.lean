module

public import FixedPointTheorems.brouwer
public import PottsDiscontinuity.Torus.DiamondDualTranslation
public import PottsDiscontinuity.TorusRC.DiagonalIntersection
public import PottsDiscontinuity.TorusTopology.LiftedEdgeCover

/-! # Geometric disjointness of actual primal and translated dual paths -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength SixVertex

variable {N M : ℕ}

/-- The odd-cell embedding of a dual path represented on the primal carrier. -/
def dualShiftCell (u : RotatedVertex) : ℤ × ℤ := (u.val.1+1,u.val.2)

theorem primal_ne_dualShift (u v : RotatedVertex) : u.val ≠ dualShiftCell v := by
  intro h
  obtain ⟨k,hk⟩ := u.property
  obtain ⟨l,hl⟩ := v.property
  rw [h] at hk
  dsimp [dualShiftCell] at hk
  omega

theorem periodicCoordinate_add_one (hp : 0 < N) (z : ℤ) :
    periodicCoordinate hp (z+1) = nxt (periodicCoordinate hp z) := by
  have h := congrArg nxt (TorusTopology.periodicCoordinate_sub_one hp (z+1))
  simpa only [add_sub_cancel_right,nxt,prv,Equiv.apply_symm_apply] using h.symm

noncomputable section

/-- Every open primal edge is geometrically disjoint from every open dual
edge, including degenerate segments at visited vertices. -/
theorem opposite_open_diagonals_disjoint (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (u v x y : RotatedVertex)
    (hp : u = v ∨ (rotatedLattice.Adj u v ∧
      translatedDualConfig A (liftedEdgeIndex hNp hMp u v) = true))
    (hq : x = y ∨ (rotatedLattice.Adj x y ∧
      A (liftedEdgeIndex hNp hMp x y) = true)) :
    Disjoint (segment ℝ (cellEmbed u.val) (cellEmbed v.val))
      (segment ℝ (cellEmbed (dualShiftCell x)) (cellEmbed (dualShiftCell y))) := by
  apply Set.disjoint_left.mpr
  intro z hzP hzQ
  rcases hp with rfl | ⟨huv,hopenP⟩
  · rw [segment_same,Set.mem_singleton_iff] at hzP
    rcases hq with rfl | ⟨hxy,_⟩
    · rw [segment_same,Set.mem_singleton_iff] at hzQ
      exact primal_ne_dualShift u x (cellEmbed_injective (hzP.symm.trans hzQ))
    · have hX : |(dualShiftCell x).1-(dualShiftCell y).1| = 1 := by
        simpa only [dualShiftCell,add_sub_add_right_eq_sub] using hxy.1
      have hY : |(dualShiftCell x).2-(dualShiftCell y).2| = 1 := hxy.2
      rw [hzP] at hzQ
      rcases integer_mem_diagonal_segment hX hY hzQ with h | h
      · exact primal_ne_dualShift u x h
      · exact primal_ne_dualShift u y h
  · rcases hq with rfl | ⟨hxy,hopenQ⟩
    · rw [segment_same,Set.mem_singleton_iff] at hzQ
      rw [hzQ] at hzP
      rcases integer_mem_diagonal_segment huv.1 huv.2 hzP with h | h
      · exact primal_ne_dualShift u x h.symm
      · exact primal_ne_dualShift v x h.symm
    · have hX : |(dualShiftCell x).1-(dualShiftCell y).1| = 1 := by
        simpa only [dualShiftCell,add_sub_add_right_eq_sub] using hxy.1
      have hgeo := diagonal_segments_intersection_index huv.1 huv.2 hX hxy.2
        (primal_ne_dualShift u x) (primal_ne_dualShift u y)
        (primal_ne_dualShift v x) (primal_ne_dualShift v y) hzP hzQ
      have hidx : liftedEdgeIndex hNp hMp u v =
          (nxt (liftedEdgeIndex hNp hMp x y).1,(liftedEdgeIndex hNp hMp x y).2) := by
        apply Prod.ext
        · have hh := congrArg Prod.fst hgeo
          dsimp [dualShiftCell] at hh
          rw [max_add_add_right] at hh
          change periodicCoordinate hNp (max u.val.1 v.val.1) = _
          rw [hh,periodicCoordinate_add_one]
          rfl
        · have hh := congrArg Prod.snd hgeo
          dsimp [dualShiftCell] at hh
          change periodicCoordinate hMp (max u.val.2 v.val.2) =
            periodicCoordinate hMp (max x.val.2 y.val.2)
          rw [hh]
      rw [hidx] at hopenP
      change shiftRCConfig (dualConfig A)
        (nxt (liftedEdgeIndex hNp hMp x y).1,(liftedEdgeIndex hNp hMp x y).2) = true at hopenP
      rw [shiftRCConfig_nxt] at hopenP
      change Bool.not (A (liftedEdgeIndex hNp hMp x y)) = true at hopenP
      rw [hopenQ] at hopenP
      contradiction

/-- The complete polygonal traces of simultaneously open primal and dual
lifted walks are disjoint. No simplicity assumption is needed. -/
theorem opposite_open_walks_disjoint (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b c d : ℤ) {u v x y : RotatedVertex}
    (p : (liftedStripGraph hNp hMp (translatedDualConfig A) a b).Walk u v)
    (q : (liftedStripGraph hNp hMp A c d).Walk x y) :
    Disjoint (Set.range (polygonWalkPath (fun z : RotatedVertex => cellEmbed z.val) p))
      (Set.range (polygonWalkPath (fun z : RotatedVertex => cellEmbed (dualShiftCell z)) q)) := by
  apply Set.disjoint_left.mpr
  intro z hzP hzQ
  obtain ⟨u',v',_,_,hP,hzP⟩ := polygonWalkPath_range _ p hzP
  obtain ⟨x',y',_,_,hQ,hzQ⟩ := polygonWalkPath_range _ q hzQ
  exact Set.disjoint_left.mp (opposite_open_diagonals_disjoint hNp hMp A u' v' x' y'
    (hP.imp id (fun h => ⟨h.1,h.2.1⟩))
    (hQ.imp id (fun h => ⟨h.1,h.2.1⟩))) hzP hzQ

end

end PottsDiscontinuity.TorusRC
