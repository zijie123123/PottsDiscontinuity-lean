/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaces
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

private theorem coverFace_shift_right (x y : ℤ) :
    parafermionicCoverSheetShift (x,y) (x+1,y) =
      if x = 0 ∧ y < 0 then 1 else 0 := by
  unfold parafermionicCoverSheetShift
  by_cases h : x = 0 ∧ y < 0 <;> simp [h]; omega

private theorem coverFace_shift_up (x y : ℤ) :
    parafermionicCoverSheetShift (x+1,y) (x+1,y+1) = 0 := by
  unfold parafermionicCoverSheetShift
  simp

private theorem coverFace_shift_left (x y : ℤ) :
    parafermionicCoverSheetShift (x+1,y+1) (x,y+1) =
      if x = 0 ∧ y+1 < 0 then -1 else 0 := by
  unfold parafermionicCoverSheetShift
  by_cases h : x = 0 ∧ y+1 < 0 <;> simp [h]; omega

@[simp] private theorem coverFace_shift_down (x y : ℤ) :
    parafermionicCoverSheetShift (x,y+1) (x,y) = 0 := by
  unfold parafermionicCoverSheetShift
  simp

@[simp] theorem parafermionicCoverFaceRightLift_formula (x y k : ℤ) :
    parafermionicCoverFaceRightLift x y k =
      ((x+1,y), k + if x = 0 ∧ y < 0 then 1 else 0) := by
  simp [parafermionicCoverFaceRightLift, parafermionicCoverNeighborLift,
    coverFace_shift_right]

@[simp] theorem parafermionicCoverFaceRightUpLift_formula (x y k : ℤ) :
    parafermionicCoverFaceRightUpLift x y k =
      ((x+1,y+1), k + if x = 0 ∧ y < 0 then 1 else 0) := by
  simp [parafermionicCoverFaceRightUpLift, parafermionicCoverFaceRightLift,
    parafermionicCoverNeighborLift, coverFace_shift_right, coverFace_shift_up]

@[simp] theorem parafermionicCoverFaceRightUpLeftLift_formula (x y k : ℤ) :
    parafermionicCoverFaceRightUpLeftLift x y k =
      ((x,y+1), k + (if x = 0 ∧ y < 0 then 1 else 0) +
        (if x = 0 ∧ y+1 < 0 then -1 else 0)) := by
  simp [parafermionicCoverFaceRightUpLeftLift,
    parafermionicCoverFaceRightUpLift, parafermionicCoverFaceRightLift,
    parafermionicCoverNeighborLift, coverFace_shift_right, coverFace_shift_up,
    coverFace_shift_left]

private theorem parafermionicCoverBox_coords (n : ℕ) (x y k : ℤ) :
    ((x,y),k) ∈ parafermionicCoverBoxVertices n ↔
      -(n : ℤ) ≤ x ∧ x ≤ (n : ℤ) ∧
      -(n : ℤ) ≤ y ∧ y ≤ (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ) := by
  rw [parafermionicCoverBoxVertices_mem]

/-- Literal finite carrier of ordinary unit faces: the lower-left lifted vertex
and each of the three intermediate vertices of its actual lift lie in `U_n`.
The puncture face is excluded. -/
def parafermionicCoverFiniteOrdinaryFaces (n : ℕ) :
    Finset ParafermionicCoverVertex :=
  (parafermionicCoverBoxFinset n).filter fun v =>
    v.1 ≠ (0,-1) ∧
      parafermionicCoverFaceRightLift v.1.1 v.1.2 v.2 ∈
        parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLift v.1.1 v.1.2 v.2 ∈
        parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLeftLift v.1.1 v.1.2 v.2 ∈
        parafermionicCoverBoxVertices n

theorem parafermionicCoverFaceIntermediateBounds_iff (n : ℕ)
    (v : ParafermionicCoverVertex) :
    v ∈ parafermionicCoverBoxVertices n ∧
      v.1 ≠ (0,-1) ∧
      parafermionicCoverFaceRightLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLeftLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ↔
    -(n : ℤ) ≤ v.1.1 ∧ v.1.1 < (n : ℤ) ∧
      -(n : ℤ) ≤ v.1.2 ∧ v.1.2 < (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ v.2 ∧ v.2 ≤ ((n ^ 5 : ℕ) : ℤ) ∧
      v.1 ≠ (0,-1) ∧
      (v.1.1 = 0 ∧ v.1.2 < -1 → v.2 < ((n ^ 5 : ℕ) : ℤ)) := by
  rcases v with ⟨⟨x,y⟩,k⟩
  simp only at *
  change ((x,y),k) ∈ parafermionicCoverBoxVertices n ∧
      ((x,y) ≠ (0,-1)) ∧
      parafermionicCoverFaceRightLift x y k ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLift x y k ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLeftLift x y k ∈ parafermionicCoverBoxVertices n ↔ _
  constructor
  · rintro ⟨hstart,hnot,hright,hup,hleft⟩
    have hs := (parafermionicCoverBox_coords n x y k).mp hstart
    have hr := (parafermionicCoverBox_coords n (x+1) y
      (k + (if x = 0 ∧ y < 0 then 1 else 0))).mp (by
        simpa using hright)
    have hu := (parafermionicCoverBox_coords n (x+1) (y+1)
      (k + (if x = 0 ∧ y < 0 then 1 else 0))).mp (by
        simpa using hup)
    rcases hs with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩
    rcases hr with ⟨_,hxhiR,_,_,_,hkhiR⟩
    rcases hu with ⟨_,_,_,hyhiU,_,_⟩
    have hxlt : x < (n : ℤ) := by omega
    have hylt : y < (n : ℤ) := by omega
    have hface : (x,y) ≠ (0,-1) := by simpa using hnot
    refine ⟨hxlo,hxlt,hylo,hylt,hklo,hkhi,hface,?_⟩
    rintro ⟨hx0, hyltm⟩
    have hyneg : y < 0 := by omega
    simp [hx0, hyneg] at hkhiR
    omega
  · rintro ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hnot,hseam⟩
    have hstart : ((x,y),k) ∈ parafermionicCoverBoxVertices n :=
      (parafermionicCoverBox_coords n x y k).mpr
        ⟨hxlo,by omega,hylo,by omega,hklo,hkhi⟩
    have hR : -((n ^ 5 : ℕ) : ℤ) ≤
        k + (if x = 0 ∧ y < 0 then 1 else 0) ∧
        k + (if x = 0 ∧ y < 0 then 1 else 0) ≤ ((n ^ 5 : ℕ) : ℤ) := by
      by_cases hs : x = 0 ∧ y < 0
      · rcases hs with ⟨hx,hy⟩
        have hyltm : y < -1 := by
          by_contra h
          have : y = -1 := by omega
          apply hnot
          exact Prod.ext hx this
        have hkn := hseam ⟨hx,hyltm⟩
        have hnpos : 0 < n := by omega
        have hpow : (0 : ℤ) < ((n ^ 5 : ℕ) : ℤ) := by
          exact_mod_cast (Nat.pow_pos hnpos : 0 < n ^ 5)
        have hklo' : -((n : ℤ) ^ 5) ≤ k := by
          simpa only [Nat.cast_pow] using hklo
        have hkn' : k < (n : ℤ) ^ 5 := by
          simpa only [Nat.cast_pow] using hkn
        simp [hx,hy]
        constructor
        · have h : -((n : ℤ) ^ 5) ≤ k + 1 := by omega
          simpa only [Nat.cast_pow] using h
        · simpa only [Nat.cast_pow] using hkn'
      · simp [hs]
        exact ⟨hklo,hkhi⟩
    have hright : parafermionicCoverFaceRightLift x y k ∈
        parafermionicCoverBoxVertices n := by
      rw [parafermionicCoverFaceRightLift_formula]
      exact (parafermionicCoverBox_coords n (x+1) y
        (k+(if x=0 ∧ y<0 then 1 else 0))).mpr
        ⟨by omega,by omega,by omega,by omega,hR.1,hR.2⟩
    have hup : parafermionicCoverFaceRightUpLift x y k ∈
        parafermionicCoverBoxVertices n := by
      rw [parafermionicCoverFaceRightUpLift_formula]
      exact (parafermionicCoverBox_coords n (x+1) (y+1)
        (k+(if x=0 ∧ y<0 then 1 else 0))).mpr
        ⟨by omega,by omega,by omega,by omega,hR.1,hR.2⟩
    have hnet : (if x = 0 ∧ y < 0 then 1 else 0) +
        (if x = 0 ∧ y+1 < 0 then -1 else 0) = 0 := by
      by_cases hx : x = 0
      · by_cases hy : y < 0
        · have hyltm : y < -1 := by
            by_contra h
            have : y = -1 := by omega
            apply hnot
            exact Prod.ext hx this
          have hy2 : y+1 < 0 := by omega
          simp [hx,hy,hy2]
        · simp [hx,hy]
          omega
      · simp [hx]
    have hleft : parafermionicCoverFaceRightUpLeftLift x y k ∈
        parafermionicCoverBoxVertices n := by
      rw [parafermionicCoverFaceRightUpLeftLift_formula]
      have hnet' : k + (if x = 0 ∧ y < 0 then 1 else 0) +
          (if x = 0 ∧ y+1 < 0 then -1 else 0) = k := by omega
      rw [hnet']
      exact (parafermionicCoverBox_coords n x (y+1) k).mpr
        ⟨by omega,by omega,by omega,by omega,hklo,hkhi⟩
    exact ⟨hstart,hnot,hright,hup,hleft⟩

theorem parafermionicCoverFiniteOrdinaryFaces_mem_iff (n : ℕ)
    (v : ParafermionicCoverVertex) :
    v ∈ parafermionicCoverFiniteOrdinaryFaces n ↔
      -(n : ℤ) ≤ v.1.1 ∧ v.1.1 < (n : ℤ) ∧
      -(n : ℤ) ≤ v.1.2 ∧ v.1.2 < (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ v.2 ∧ v.2 ≤ ((n ^ 5 : ℕ) : ℤ) ∧
      v.1 ≠ (0,-1) ∧
      (v.1.1 = 0 ∧ v.1.2 < -1 → v.2 < ((n ^ 5 : ℕ) : ℤ)) := by
  classical
  rw [parafermionicCoverFiniteOrdinaryFaces, Finset.mem_filter]
  change (v ∈ parafermionicCoverBoxVertices n ∧
      v.1 ≠ (0,-1) ∧
      parafermionicCoverFaceRightLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLeftLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n) ↔ _
  exact (parafermionicCoverFaceIntermediateBounds_iff n v)

end PottsDiscontinuity.TorusTopology.Planar.Medial
