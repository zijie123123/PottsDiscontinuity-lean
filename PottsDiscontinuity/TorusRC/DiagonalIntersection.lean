module

public import FixedPointTheorems.brouwer
public import Mathlib
public import PottsDiscontinuity.TorusRC.LiftedInterpolation

/-! # Intersections of opposite-colour unit diagonal segments -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Set

noncomputable section

private theorem unit_affine_between (a b : ℤ) (hab : |a-b| = 1)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ((max a b : ℤ):ℝ)-1 < (1-t)*(a:ℝ)+t*(b:ℝ) ∧
      (1-t)*(a:ℝ)+t*(b:ℝ) < (max a b : ℤ) := by
  have hne : a ≠ b := by intro h; simp [h] at hab
  have hd := abs_le.mp (le_of_eq hab)
  by_cases h : a < b
  · have hb : b = a+1 := by omega
    rw [max_eq_right h.le,hb]
    push_cast
    constructor <;> nlinarith
  · have ha : a = b+1 := by omega
    rw [max_eq_left (by omega),ha]
    push_cast
    constructor <;> nlinarith

private theorem unit_intervals_unique (a b : ℤ) (z : ℝ)
    (ha : (a:ℝ)-1 < z ∧ z < a) (hb : (b:ℝ)-1 < z ∧ z < b) : a = b := by
  have hab : a < b+1 := by
    have h : (a:ℝ) < (b:ℝ)+1 := by linarith
    exact_mod_cast h
  have hba : b < a+1 := by
    have h : (b:ℝ) < (a:ℝ)+1 := by linarith
    exact_mod_cast h
  omega

/-- Two unit diagonal segments with disjoint integer endpoint sets can
intersect only in the same unit square. The assertion includes all possible
orientations and does not assume the interpolating paths are simple. -/
theorem diagonal_segments_intersection_index {p p' q q' : ℤ × ℤ} {z : ℝ × ℝ}
    (hpX : |p.1-p'.1| = 1) (hpY : |p.2-p'.2| = 1)
    (hqX : |q.1-q'.1| = 1) (hqY : |q.2-q'.2| = 1)
    (h00 : p ≠ q) (h01 : p ≠ q') (h10 : p' ≠ q) (h11 : p' ≠ q')
    (hzP : z ∈ segment ℝ (cellEmbed p) (cellEmbed p'))
    (hzQ : z ∈ segment ℝ (cellEmbed q) (cellEmbed q')) :
    (max p.1 p'.1,max p.2 p'.2) = (max q.1 q'.1,max q.2 q'.2) := by
  have hnotP (a : ℤ × ℤ) (ha0 : a ≠ q) (ha1 : a ≠ q') : z ≠ cellEmbed a := by
    intro heq
    have ha : cellEmbed a ∈ segment ℝ (cellEmbed q) (cellEmbed q') := by rwa [heq] at hzQ
    rcases integer_mem_diagonal_segment hqX hqY ha with h | h
    · exact ha0 h
    · exact ha1 h
  have hnotQ (a : ℤ × ℤ) (ha0 : a ≠ p) (ha1 : a ≠ p') : z ≠ cellEmbed a := by
    intro heq
    have ha : cellEmbed a ∈ segment ℝ (cellEmbed p) (cellEmbed p') := by rwa [heq] at hzP
    rcases integer_mem_diagonal_segment hpX hpY ha with h | h
    · exact ha0 h
    · exact ha1 h
  rw [segment_eq_image] at hzP hzQ
  obtain ⟨s,⟨hs0,hs1⟩,hsz⟩ := hzP
  obtain ⟨t,⟨ht0,ht1⟩,htz⟩ := hzQ
  have hs0' : 0 < s := by
    have hne : s ≠ 0 := by
      intro heq
      exact hnotP p h00 h01 (by simpa [heq] using hsz.symm)
    exact lt_of_le_of_ne hs0 (Ne.symm hne)
  have hs1' : s < 1 := by
    have hne : s ≠ 1 := by
      intro heq
      exact hnotP p' h10 h11 (by simpa [heq] using hsz.symm)
    exact lt_of_le_of_ne hs1 hne
  have ht0' : 0 < t := by
    have hne : t ≠ 0 := by
      intro heq
      exact hnotQ q h00.symm h10.symm (by simpa [heq] using htz.symm)
    exact lt_of_le_of_ne ht0 (Ne.symm hne)
  have ht1' : t < 1 := by
    have hne : t ≠ 1 := by
      intro heq
      exact hnotQ q' h01.symm h11.symm (by simpa [heq] using htz.symm)
    exact lt_of_le_of_ne ht1 hne
  have hpx := unit_affine_between p.1 p'.1 hpX s hs0' hs1'
  have hpy := unit_affine_between p.2 p'.2 hpY s hs0' hs1'
  have hqx := unit_affine_between q.1 q'.1 hqX t ht0' ht1'
  have hqy := unit_affine_between q.2 q'.2 hqY t ht0' ht1'
  have hpxz := congrArg Prod.fst hsz
  have hpyz := congrArg Prod.snd hsz
  have hqxz := congrArg Prod.fst htz
  have hqyz := congrArg Prod.snd htz
  change (1-s)*(p.1:ℝ)+s*(p'.1:ℝ) = z.1 at hpxz
  change (1-s)*(p.2:ℝ)+s*(p'.2:ℝ) = z.2 at hpyz
  change (1-t)*(q.1:ℝ)+t*(q'.1:ℝ) = z.1 at hqxz
  change (1-t)*(q.2:ℝ)+t*(q'.2:ℝ) = z.2 at hqyz
  rw [hpxz] at hpx
  rw [hpyz] at hpy
  rw [hqxz] at hqx
  rw [hqyz] at hqy
  exact Prod.ext (unit_intervals_unique _ _ z.1 hpx hqx)
    (unit_intervals_unique _ _ z.2 hpy hqy)

end

end PottsDiscontinuity.TorusRC
