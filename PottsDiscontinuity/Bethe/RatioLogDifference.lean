module

public import PottsDiscontinuity.Bethe.RatioProfile

/-! # Mean-value control of the singular logarithmic differences -/

@[expose] public section

open Set Finset
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem ratio_segment_distance {x y t : ℝ} (ht : t ∈ uIcc x y) :
    |t - x| ≤ |y - x| := by
  rcases le_total x y with hxy | hyx
  · rw [uIcc_of_le hxy] at ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1), abs_of_nonneg (sub_nonneg.mpr hxy)]
    linarith [ht.2]
  · rw [uIcc_of_ge hyx] at ht
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonpos (sub_nonpos.mpr hyx)]
    linarith [ht.1]

theorem ratio_segment_away_zero {x y : ℝ} (hx : x ≠ 0) (hclose : |y - x| ≤ |x| / 2)
    {t : ℝ} (ht : t ∈ uIcc x y) : |x| / 2 ≤ |t| ∧ t ≠ 0 := by
  have hd := (ratio_segment_distance ht).trans hclose
  have htri : |x| ≤ |t| + |t - x| := by
    have h := abs_add_le t (x - t)
    rw [add_sub_cancel, abs_sub_comm x t] at h
    exact h
  have hxpos := abs_pos.mpr hx
  constructor
  · linarith
  · intro hz
    rw [hz, zero_sub, abs_neg] at hd
    linarith

/-- A mean-value bound on a segment that stays a fixed relative distance
from the singularity. This needs only a bound for `|t f'(t)|`. -/
theorem ratio_singular_difference_bound (f f' : ℝ → ℝ) {x y B : ℝ}
    (hx : x ≠ 0) (_hB : 0 ≤ B) (hclose : |y - x| ≤ |x| / 2)
    (hder : ∀ t ∈ uIcc x y, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ uIcc x y, |t * f' t| ≤ B) :
    |f y - f x| ≤ (2 * B / |x|) * |y - x| := by
  have hxpos := abs_pos.mpr hx
  have hderbound (t : ℝ) (ht : t ∈ uIcc x y) : ‖f' t‖ ≤ 2 * B / |x| := by
    have htaway := (ratio_segment_away_zero hx hclose ht).1
    have hb := hbound t ht
    rw [abs_mul] at hb
    rw [Real.norm_eq_abs]
    apply (le_div_iff₀ hxpos).mpr
    have hm := mul_le_mul_of_nonneg_right htaway (abs_nonneg (f' t))
    nlinarith only [hm, hb]
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hder t ht).hasDerivWithinAt) hderbound (convex_uIcc x y)
    (left_mem_uIcc : x ∈ uIcc x y) (right_mem_uIcc : y ∈ uIcc x y)
  simpa only [Real.norm_eq_abs] using hm

/-- The actual spectral profile satisfies the relative-segment bound. -/
theorem ratio_ell_difference_bound {c x y : ℝ} (hc : 2 < c)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hy : y ∈ Ioo (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hclose : |y - x| ≤ |x| / 2) :
    |ratioEll c y - ratioEll c x| ≤
      (2 * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4) / |x|) * |y - x| := by
  have hB : 0 ≤ Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4 := by
    have hc2 : 4 < c ^ 2 := by nlinarith
    exact add_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (sq_nonneg _))
      (by positivity)
  have hseg : uIcc x y ⊆ Ioo (-Real.pi) Real.pi := by
    intro t ht
    rcases le_total x y with hxy | hyx
    · rw [uIcc_of_le hxy] at ht
      exact ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
    · rw [uIcc_of_ge hyx] at ht
      exact ⟨hy.1.trans_le ht.1, ht.2.trans_lt hx.2⟩
  apply ratio_singular_difference_bound (ratioEll c) (ratioEllPrime c) hx0 hB hclose
  · intro t ht
    exact ratio_hasDerivAt_ell hc (hseg ht) (ratio_segment_away_zero hx0 hclose ht).2
  · intro t ht
    exact ratio_ellPrime_weighted_bound hc (Ioo_subset_Icc_self (hseg ht))

/-- A displacement of size `C|x|/N` gives a uniformly `O(1/N)` log difference. -/
theorem ratio_scaled_ell_difference_bound {c x y C : ℝ} {N : ℕ}
    (hc : 2 < c) (hN : 0 < N) (hlarge : 2 * C ≤ N)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hy : y ∈ Ioo (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hshift : |y - x| ≤ C * |x| / N) :
    |(N : ℝ) * (ratioEll c y - ratioEll c x)| ≤
      2 * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4) * C := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hxpos := abs_pos.mpr hx0
  have hclose : |y - x| ≤ |x| / 2 := by
    apply hshift.trans
    apply (div_le_iff₀ hNp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hlarge hxpos.le]
  have hh := ratio_ell_difference_bound hc hx hy hx0 hclose
  let B := Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4
  have hB : 0 ≤ B := by
    have hc2 : 4 < c ^ 2 := by nlinarith
    exact add_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (sq_nonneg _))
      (by positivity)
  have hfac : 0 ≤ 2 * B / |x| :=
    div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB) hxpos.le
  have hs := mul_le_mul_of_nonneg_left hshift hfac
  have he : (2 * B / |x|) * (C * |x| / (N : ℝ)) = (2 * B * C) / N := by
    field_simp
  have hb : |ratioEll c y - ratioEll c x| ≤ (2 * B * C) / N := hh.trans (hs.trans_eq he)
  rw [abs_mul, abs_of_pos hNp]
  calc
    _ = |ratioEll c y - ratioEll c x| * (N : ℝ) := mul_comm _ _
    _ ≤ 2 * B * C := (le_div_iff₀ hNp).mp hb

end PottsDiscontinuity.Bethe
