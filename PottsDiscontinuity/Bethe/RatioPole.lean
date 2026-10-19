module

public import PottsDiscontinuity.Bethe.RatioProducts

/-! # The central simple pole of the spectral factor

The regular part is given by an explicit sinc formula. No singular value
is assigned by a default branch. Its value at zero is exactly c².
-/

@[expose] public section

open Set Filter Complex
open scoped Topology

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

/-- The regular numerator/sinc profile obtained by removing the central pole. -/
noncomputable def ratioRegularPart (c x : ℝ) : ℝ :=
  ‖1 - (c : ℂ) ^ 2 - z x‖ / |Real.sinc (x / 2)|

theorem ratio_regularPart_zero (c : ℝ) : ratioRegularPart c 0 = c ^ 2 := by
  unfold ratioRegularPart
  rw [z_zero]
  have he : (1 : ℂ) - (c : ℂ) ^ 2 - 1 = -((c : ℂ) ^ 2) := by ring
  rw [he, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp

theorem ratio_continuousAt_regularPart_zero (c : ℝ) : ContinuousAt (ratioRegularPart c) 0 := by
  unfold ratioRegularPart z
  fun_prop (disch := simp)

theorem ratio_norm_denominator (x : ℝ) : ‖1 - z x‖ = |x| * |Real.sinc (x / 2)| := by
  by_cases hx : x = 0
  · simp [hx]
  have hhalf : x / 2 ≠ 0 := div_ne_zero hx (by norm_num)
  calc
    ‖1 - z x‖ = ‖z x - 1‖ := norm_sub_rev _ _
    _ = ‖2 * Real.sin (x / 2)‖ := Complex.norm_exp_I_mul_ofReal_sub_one x
    _ = |x| * |Real.sinc (x / 2)| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        Real.sinc_of_ne_zero hhalf, abs_div, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      field_simp

/-- The regular part equals `|x| |M|` throughout the punctured fundamental interval. -/
theorem ratio_regularPart_eq_mul_norm {c x : ℝ}
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ratioRegularPart c x = |x| * ‖M c (z x)‖ := by
  have hzx := z_ne_one hx hx0
  have hden : 1 - z x ≠ 0 := sub_ne_zero.mpr (Ne.symm hzx)
  have hM : M c (z x) = (1 - (c : ℂ) ^ 2 - z x) / (1 - z x) := by
    unfold M
    field_simp
    ring
  have hxabs := (abs_pos.mpr hx0).ne'
  have hsinc : |Real.sinc (x / 2)| ≠ 0 := by
    have hd := norm_ne_zero_iff.mpr hden
    rw [ratio_norm_denominator] at hd
    exact (mul_ne_zero_iff.mp hd).2
  rw [hM, norm_div, ratio_norm_denominator]
  unfold ratioRegularPart
  field_simp

theorem ratio_norm_div_size_tendsto {ι : Type*} {l : Filter ι} {c a : ℝ}
    (ha : 0 < a) (N : ι → ℝ) (hN : ∀ i, N i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Ioo (-Real.pi) Real.pi) (hxpos : ∀ i, 0 < x i)
    (hxlim : Tendsto x l (𝓝 0)) (hscale : Tendsto (fun i => N i * x i) l (𝓝 a)) :
    Tendsto (fun i => ‖M c (z (x i))‖ / N i) l (𝓝 (c ^ 2 / a)) := by
  have hr := (ratio_continuousAt_regularPart_zero c).tendsto.comp hxlim
  rw [ratio_regularPart_zero] at hr
  have ht := hr.div hscale ha.ne'
  apply ht.congr
  intro i
  dsimp only [Pi.div_apply, Function.comp_def]
  rw [ratio_regularPart_eq_mul_norm (hx i) (hxpos i).ne', abs_of_pos (hxpos i)]
  field_simp [(hxpos i).ne', hN i]

/-- In particular, this is the source term (3) after the central root scaling. -/
theorem ratio_scaled_inverse_norm_tendsto {ι : Type*} {l : Filter ι} {c a : ℝ}
    (hc : 2 < c) (N : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-Real.pi) Real.pi) (hxpos : ∀ i, 0 < x i)
    (hxlim : Tendsto x l (𝓝 0)) (hscale : Tendsto (fun i => N i * x i) l (𝓝 a)) :
    Tendsto (fun i => N i * ‖M c (z (x i))‖⁻¹) l (𝓝 (a / c ^ 2)) := by
  have hc0 : c ≠ 0 := by linarith
  have hr := (ratio_continuousAt_regularPart_zero c).tendsto.comp hxlim
  rw [ratio_regularPart_zero] at hr
  have ht := hscale.div hr (pow_ne_zero 2 hc0)
  apply ht.congr
  intro i
  dsimp only [Pi.div_apply, Function.comp_def]
  rw [ratio_regularPart_eq_mul_norm (hx i) (hxpos i).ne', abs_of_pos (hxpos i)]
  field_simp [(hxpos i).ne', norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (x i))]

/-- The fixed-rank midpoint factor; half-integer root scales give the
Wallis factor `1-1/(4(k+1)²)` after substitution. -/
theorem ratio_midpoint_factor_tendsto {ι : Type*} {l : Filter ι} {c a b : ℝ}
    (hc : 2 < c) (ha : 0 < a) (hb : 0 < b) (N : ι → ℝ) (hN : ∀ i, N i ≠ 0)
    (x y : ι → ℝ) (hx : ∀ i, x i ∈ Ioo (-Real.pi) Real.pi)
    (hy : ∀ i, y i ∈ Ioo (-Real.pi) Real.pi) (hxpos : ∀ i, 0 < x i) (hypos : ∀ i, 0 < y i)
    (hxlim : Tendsto x l (𝓝 0)) (hylim : Tendsto y l (𝓝 0))
    (hscaleX : Tendsto (fun i => N i * x i) l (𝓝 a))
    (hscaleY : Tendsto (fun i => N i * y i) l (𝓝 b)) :
    Tendsto (fun i => ‖M c (z ((x i + y i) / 2))‖ ^ 2 /
      (‖M c (z (x i))‖ * ‖M c (z (y i))‖)) l (𝓝 (4 * a * b / (a + b) ^ 2)) := by
  let zmid : ι → ℝ := fun i => (x i + y i) / 2
  have hmid (i : ι) : zmid i ∈ Ioo (-Real.pi) Real.pi := by
    constructor <;> dsimp [zmid] <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
  have hmidpos (i : ι) : 0 < zmid i := div_pos (add_pos (hxpos i) (hypos i)) (by norm_num)
  have hmidlim : Tendsto zmid l (𝓝 0) := by simpa [zmid] using (hxlim.add hylim).div_const 2
  have hmidscale : Tendsto (fun i => N i * zmid i) l (𝓝 ((a + b) / 2)) := by
    have ht := (hscaleX.add hscaleY).div_const 2
    apply ht.congr
    intro i
    dsimp [zmid]
    ring
  have hX := ratio_norm_div_size_tendsto (c := c) ha N hN x hx hxpos hxlim hscaleX
  have hY := ratio_norm_div_size_tendsto (c := c) hb N hN y hy hypos hylim hscaleY
  have hZ := ratio_norm_div_size_tendsto (c := c) (div_pos (add_pos ha hb) (by norm_num))
    N hN zmid hmid hmidpos hmidlim hmidscale
  have hc0 : c ≠ 0 := by linarith
  have hden : c ^ 2 / a * (c ^ 2 / b) ≠ 0 := by positivity
  have ht := (hZ.pow 2).div (hX.mul hY) hden
  have hvalue : (c ^ 2 / ((a + b) / 2)) ^ 2 / (c ^ 2 / a * (c ^ 2 / b)) =
      4 * a * b / (a + b) ^ 2 := by
    field_simp [hc0, ha.ne', hb.ne', (add_pos ha hb).ne']
    ring
  rw [hvalue] at ht
  apply ht.congr
  intro i
  change (‖M c (z (zmid i))‖ / N i) ^ 2 /
    ((‖M c (z (x i))‖ / N i) * (‖M c (z (y i))‖ / N i)) = _
  dsimp only [zmid]
  field_simp [hN i, norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (x i)),
    norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (y i))]

end PottsDiscontinuity.Bethe
