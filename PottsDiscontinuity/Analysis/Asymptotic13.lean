module

public import Mathlib
public import PottsDiscontinuity.Infra.Lambda

/-!
# The asymptotics (1.3) of the hyperbolic series

For `lam(q) = arcosh (√q / 2)` and `T(lam) = ∑_{k ≥ 0} 4 / ((2k+1) sinh (π² (2k+1) / (2 lam)))`
we prove `T(lam(q)) ~ 8 exp (-(π² / √(q - 4)))` as `q → 4⁺` (`asymptotic13`).

With `c = π² / (2 lam)` the series is `H(c) = ∑_k 4 / ((2k+1) sinh ((2k+1) c))`, and Tannery's
theorem shows `exp c * H c → 8` as `c → ∞` (`tendsto_exp_mul_hyperbolic_series`).  The exact
identity `2 sinh (arcosh (√q / 2)) = √(q - 4)` (`two_mul_sinh_arcosh_sqrt_div_two`) turns the
exponent `π² / √(q-4)` into `π² / (2 sinh lam)`, which differs from `c` by `o(1)`
(`tendsto_inv_sinh_sub_inv`).
-/

@[expose] public section

open Filter Topology Real

namespace PottsDiscontinuity

/-! ### Elementary hyperbolic estimates -/

theorem exp_div_four_le_sinh {y : ℝ} (hy : 1 ≤ y) : Real.exp y / 4 ≤ Real.sinh y := by
  rw [Real.sinh_eq]
  have h2 : (2 : ℝ) ≤ Real.exp (2 * y) := by
    have := Real.add_one_le_exp (2 * y)
    linarith
  have hexp : Real.exp (2 * y) = Real.exp y * Real.exp y := by rw [two_mul, Real.exp_add]
  have hpos := Real.exp_pos y
  have h3 : (Real.exp y)⁻¹ ≤ Real.exp y / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hpos two_pos]
    nlinarith
  rw [Real.exp_neg]
  linarith

/-- The `k`-th term of the series `H(c)`, multiplied by `exp c`, is at most `16 exp (-2 k c)`
for `c ≥ 1`. -/
theorem term_le {c : ℝ} (hc : 1 ≤ c) (k : ℕ) :
    Real.exp c * (4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) ≤
      16 * Real.exp (-(2 * (k : ℝ) * c)) := by
  have hk1 : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hy : 1 ≤ (2 * (k : ℝ) + 1) * c := by nlinarith
  have hs := exp_div_four_le_sinh hy
  have hepos := Real.exp_pos ((2 * (k : ℝ) + 1) * c)
  have h1 : 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c)) ≤
      16 * Real.exp (-((2 * (k : ℝ) + 1) * c)) := by
    calc 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))
        ≤ 4 / (Real.exp ((2 * (k : ℝ) + 1) * c) / 4) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith
      _ = 16 * Real.exp (-((2 * (k : ℝ) + 1) * c)) := by
          rw [Real.exp_neg]
          field_simp
          norm_num
  calc Real.exp c * (4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c)))
      ≤ Real.exp c * (16 * Real.exp (-((2 * (k : ℝ) + 1) * c))) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos c).le
    _ = 16 * Real.exp (-(2 * (k : ℝ) * c)) := by
        rw [← mul_assoc, mul_comm (Real.exp c) 16, mul_assoc, ← Real.exp_add]
        congr 2
        ring

theorem term_nonneg {c : ℝ} (hc : 0 < c) (k : ℕ) :
    0 ≤ Real.exp c * (4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) := by
  have : 0 < Real.sinh ((2 * (k : ℝ) + 1) * c) := Real.sinh_pos_iff.2 (by positivity)
  positivity

theorem tendsto_term_zero :
    Tendsto (fun c : ℝ => Real.exp c * (4 / ((2 * ((0 : ℕ) : ℝ) + 1) *
      Real.sinh ((2 * ((0 : ℕ) : ℝ) + 1) * c)))) atTop (𝓝 8) := by
  have h1 : Tendsto (fun c : ℝ => Real.exp (-(2 * c))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop two_pos)
  have h2 : Tendsto (fun c : ℝ => 8 / (1 - Real.exp (-(2 * c)))) atTop (𝓝 8) := by
    have := (tendsto_const_nhds (x := (8 : ℝ))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub h1) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa [Pi.div_def] using this
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  have hE : Real.exp (-(2 * c)) = (Real.exp c)⁻¹ * (Real.exp c)⁻¹ := by
    rw [show -(2 * c) = -c + -c by ring, Real.exp_add, Real.exp_neg]
  have hpos := Real.exp_pos c
  have hs : Real.sinh c = (Real.exp c - (Real.exp c)⁻¹) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg]
  have hgt : 1 < Real.exp c := Real.one_lt_exp_iff.2 hc
  have hne : Real.exp c - (Real.exp c)⁻¹ ≠ 0 := by
    have : (Real.exp c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
    linarith
  have hne2 : 1 - (Real.exp c)⁻¹ * (Real.exp c)⁻¹ ≠ 0 := by
    have h0 : (Real.exp c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
    have h00 : 0 < (Real.exp c)⁻¹ := inv_pos.2 hpos
    nlinarith
  simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]
  rw [hE, hs]
  field_simp
  ring

theorem tendsto_term_zero_of_pos {k : ℕ} (hk : 0 < k) :
    Tendsto (fun c : ℝ => Real.exp c * (4 / ((2 * (k : ℝ) + 1) *
      Real.sinh ((2 * (k : ℝ) + 1) * c)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun c : ℝ => 16 * Real.exp (-(2 * c))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (two_pos : (0 : ℝ) < 2))).const_mul 16
    simpa using this
  refine squeeze_zero' ?_ ?_ h1
  · filter_upwards [eventually_gt_atTop 0] with c hc using term_nonneg hc k
  · filter_upwards [eventually_ge_atTop 1] with c hc
    refine (term_le hc k).trans ?_
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    gcongr
    nlinarith

/-- **Tannery limit**: `exp c * ∑_k 4 / ((2k+1) sinh ((2k+1) c)) → 8` as `c → ∞`. -/
theorem tendsto_exp_mul_hyperbolic_series :
    Tendsto (fun c : ℝ => Real.exp c *
      ∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) atTop (𝓝 8) := by
  have hlt : Real.exp (-2) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hsum : Summable (fun k : ℕ => 16 * (Real.exp (-2)) ^ k) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left 16
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℝ))
    (f := fun (c : ℝ) (k : ℕ) =>
      Real.exp c * (4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))))
    (g := fun k : ℕ => if k = 0 then (8 : ℝ) else 0) hsum
    (fun k => by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using tendsto_term_zero
      · simpa [Nat.pos_iff_ne_zero.1 hk] using tendsto_term_zero_of_pos hk)
    (by
      filter_upwards [eventually_ge_atTop 1] with c hc k
      have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
      rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg hc0 k)]
      refine (term_le hc k).trans ?_
      rw [← Real.exp_nat_mul]
      have : Real.exp (-(2 * (k : ℝ) * c)) ≤ Real.exp ((k : ℝ) * -2) := by
        apply Real.exp_le_exp.2
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      linarith)
  have hg : ∑' k : ℕ, (if k = 0 then (8 : ℝ) else 0) = 8 := by
    rw [tsum_eq_single 0 (fun b hb => by simp [hb])]
    simp
  rw [hg] at hT
  refine hT.congr fun c => ?_
  rw [tsum_mul_left]

/-! ### Comparison of `1 / sinh` and `1 / x` near zero -/

theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  have hd : ∀ y : ℝ, HasDerivAt (fun x : ℝ => x * Real.cosh x - Real.sinh x)
      (y * Real.sinh y) y := by
    intro y
    have := ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y)
    convert this using 1
    · rfl
    · simp only [id]; ring
  have hmono : MonotoneOn (fun x : ℝ => x * Real.cosh x - Real.sinh x) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (fun y _ => (hd y).continuousAt.continuousWithinAt)
    · exact (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hd y).deriv]
      exact mul_nonneg (le_of_lt hy) (Real.sinh_nonneg_iff.2 (le_of_lt hy))
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simpa using this

theorem inv_sub_inv_sinh_le {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 / x - 1 / Real.sinh x ∧ 1 / x - 1 / Real.sinh x ≤ (Real.cosh x - 1) / x := by
  have hs : x ≤ Real.sinh x := Real.self_le_sinh_iff.2 hx.le
  have hspos : 0 < Real.sinh x := lt_of_lt_of_le hx hs
  have hc1 : 1 ≤ Real.cosh x := Real.one_le_cosh x
  have hsc := sinh_le_mul_cosh hx.le
  have e : 1 / x - 1 / Real.sinh x = (Real.sinh x - x) / (x * Real.sinh x) := by
    field_simp
  rw [e]
  constructor
  · apply div_nonneg <;> nlinarith
  · rw [div_le_div_iff₀ (by positivity) hx]
    nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hs)]

theorem tendsto_cosh_sub_one_div :
    Tendsto (fun x : ℝ => (Real.cosh x - 1) / x) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.hasDerivAt_cosh 0).tendsto_slope_zero_right
  simp only [Real.sinh_zero, zero_add, Real.cosh_zero, smul_eq_mul] at h
  refine h.congr fun x => ?_
  rw [inv_mul_eq_div]

theorem tendsto_inv_sinh_sub_inv :
    Tendsto (fun x : ℝ => 1 / Real.sinh x - 1 / x) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => 1 / x - 1 / Real.sinh x) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ tendsto_cosh_sub_one_div
    · filter_upwards [self_mem_nhdsWithin] with x hx using (inv_sub_inv_sinh_le hx).1
    · filter_upwards [self_mem_nhdsWithin] with x hx using (inv_sub_inv_sinh_le hx).2
  have := h.neg
  simp only [neg_zero] at this
  refine this.congr fun x => ?_
  ring

/-! ### The parameter `lam(q) = arcosh (√q / 2)` -/

theorem two_mul_sinh_arcosh_sqrt_div_two {q : ℝ} (hq : 4 < q) :
    2 * Real.sinh (Real.arcosh (Real.sqrt q / 2)) = Real.sqrt (q - 4) := by
  have h2 : (2 : ℝ) < Real.sqrt q := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hq
  rw [Real.sinh_arcosh (by linarith)]
  have h4 : (Real.sqrt q / 2) ^ 2 - 1 = (q - 4) / 2 ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by linarith)]
    ring
  rw [h4, Real.sqrt_div (by linarith), Real.sqrt_sq (by norm_num)]
  ring

theorem tendsto_arcosh_sqrt_div_two :
    Tendsto (fun q : ℝ => Real.arcosh (Real.sqrt q / 2)) (𝓝[>] 4) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · -- `lam = arsinh (sinh lam) = arsinh (√(q-4)/2) → arsinh 0 = 0`
    have hs : Tendsto (fun q : ℝ => Real.sqrt (q - 4) / 2) (𝓝[>] 4) (𝓝 0) := by
      have h1 : Tendsto (fun q : ℝ => q - 4) (𝓝[>] 4) (𝓝 0) := by
        have hcont : Continuous (fun q : ℝ => q - 4) := by fun_prop
        have := hcont.tendsto (4 : ℝ)
        simpa using tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (4 : ℝ)) this
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      simpa using h2.div_const 2
    have h3 := (Real.continuous_arsinh.tendsto 0).comp hs
    rw [Real.arsinh_zero] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq' : 4 < q := hq
    simp only [Function.comp]
    rw [← two_mul_sinh_arcosh_sqrt_div_two hq']
    rw [show 2 * Real.sinh (Real.arcosh (Real.sqrt q / 2)) / 2 =
      Real.sinh (Real.arcosh (Real.sqrt q / 2)) by ring, Real.arsinh_sinh]
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact (arcosh_pos_of_gt4 q hq).1

/-! ### The asymptotic equivalence -/

theorem asymptotic13 :
    Asymptotics.IsEquivalent (𝓝[>] (4 : ℝ))
      (fun q => ∑' k : ℕ, 4 / ((2 * k + 1) *
        Real.sinh (π ^ 2 * (2 * k + 1) / (2 * Real.arcosh (Real.sqrt q / 2)))))
      (fun q => 8 * Real.exp (-(π ^ 2 / Real.sqrt (q - 4)))) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  set L : ℝ → ℝ := fun q => Real.arcosh (Real.sqrt q / 2) with hL
  have hLt : Tendsto L (𝓝[>] 4) (𝓝[>] 0) := tendsto_arcosh_sqrt_div_two
  have hc : Tendsto (fun q => π ^ 2 / 2 * (L q)⁻¹) (𝓝[>] 4) atTop :=
    Tendsto.const_mul_atTop (by positivity) (tendsto_inv_nhdsGT_zero.comp hLt)
  have hG := tendsto_exp_mul_hyperbolic_series.comp hc
  have hd : Tendsto (fun q => π ^ 2 / Real.sqrt (q - 4) - π ^ 2 / 2 * (L q)⁻¹) (𝓝[>] 4) (𝓝 0) := by
    have h1 := (tendsto_inv_sinh_sub_inv.comp hLt).const_mul (π ^ 2 / 2)
    simp only [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq' : 4 < q := hq
    have h2 := two_mul_sinh_arcosh_sqrt_div_two hq'
    simp only [Function.comp]
    rw [← h2]
    have hpos : 0 < Real.sinh (L q) := Real.sinh_pos_iff.2 (arcosh_pos_of_gt4 q hq').1
    simp only [hL] at hpos ⊢
    field_simp
  have hlim := (hG.div_const 8).mul (hd.rexp)
  simp only [Real.exp_zero, mul_one] at hlim
  rw [show (8 : ℝ) / 8 = 1 by norm_num] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq' : 4 < q := hq
  have hLpos : 0 < L q := (arcosh_pos_of_gt4 q hq').1
  have hsq : 0 < Real.sqrt (q - 4) := Real.sqrt_pos.2 (by linarith)
  simp only [Function.comp, Pi.div_apply]
  set c := π ^ 2 / 2 * (L q)⁻¹ with hcdef
  set s := π ^ 2 / Real.sqrt (q - 4) with hsdef
  have hu : (∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) *
      Real.sinh (π ^ 2 * (2 * k + 1) / (2 * Real.arcosh (Real.sqrt q / 2))))) =
      ∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c)) := by
    refine tsum_congr fun k => ?_
    congr 3
    simp only [hcdef, hL]
    field_simp
  rw [hu]
  generalize (∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) = H
  rw [Real.exp_sub, Real.exp_neg]
  have h1 := Real.exp_pos c
  have h2 := Real.exp_pos s
  field_simp

end PottsDiscontinuity
