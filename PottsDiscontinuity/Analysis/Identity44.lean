module

public import Mathlib
public import PottsDiscontinuity.Analysis.HyperbolicSeries

/-!
# The identity (4.4): convergence, positivity and the value of the alternating tanh series

For every `lam > 0`, the partial sums `∑_{k=1}^N (-1)^k / k * tanh (k lam)` converge to a limit
`S`, the series `∑_{k ≥ 0} 4 / ((2k+1) sinh (π² (2k+1) / (2 lam)))` has a sum `T`, and
`lam + 2 S = T > 0` (`identity44`).

The proof expands `tanh (m lam) / m = ∑_j c_j(m)` into partial fractions
(`hasSum_cTerm_tanh`), interchanges the (conditionally convergent) double series with Tannery's
theorem, using the alternating-series bound `|∑_{m ≤ N} (-1)^m c_j(m)| ≤ c_j(1)`
(`alt_partial_sum_bounds`), and evaluates the inner alternating series in closed form
(`hasSum_alt_cTerm`).
-/

@[expose] public section

open Filter Topology Real

namespace PottsDiscontinuity

/-! ### Alternating partial sums of an antitone nonnegative sequence -/

theorem alt_partial_sum_bounds : ∀ (N : ℕ) (u : ℕ → ℝ), Antitone u → (∀ i, 0 ≤ u i) →
    0 ≤ ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * u i ∧
      ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * u i ≤ u 0
  | 0, u, _, h0 => by simp [h0 0]
  | N + 1, u, hu, h0 => by
    have ih := alt_partial_sum_bounds N (fun i => u (i + 1))
      (fun a b hab => hu (by omega)) (fun i => h0 _)
    have h01 : u 1 ≤ u 0 := hu (by omega)
    rw [Finset.sum_range_succ']
    have e : ∑ i ∈ Finset.range N, (-1 : ℝ) ^ (i + 1) * u (i + 1) =
        -∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * u (i + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ]
      ring
    rw [e]
    simp only [pow_zero, one_mul]
    constructor <;> linarith [ih.1, ih.2]

theorem sum_Icc_one_eq_sum_range (g : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, g k = ∑ n ∈ Finset.range N, g (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-! ### The sum of the odd reciprocal squares -/

theorem hasSum_odd_inv_sq : HasSum (fun j : ℕ => 1 / (2 * (j : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
  have hz := hasSum_zeta_two
  have hev : HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2) (π ^ 2 / 6 / 4) := by
    have h := hz.div_const 4
    convert h using 1
    funext k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · push_cast
      have : (k : ℝ) ≠ 0 := by positivity
      field_simp
      norm_num
  have hodd : Summable (fun j : ℕ => 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2) :=
    hz.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) (fun x y h => by simp only at h; omega)
  have h2 := HasSum.even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) hev hodd.hasSum
  have h3 := hz.unique h2
  have e : ∑' j : ℕ, 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2 = π ^ 2 / 8 := by linarith
  rw [← e]
  convert hodd.hasSum using 1
  funext j
  push_cast
  rfl

theorem hasSum_odd_inv_sq_mul (c : ℝ) :
    HasSum (fun j : ℕ => c / (2 * (j : ℝ) + 1) ^ 2) (c * (π ^ 2 / 8)) := by
  convert hasSum_odd_inv_sq.mul_left c using 1
  funext j
  rw [mul_one_div]

/-! ### The partial-fraction terms -/

/-- `c_j(m) = 8 lam / ((2j+1)² π² + 4 m² lam²)`, so that `tanh (m lam) / m = ∑_j c_j(m)`. -/
noncomputable def cTerm (lam : ℝ) (j : ℕ) (m : ℝ) : ℝ :=
  8 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2 + 4 * m ^ 2 * lam ^ 2)

/-- The closed form of the inner alternating series. -/
noncomputable def dTerm (lam : ℝ) (j : ℕ) : ℝ :=
  2 / ((2 * (j : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam))) -
    4 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2)

theorem cTerm_pos {lam : ℝ} (hlam : 0 < lam) (j : ℕ) (m : ℝ) : 0 < cTerm lam j m := by
  unfold cTerm
  positivity

theorem hasSum_cTerm_tanh {lam : ℝ} (hlam : 0 < lam) {m : ℝ} (hm : 0 < m) :
    HasSum (fun j : ℕ => cTerm lam j m) (Real.tanh (m * lam) / m) := by
  have ha : 0 < 2 * m * lam / π := by positivity
  have h := (hasSum_inv_sq_add_odd_sq ha).mul_left (8 * lam / π ^ 2)
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hm0 : m ≠ 0 := hm.ne'
  have hl0 : lam ≠ 0 := hlam.ne'
  convert h using 1
  · funext j
    unfold cTerm
    field_simp
    ring
  · rw [show π * (2 * m * lam / π) / 2 = m * lam by field_simp]
    field_simp
    ring

theorem hasSum_alt_cTerm {lam : ℝ} (hlam : 0 < lam) (j : ℕ) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * cTerm lam j ((n : ℝ) + 1)) (dTerm lam j) := by
  set b : ℝ := (2 * (j : ℝ) + 1) * π / (2 * lam) with hb
  have hbpos : 0 < b := by positivity
  have h := (hasSum_nat_add_iff' (f := fun n : ℕ => (-1 : ℝ) ^ n / (b ^ 2 + (n : ℝ) ^ 2)) 1
    (g := π / (2 * b * Real.sinh (π * b)) + 1 / (2 * b ^ 2))).2 (hasSum_alt_inv_sq_add_sq hbpos)
  have h2 := h.mul_left (2 / lam)
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hl0 : lam ≠ 0 := hlam.ne'
  have hb0 : b ≠ 0 := hbpos.ne'
  have hj : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  convert h2 using 1
  · funext n
    unfold cTerm
    simp only [hb]
    push_cast
    have : ((n : ℝ) + 1) ^ 2 * (4 * lam ^ 2) + (2 * (j : ℝ) + 1) ^ 2 * π ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  · unfold dTerm
    simp only [Finset.sum_range_one, Nat.cast_zero, pow_zero, zero_pow two_ne_zero, add_zero,
      one_div]
    have e : π * b = π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam) := by
      simp only [hb]
      field_simp
    rw [e]
    simp only [hb]
    have hs : Real.sinh (π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam)) ≠ 0 :=
      (Real.sinh_pos_iff.2 (by positivity)).ne'
    field_simp
    ring

/-! ### Bounds -/

theorem cTerm_antitone {lam : ℝ} (hlam : 0 < lam) (j : ℕ) :
    Antitone (fun n : ℕ => cTerm lam j ((n : ℝ) + 1)) := by
  intro a b hab
  unfold cTerm
  have hab' : ((a : ℝ) + 1) ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hab
  have hpos : 0 < (2 * (j : ℝ) + 1) ^ 2 * π ^ 2 + 4 * ((a : ℝ) + 1) ^ 2 * lam ^ 2 := by positivity
  apply div_le_div_of_nonneg_left (by positivity) hpos
  have h0 : (0 : ℝ) ≤ (a : ℝ) + 1 := by positivity
  nlinarith [sq_nonneg lam, mul_le_mul hab' hab' h0 (by positivity)]

theorem cTerm_one_le {lam : ℝ} (hlam : 0 < lam) (j : ℕ) :
    cTerm lam j (((0 : ℕ) : ℝ) + 1) ≤ 8 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2) := by
  unfold cTerm
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [sq_nonneg lam]

/-- The partial sums of the inner alternating series are dominated by `c_j(1)`. -/
theorem norm_partial_cTerm_le {lam : ℝ} (hlam : 0 < lam) (j N : ℕ) :
    ‖∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * cTerm lam j ((n : ℝ) + 1)‖ ≤
      8 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2) := by
  have hb := alt_partial_sum_bounds N (fun n : ℕ => cTerm lam j ((n : ℝ) + 1))
    (cTerm_antitone hlam j) (fun i => (cTerm_pos hlam j _).le)
  have e : ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * cTerm lam j ((n : ℝ) + 1) =
      -∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * cTerm lam j ((n : ℝ) + 1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ]
    ring
  rw [e, norm_neg, Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2.trans (cTerm_one_le hlam j)

theorem summable_bound {lam : ℝ} (hlam : 0 < lam) :
    HasSum (fun j : ℕ => 8 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2)) (lam) := by
  have h := hasSum_odd_inv_sq_mul (8 * lam / π ^ 2)
  have hpi : π ≠ 0 := Real.pi_ne_zero
  convert h using 1
  · funext j
    have : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · field_simp

/-! ### The terms `4 / ((2k+1) sinh (π² (2k+1) / (2 lam)))` -/

theorem tTerm_pos {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    0 < 4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam))) := by
  have : 0 < Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam)) :=
    Real.sinh_pos_iff.2 (by positivity)
  positivity

theorem tTerm_le {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam))) ≤
      8 * lam / ((2 * (k : ℝ) + 1) ^ 2 * π ^ 2) := by
  have hy : 0 < π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam) := by positivity
  have hs : π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam) ≤
      Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam)) := Real.self_le_sinh_iff.2 hy.le
  have hk : 0 < 2 * (k : ℝ) + 1 := by positivity
  calc 4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam)))
      ≤ 4 / ((2 * (k : ℝ) + 1) * (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam))) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_left hs hk.le
    _ = 8 * lam / ((2 * (k : ℝ) + 1) ^ 2 * π ^ 2) := by
        field_simp
        norm_num

theorem summable_tTerm {lam : ℝ} (hlam : 0 < lam) :
    Summable (fun k : ℕ =>
      4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam)))) :=
  Summable.of_nonneg_of_le (fun k => (tTerm_pos hlam k).le) (fun k => tTerm_le hlam k)
    (summable_bound hlam).summable

theorem dTerm_eq {lam : ℝ} (hlam : 0 < lam) (j : ℕ) :
    dTerm lam j =
      (4 / ((2 * (j : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam)))) / 2 -
        4 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2) := by
  unfold dTerm
  have hs : Real.sinh (π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam)) ≠ 0 :=
    (Real.sinh_pos_iff.2 (by positivity)).ne'
  have : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  generalize Real.sinh (π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam)) = s at hs ⊢
  field_simp
  ring

/-! ### The main identity -/

/-- **Identity (4.4)** together with the convergence and positivity statements: for every
`lam > 0`, the partial sums of `∑ (-1)^k / k * tanh (k lam)` converge to `S`, the hyperbolic series
sums to `T`, and `lam + 2 S = T > 0`. -/
theorem identity44 (lam : ℝ) (hlam : 0 < lam) :
    ∃ S T : ℝ,
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
          (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
      HasSum (fun k : ℕ => 4 / ((2 * k + 1) * Real.sinh (π ^ 2 * (2 * k + 1) / (2 * lam)))) T ∧
      0 < lam + 2 * S ∧ lam + 2 * S = T := by
  have hT := (summable_tTerm hlam).hasSum
  set T := ∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam)))
    with hTdef
  have hTpos : 0 < T := (summable_tTerm hlam).tsum_pos (fun k => (tTerm_pos hlam k).le) 0
    (tTerm_pos hlam 0)
  have hd : HasSum (fun j : ℕ => dTerm lam j) (T / 2 - lam / 2) := by
    have h := (hT.div_const 2).sub ((hasSum_odd_inv_sq_mul (4 * lam / π ^ 2)))
    have hpi : π ≠ 0 := Real.pi_ne_zero
    convert h using 1
    · funext j
      rw [dTerm_eq hlam j]
      have : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    · field_simp
      ring
  set S := ∑' j : ℕ, dTerm lam j with hSdef
  have hS : S = T / 2 - lam / 2 := hd.tsum_eq
  refine ⟨S, T, ?_, hT, by rw [hS]; linarith, by rw [hS]; ring⟩
  -- Tannery
  have hf : ∀ N : ℕ, ∑ k ∈ Finset.Icc 1 N, (-1 : ℝ) ^ k / k * Real.tanh (k * lam) =
      ∑' j : ℕ, ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * cTerm lam j ((n : ℝ) + 1) := by
    intro N
    rw [Summable.tsum_finsetSum, sum_Icc_one_eq_sum_range]
    · refine Finset.sum_congr rfl fun n _ => ?_
      have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [(hasSum_cTerm_tanh hlam hm).mul_left ((-1 : ℝ) ^ (n + 1)) |>.tsum_eq]
      push_cast
      ring
    · intro n _
      have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact ((hasSum_cTerm_tanh hlam hm).mul_left ((-1 : ℝ) ^ (n + 1))).summable
  simp_rw [hf]
  exact tendsto_tsum_of_dominated_convergence (summable_bound hlam).summable
    (fun j => (hasSum_alt_cTerm hlam j).tendsto_sum_nat)
    (Eventually.of_forall fun N j => norm_partial_cTerm_le hlam j N)

end PottsDiscontinuity
