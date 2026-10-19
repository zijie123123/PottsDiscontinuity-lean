module

public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Fekete's lemma for connection probabilities

This module isolates the analytic step used once the finite-distance
connection probabilities are known to be positive and supermultiplicative.
-/

@[expose] public section

namespace PottsDiscontinuity.CorrLength

open Filter Topology

/-- A nonnegative subadditive sequence has a finite asymptotic rate. -/
theorem nonnegative_subadditive_rate (a : ℕ → ℝ)
    (hsub : Subadditive a) (ha : ∀ n, 0 ≤ a n) :
    0 ≤ hsub.lim ∧ hsub.lim ≤ a 1 ∧
      Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 hsub.lim) := by
  have hbdd : BddBelow (Set.range fun n : ℕ => a n / (n : ℝ)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact div_nonneg (ha n) (Nat.cast_nonneg n)
  have hlim := hsub.tendsto_lim hbdd
  have hnonneg : 0 ≤ hsub.lim := by
    rw [Subadditive.lim]
    apply le_csInf
    · exact ⟨a 1 / (1 : ℝ), ⟨1, by norm_num, by norm_num⟩⟩
    · rintro x ⟨n, hn, rfl⟩
      exact div_nonneg (ha n) (Nat.cast_nonneg n)
  have hle := hsub.lim_le_div hbdd (by norm_num : (1 : ℕ) ≠ 0)
  have hle' : hsub.lim ≤ a 1 := by simpa using hle
  exact ⟨hnonneg, hle', hlim⟩

/-- Positive supermultiplicative probabilities yield a finite limit for their
negative logarithms divided by the distance parameter. -/
theorem log_rate_of_supermultiplicative (p : ℕ → ℝ)
    (hp : ∀ n, 0 < p n) (hpone : ∀ n, p n ≤ 1)
    (hmul : ∀ m n, p m * p n ≤ p (m + n)) :
    ∃ L : ℝ, 0 ≤ L ∧ L ≤ -Real.log (p 1) ∧
      Tendsto (fun n : ℕ => -Real.log (p n) / (n : ℝ)) atTop (𝓝 L) := by
  let a : ℕ → ℝ := fun n => -Real.log (p n)
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    dsimp [a]
    have hlog : Real.log (p n) ≤ Real.log 1 :=
      Real.log_le_log (hp n) (hpone n)
    have hlog' : Real.log (p n) ≤ 0 := by simpa using hlog
    exact neg_nonneg.mpr hlog'
  have hsub : Subadditive a := by
    intro m n
    dsimp [a]
    have hlog : Real.log (p m * p n) ≤ Real.log (p (m + n)) :=
      Real.log_le_log (mul_pos (hp m) (hp n)) (hmul m n)
    rw [Real.log_mul (hp m).ne' (hp n).ne'] at hlog
    linarith
  obtain ⟨hL0, hL1, hlim⟩ := nonnegative_subadditive_rate a hsub ha
  refine ⟨hsub.lim, hL0, ?_, ?_⟩
  · simpa [a] using hL1
  · simpa [a] using hlim

/-- Reindexing a sequence by the diagonal sites `diagonalSite n` halves its
per-site logarithmic rate. The only input is the exact identity
`diagonalSite (2*m) = diagonalSite (2*m+1) = (m,m)`. -/
theorem tendsto_rate_of_even_odd_subsequence (a b : ℕ → ℝ) (L : ℝ)
    (h : Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 L))
    (heven : ∀ m, b (2 * m) = a m)
    (hodd : ∀ m, b (2 * m + 1) = a m) :
    Tendsto (fun n : ℕ => b n / (n : ℝ)) atTop (𝓝 (L / 2)) := by
  have hdouble : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with m hm
    omega
  have hevenLim : Tendsto (fun m : ℕ => b (2 * m) / ((2 * m : ℕ) : ℝ)) atTop
      (𝓝 (L / 2)) := by
    have h' : Tendsto (fun m : ℕ => (a m / (m : ℝ)) / 2) atTop (𝓝 (L / 2)) :=
      h.div_const 2
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    rw [heven m]
    push_cast
    field_simp
  have hfrac : Tendsto (fun m : ℕ => (m : ℝ) / (2 * (m : ℝ) + 1)) atTop
      (𝓝 (1 / 2)) := by
    simpa [add_comm] using tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ) 0 1 1
      (d := 2) (by norm_num)
  have hoddLim : Tendsto (fun m : ℕ => b (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ)) atTop
      (𝓝 (L / 2)) := by
    have h' : Tendsto (fun m : ℕ => (a m / (m : ℝ)) *
        ((m : ℝ) / (2 * (m : ℝ) + 1))) atTop (𝓝 (L * (1 / 2))) := h.mul hfrac
    have h'' : L * (1 / 2) = L / 2 := by ring
    rw [h''] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    rw [hodd m]
    push_cast
    field_simp
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro x hx
    have hresidue (k : ℕ) (hk : k < 2) :
        ∀ᶠ m : ℕ in atTop, x < b (2 * m + k) / ((2 * m + k : ℕ) : ℝ) := by
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · simpa using hevenLim.eventually (Ioi_mem_nhds hx)
      · simpa using hoddLim.eventually (Ioi_mem_nhds hx)
    exact Filter.Eventually.atTop_of_arithmetic
      (p := fun n => x < b n / (n : ℝ)) (n := 2) (by norm_num) hresidue
  · intro y hy
    have hresidue (k : ℕ) (hk : k < 2) :
        ∀ᶠ m : ℕ in atTop, b (2 * m + k) / ((2 * m + k : ℕ) : ℝ) < y := by
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · simpa using hevenLim.eventually (Iio_mem_nhds hy)
      · simpa using hoddLim.eventually (Iio_mem_nhds hy)
    exact Filter.Eventually.atTop_of_arithmetic
      (p := fun n => b n / (n : ℝ) < y) (n := 2) (by norm_num) hresidue

end PottsDiscontinuity.CorrLength
