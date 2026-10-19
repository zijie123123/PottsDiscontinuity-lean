module

public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite

/-!
# A positive logarithmic rate gives a diagonal exponential bound

The index here is exactly the frozen index: `diagonalSite n = (⌊n/2⌋,⌊n/2⌋)`.
The theorem does not substitute `(n,n)` or infer off-diagonal bounds.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.Duality

/-- Every smaller positive rate admits a uniform exponential bound, absorbing
the finite initial segment into the prefactor. No positivity of `f` is needed. -/
theorem exponential_bound_of_pos_logarithmic_rate
    (f : ℕ → ℝ) (hf : ∀ n, f n ≤ 1) (L c : ℝ) (hc : 0 < c) (hcL : c < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (f n)) atTop (𝓝 L)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, f n ≤ C * Real.exp (-c * (n : ℝ)) := by
  have hevent := hrate.eventually (eventually_gt_nhds hcL)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hevent.and (eventually_ge_atTop 1))
  refine ⟨Real.exp (c * (N : ℝ)), Real.exp_pos _, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast (hN n hn).2
    have hdiv : c < -Real.log (f n) / (n : ℝ) := by
      convert (hN n hn).1 using 1; ring
    have hlog : Real.log (f n) ≤ -c * (n : ℝ) := by
      have hmul := (lt_div_iff₀ hnpos).1 hdiv
      linarith only [hmul]
    have hC : 1 ≤ Real.exp (c * (N : ℝ)) :=
      Real.one_le_exp_iff.2 (mul_nonneg hc.le (Nat.cast_nonneg _))
    calc
      f n ≤ Real.exp (-c * (n : ℝ)) := Real.le_exp_of_log_le hlog
      _ ≤ Real.exp (c * (N : ℝ)) * Real.exp (-c * (n : ℝ)) := by
        exact le_mul_of_one_le_left (Real.exp_nonneg _) hC
  · have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hn))
    calc
      f n ≤ 1 := hf n
      _ ≤ Real.exp (c * (N : ℝ)) * Real.exp (-c * (n : ℝ)) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        nlinarith only [mul_nonneg hc.le (sub_nonneg.2 hnN)]

/-- Apply the quantitative rate lemma to the exact frozen diagonal two-point
probabilities of any probability measure on lattice configurations. -/
theorem diagonal_exponential_bound_of_pos_rate
    (μ : Measure FK.LatticeConfiguration) [IsProbabilityMeasure μ]
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
      Real.log (μ.real (connectionEvent 0 (diagonalSite n)))) atTop (𝓝 L)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      μ.real (connectionEvent 0 (diagonalSite n)) ≤ C * Real.exp (-c * (n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exponential_bound_of_pos_logarithmic_rate
    (fun n => μ.real (connectionEvent 0 (diagonalSite n)))
    (fun _ => measureReal_le_one) L (L / 2) (by positivity) (by linarith only [hL]) hrate
  exact ⟨C, L / 2, hC, by positivity, hbound⟩

end PottsDiscontinuity.Duality
