module

public import PottsDiscontinuity.CorrLength.Positivity
public import PottsDiscontinuity.CorrLength.SubadditiveRate
public import PottsDiscontinuity.CorrLength.RotatedLattice

/-!
# Existence of the correlation-length rate

The finite-distance connection probabilities are positive and
supermultiplicative. Fekete's lemma applied to their negative logarithms gives
the diagonal rate; the frozen sites `diagonalSite n` repeat each diagonal point
at the two consecutive indices `2*m` and `2*m+1`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.CorrLength

open PottsDiscontinuity.FK

noncomputable section

/-- The free-limit connection probability at the diagonal point `(n,n)`. -/
def diagonalConnectionProbability (μ : Measure LatticeConfiguration) (n : ℕ) : ℝ :=
  μ.real (connectionEvent (0, 0) ((n : ℤ), (n : ℤ)))

private theorem diagonalConnectionProbability_pos (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) (n : ℕ) :
    0 < diagonalConnectionProbability μ n := by
  exact isRCInfiniteVolumeLimit_connection_positive θ μ hμ (0, 0) ((n : ℤ), (n : ℤ))

private theorem diagonalConnectionProbability_le_one (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      (θ.toP) (θ.toQ) 0 μ) (n : ℕ) :
    diagonalConnectionProbability μ n ≤ 1 := by
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  have hle := ProbabilityMeasure.apply_le_one ν
    (connectionEvent (0, 0) ((n : ℤ), (n : ℤ)))
  have heq : diagonalConnectionProbability μ n =
      ((ν (connectionEvent (0, 0) ((n : ℤ), (n : ℤ))) : NNReal) : ℝ) := by
    change (ν : Measure LatticeConfiguration).real
        (connectionEvent (0, 0) ((n : ℤ), (n : ℤ))) = _
    exact ProbabilityMeasure.measureReal_eq_coe_coeFn ν _
  rw [heq]
  exact_mod_cast hle

private theorem diagonalConnectionProbability_supermultiplicative
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) (m n : ℕ) :
    diagonalConnectionProbability μ m * diagonalConnectionProbability μ n ≤
      diagonalConnectionProbability μ (m + n) := by
  have h := isRCInfiniteVolumeLimit_origin_connection_supermultiplicative θ μ hμ
    ((m : ℤ), (m : ℤ)) ((n : ℤ), (n : ℤ))
  simpa [diagonalConnectionProbability, Nat.cast_add] using h

/-- There is a finite nonnegative limit for the negative logarithmic rate along
the points `(n,n)`. -/
theorem diagonal_correlation_rate_exists (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) :
    ∃ aInf : ℝ, 0 ≤ aInf ∧ aInf ≤ -Real.log (diagonalConnectionProbability μ 1) ∧
      Tendsto (fun n : ℕ =>
        -Real.log (diagonalConnectionProbability μ n) / (n : ℝ)) atTop (𝓝 aInf) := by
  exact log_rate_of_supermultiplicative (diagonalConnectionProbability μ)
    (diagonalConnectionProbability_pos θ μ hμ)
    (diagonalConnectionProbability_le_one θ μ hμ)
    (diagonalConnectionProbability_supermultiplicative θ μ hμ)

/-- Reindexing the free-limit connection probabilities by the frozen sites
`xₙ = diagonalSite n` halves the diagonal rate. -/
theorem diagonalSite_correlation_rate_exists (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) :
    ∃ aInf : ℝ, 0 ≤ aInf ∧
      Tendsto (fun n : ℕ =>
        -Real.log (μ.real (connectionEvent (0, 0)
          (PottsDiscontinuity.diagonalSite n))) / (n : ℝ))
        atTop (𝓝 (aInf / 2)) := by
  obtain ⟨aInf, haInf, _, hrate⟩ := diagonal_correlation_rate_exists θ μ hμ
  let a : ℕ → ℝ := fun m => -Real.log (diagonalConnectionProbability μ m)
  let b : ℕ → ℝ := fun n =>
    -Real.log (μ.real (connectionEvent (0, 0)
      (PottsDiscontinuity.diagonalSite n)))
  have hEven (m : ℕ) : b (2 * m) = a m := by
    simp [a, b, diagonalConnectionProbability, diagonalSite_even]
  have hOdd (m : ℕ) : b (2 * m + 1) = a m := by
    simp [a, b, diagonalConnectionProbability, diagonalSite_odd]
  have hrate' : Tendsto (fun m : ℕ => a m / (m : ℝ)) atTop (𝓝 aInf) := by
    simpa [a] using hrate
  have hdiag := tendsto_rate_of_even_odd_subsequence a b aInf hrate' hEven hOdd
  refine ⟨aInf, haInf, ?_⟩
  simpa [b] using hdiag

end

end PottsDiscontinuity.CorrLength
