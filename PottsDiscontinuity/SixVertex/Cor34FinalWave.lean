module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34BethePF

/-! # Corollary 3.4: nonvanishing of the normalized block wave -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.SixVertex

/-- The nonzero source coordinate wave transfers to the zero-based particle block by the
one-site shift phase. -/
theorem cor34_final_eventually_normalizedBlockWave_ne_zero {N n : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hN : 0 < N) (hn : 2 * n ≤ N) :
    ∀ᶠ ε in 𝓝[<] (0 : ℝ),
      cor34_normalizedBlockWave (N := N) ε (p ε) ≠ 0 := by
  have hsource := cor34_eventually_normalizedCoordinate_ne_zero hp hp0 hN hn
  have hsourceLeft := hsource.filter_mono
    (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ)))
  filter_upwards [hsourceLeft, self_mem_nhdsWithin] with ε hsource hε
  have hpos : cor34_sourceEvenPositions =
      fun k => BetheAnsatz.positions (cor34_evenCoordinateState hn) k + 1 := by
    funext k
    rw [cor34_evenCoordinateState_positions hn]
    simp [cor34_sourceEvenPositions]
    omega
  have hcoordinate :
      cor34_normalizedCoordinate ε (p ε) cor34_sourceEvenPositions =
        Complex.exp (Complex.I * ((∑ j, p ε j : ℝ) : ℂ)) *
          cor34_normalizedCoordinate ε (p ε)
            (BetheAnsatz.positions (cor34_evenCoordinateState hn)) := by
    have hεne : ε ≠ 0 := ne_of_lt hε
    rw [cor34_normalizedCoordinate_eq_scaled_coordinateWave ε (p ε)
      cor34_sourceEvenPositions hεne,
      cor34_normalizedCoordinate_eq_scaled_coordinateWave ε (p ε)
      (BetheAnsatz.positions (cor34_evenCoordinateState hn)) hεne]
    rw [hpos, BetheAnsatz.coordinateWave_add_one]
    ring
  have hblock :
      cor34_normalizedCoordinate ε (p ε) cor34_sourceEvenPositions =
        Complex.exp (Complex.I * ((∑ j, p ε j : ℝ) : ℂ)) *
          cor34_normalizedBlockWave (N := N) ε (p ε) (cor34_evenCoordinateState hn) := by
    simpa [cor34_normalizedBlockWave] using hcoordinate
  have hphase : Complex.exp (Complex.I * ((∑ j, p ε j : ℝ) : ℂ)) ≠ 0 :=
    BetheAnsatz.coordinate_shift_phase_ne_zero (p ε)
  have hvalue :
      cor34_normalizedBlockWave (N := N) ε (p ε) (cor34_evenCoordinateState hn) ≠ 0 := by
    intro hz
    apply hsource
    rw [hblock, hz, mul_zero]
  intro hwave
  exact hvalue (congrFun hwave (cor34_evenCoordinateState hn))

end PottsDiscontinuity.SixVertex
