module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.DistinctMeasures
public import PottsDiscontinuity.Duality.WiredPercolation

/-! The discontinuity consequences of positive diagonal decay, including the
exact parameter/event form consumed by Theorem 1.2 items 1–2. Neither the
theorem-statement modules (`Frozen/`) nor the provider modules (`Provider/`) are imported. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK MeasureTheory Filter Topology
noncomputable section

/-- All four discontinuity consequences under an explicit full ℓ¹ decay bound. -/
theorem critical_discontinuity_of_exponential_decay (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ₁)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ₀ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    μ₀ (infiniteClusterAt 0) = 0 ∧ 0 < μ₁ (infiniteClusterAt 0) ∧
      μ₁ existsInfiniteCluster = 1 ∧ μ₁ ≠ μ₀ := by
  have := hμ₀.1
  have hμ₁dual : IsRCInfiniteVolumeLimit (dualParameters (criticalParameters q)).toP
      (dualParameters (criticalParameters q)).toQ 1 μ₁ := by
    simpa only [dualParameters_criticalParameters] using hμ₁
  refine ⟨?_, wired_origin_pos_of_free_exponential_decay (criticalParameters q)
    μ₀ μ₁ hμ₀ hμ₁dual C c hC hc hdecay,
    wired_existsInfiniteCluster_eq_one_of_free_decay (criticalParameters q)
      μ₀ μ₁ hμ₀ hμ₁dual C c hC hc hdecay,
    (free_ne_wired_at_critical_of_exponential_decay q μ₀ μ₁ hμ₀ hμ₁ C c hC hc hdecay).symm⟩
  apply infiniteClusterAt_zero_of_exponential_decay μ₀ C c hc
  intro x
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ₀ _)]
  exact ENNReal.ofReal_le_ofReal (hdecay x)

/-- The rate is taken along the exact frozen points
`diagonalSite n = (floor(n/2), floor(n/2))`, with normalization 1/n. -/
theorem critical_discontinuity_of_pos_diagonal_rate (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ₁)
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
      Real.log (twoPoint μ₀ (diagonalSite n))) atTop (𝓝 L)) :
    μ₀ (infiniteClusterAt 0) = 0 ∧ 0 < μ₁ (infiniteClusterAt 0) ∧
      μ₁ existsInfiniteCluster = 1 ∧ μ₁ ≠ μ₀ := by
  obtain ⟨C,c,hC,hc,hb⟩ := free_exponential_decay_of_pos_diagonal_rate
    (criticalParameters q) μ₀ hμ₀ L hL hrate
  exact critical_discontinuity_of_exponential_decay q μ₀ μ₁ hμ₀ hμ₁ C c hC.le hc hb

/-- Positive origin percolation also holds for real-valued probabilities. -/
theorem wired_origin_real_pos_at_critical_of_pos_diagonal_rate (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ₁)
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
      Real.log (twoPoint μ₀ (diagonalSite n))) atTop (𝓝 L)) :
    μ₁.real (infiniteClusterAt 0) > 0 := by
  have := hμ₁.1
  have hp := (critical_discontinuity_of_pos_diagonal_rate q μ₀ μ₁ hμ₀ hμ₁ L hL hrate).2.1
  exact ENNReal.toReal_pos hp.ne' (measure_ne_top μ₁ _)

/-- Items 1–2 in the exact frozen Theorem 1.2 carrier, critical parameters,
family indexing, existence event, and real-probability convention. The only
additional premise beyond the box limits is the positive frozen diagonal rate. -/
theorem rcm_items_one_two_of_pos_diagonal_rate (q : ℝ) (hq : 4 < q)
    (φ : Fin 2 → Measure (squareLattice.edgeSet → Bool))
    (hφ : ∀ i, IsRCInfiniteVolumeLimit
      (rcCriticalParameter ⟨q, Set.mem_Ici.2 (by linarith)⟩)
      ⟨q, Set.mem_Ioi.2 (by linarith)⟩ i (φ i))
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
      Real.log ((φ 0).real {ω | (rcInfiniteOpenGraph ω).Reachable (0,0) (diagonalSite n)}))
        atTop (𝓝 L)) :
    φ 1 ≠ φ 0 ∧
      (φ 1).real {ω | ∃ x, {y | (rcInfiniteOpenGraph ω).Reachable x y}.Infinite} = 1 := by
  let q₁ : Set.Ici (1 : ℝ) := ⟨q, Set.mem_Ici.2 (by linarith only [hq])⟩
  have h₀ : IsRCInfiniteVolumeLimit (criticalParameters q₁).toP (criticalParameters q₁).toQ 0
      (φ 0) := hφ 0
  have h₁ : IsRCInfiniteVolumeLimit (criticalParameters q₁).toP (criticalParameters q₁).toQ 1
      (φ 1) := hφ 1
  have h := critical_discontinuity_of_pos_diagonal_rate q₁ (φ 0) (φ 1) h₀ h₁ L hL hrate
  refine ⟨h.2.2.2,?_⟩
  change (φ 1).real existsInfiniteCluster = 1
  rw [Measure.real_def,h.2.2.1,ENNReal.toReal_one]

/-- Existential packaging of exactly items 1–2 when the supplied box-limit
family has a positive rate along the frozen diagonal. -/
theorem rcm_items_one_two_exists_of_pos_diagonal_rate (q : ℝ) (hq : 4 < q)
    (φ : Fin 2 → Measure (squareLattice.edgeSet → Bool))
    (hφ : ∀ i, IsRCInfiniteVolumeLimit
      (rcCriticalParameter ⟨q, Set.mem_Ici.2 (by linarith)⟩)
      ⟨q, Set.mem_Ioi.2 (by linarith)⟩ i (φ i))
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
      Real.log ((φ 0).real {ω | (rcInfiniteOpenGraph ω).Reachable (0,0) (diagonalSite n)}))
        atTop (𝓝 L)) :
    ∃ ψ : Fin 2 → Measure (squareLattice.edgeSet → Bool),
      (∀ i, IsRCInfiniteVolumeLimit
        (rcCriticalParameter ⟨q, Set.mem_Ici.2 (by linarith)⟩)
        ⟨q, Set.mem_Ioi.2 (by linarith)⟩ i (ψ i)) ∧
      ψ 1 ≠ ψ 0 ∧
      (ψ 1).real {ω | ∃ x, {y | (rcInfiniteOpenGraph ω).Reachable x y}.Infinite} = 1 :=
  ⟨φ,hφ,rcm_items_one_two_of_pos_diagonal_rate q hq φ hφ L hL hrate⟩

end
end PottsDiscontinuity.Duality
