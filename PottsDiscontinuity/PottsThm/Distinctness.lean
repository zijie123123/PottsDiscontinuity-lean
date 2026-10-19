module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.PottsThm.DiscontinuityConsequences
public import PottsDiscontinuity.PottsThm.OneSite

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.Duality
open PottsDiscontinuity.RCInfinite

theorem critical_potts_limits_pairwise_distinct (q : ℕ) (hq : 4 < q)
    (μ : Fin (q + 1) → ProbabilityMeasure (SpinSpace q))
    (φ₀ : ProbabilityMeasure LatticeConfiguration)
    (φp : Fin q → ProbabilityMeasure LatticeConfiguration)
    (hRC₀ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 0 φ₀.toMeasure)
    (hμ₀ : IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) 0 (μ 0).toMeasure)
    (hRCp : ∀ i : Fin q, IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 1 (φp i).toMeasure)
    (hμp : ∀ i : Fin q, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i.succ
      (μ i.succ).toMeasure)
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
      (φ₀.toMeasure.real
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
      atTop (𝓝 L)) :
    ∀ i j : Fin (q + 1), i ≠ j → (μ i).toMeasure ≠ (μ j).toMeasure := by
  have hq2 : 2 ≤ q := by omega
  have hβ : 0 < pottsCriticalBeta q := pottsCriticalBeta_pos q hq
  have hθ : (criticalFKParameters q hq).toP =
      (FK.criticalParameters ⟨(q : ℝ), by
        change (1 : ℝ) ≤ (q : ℝ)
        exact_mod_cast (show 1 ≤ q by omega)⟩).toP ∧
      (criticalFKParameters q hq).toQ =
      (FK.criticalParameters ⟨(q : ℝ), by
        change (1 : ℝ) ≤ (q : ℝ)
        exact_mod_cast (show 1 ≤ q by omega)⟩).toQ := fkCritical_toP_toQ q hq
  have hφ₀weak : Tendsto
      (fun n => boxProbabilityMeasure (fkParameters q hq2 (pottsCriticalBeta q) hβ) (0, 0) n)
      atTop (𝓝 φ₀) := by
    have ht := boxMeasure_tendsto (criticalFKParameters q hq) 0 φ₀.toMeasure hRC₀
    have htarget :
        (⟨φ₀.toMeasure, hRC₀.1⟩ : ProbabilityMeasure LatticeConfiguration) = φ₀ := by
      ext
      rfl
    rw [htarget] at ht
    simpa [boxMeasure_free, criticalFKParameters, fkParameters] using ht
  have hφpweak (k : Fin q) : Tendsto
      (fun n => wiredBoxProbabilityMeasure
        (fkParameters q hq2 (pottsCriticalBeta q) hβ) (0, 0) n)
      atTop (𝓝 (φp k)) := by
    have ht := boxMeasure_tendsto (criticalFKParameters q hq) 1 (φp k).toMeasure (hRCp k)
    have htarget :
        (⟨(φp k).toMeasure, (hRCp k).1⟩ : ProbabilityMeasure LatticeConfiguration) = φp k := by
      ext
      rfl
    rw [htarget] at ht
    simpa [boxMeasure_wired, criticalFKParameters, fkParameters] using ht
  have hpin (k : Fin q) :
      1 / (q : ℝ) < (μ k.succ).toMeasure.real
        {σ | (σ (0, 0) : ℕ) = (k.succ : ℕ)} := by
    have hdisc := rc_discontinuity_of_positive_rate q hq φ₀ (φp k)
      hRC₀ (hRCp k) L hL hrate
    have hpos : 0 < (φp k).toMeasure.real
        {ω | clusterIsInfinite (rcInfiniteOpenGraph ω) (0, 0)} :=
      ENNReal.toReal_pos hdisc.2.ne' (measure_ne_top _ _)
    exact wired_pinned_one_site_probability_gt q hq2 (pottsCriticalBeta q) hβ
      k.succ (by simp only [Fin.val_succ]; omega) (φp k) (hφpweak k)
      (μ k.succ) (hμp k) hpos
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ k =>
      intro heq
      have hfree := free_one_site_probability q hq2 (pottsCriticalBeta q) hβ
        φ₀ hφ₀weak (μ 0) hμ₀ (0, 0)
        (boundaryColor q k.succ (by simp only [Fin.val_succ]; omega))
      have hfree' : (μ 0).toMeasure.real
          {σ | (σ (0, 0) : ℕ) = (k.succ : ℕ)} = 1 / (q : ℝ) := by
        simpa [boundaryColor, Subtype.ext_iff] using hfree
      have hprob := congrArg (fun ν : Measure (SpinSpace q) => ν.real
        {σ | (σ (0, 0) : ℕ) = (k.succ : ℕ)}) heq
      have hpin' := hpin k
      rw [← hprob] at hpin'
      linarith [hfree']
  | succ k =>
    cases j using Fin.cases with
    | zero =>
      intro heq
      have hfree := free_one_site_probability q hq2 (pottsCriticalBeta q) hβ
        φ₀ hφ₀weak (μ 0) hμ₀ (0, 0)
        (boundaryColor q k.succ (by simp only [Fin.val_succ]; omega))
      have hfree' : (μ 0).toMeasure.real
          {σ | (σ (0, 0) : ℕ) = (k.succ : ℕ)} = 1 / (q : ℝ) := by
        simpa [boundaryColor, Subtype.ext_iff] using hfree
      have hprob := congrArg (fun ν : Measure (SpinSpace q) => ν.real
        {σ | (σ (0, 0) : ℕ) = (k.succ : ℕ)}) heq.symm
      have hpin' := hpin k
      rw [← hprob] at hpin'
      linarith [hfree']
    | succ l =>
      intro heq
      have hcolor : boundaryColor q l.succ
          (by simp only [Fin.val_succ]; omega) ≠ boundaryColor q k.succ
          (by simp only [Fin.val_succ]; omega) := by
        intro h
        apply hij
        exact Fin.ext (by
          have hv := congrArg Subtype.val h
          simpa [boundaryColor, Fin.val_succ] using hv.symm)
      have hoff := wired_off_color_probability_le_uniform q hq2
        (pottsCriticalBeta q) hβ l.succ (by simp only [Fin.val_succ]; omega)
        (φp l) (hφpweak l) (μ l.succ) (hμp l) (0, 0)
        (boundaryColor q k.succ (by simp only [Fin.val_succ]; omega)) hcolor.symm
      have hoff' : (μ l.succ).toMeasure.real
          {σ | (σ (0, 0) : ℕ) = (k.succ : ℕ)} ≤ 1 / (q : ℝ) := by
        simpa [boundaryColor, Subtype.ext_iff] using hoff
      have hprob := congrArg (fun ν : Measure (SpinSpace q) => ν.real
        {σ | (σ (0, 0) : ℕ) = (k.succ : ℕ)}) heq
      have hpin' := hpin k
      rw [hprob] at hpin'
      linarith [hoff']

end PottsDiscontinuity.PottsThm
