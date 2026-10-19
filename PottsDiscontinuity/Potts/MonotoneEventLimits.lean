module

public import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Diagonal limits of increasing and decreasing connection approximations. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory Filter Topology
noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Increasing finite-path events may grow with the volume if each finite law
is dominated by the limiting law on that event. -/
theorem increasing_event_diagonal_tendsto (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (E : ℕ → Set X) (hE : Monotone E)
    (hlocal : ∀ m, Tendsto (fun n => (μs n).toMeasure.real (E m)) atTop (𝓝 (μ.toMeasure.real (E m))))
    (hdom : ∀ n, (μs n).toMeasure.real (E n) ≤ μ.toMeasure.real (E n)) :
    Tendsto (fun n => (μs n).toMeasure.real (E n)) atTop (𝓝 (μ.toMeasure.real (⋃ n, E n))) := by
  have hcont : Tendsto (fun n => μ.toMeasure.real (E n)) atTop (𝓝 (μ.toMeasure.real (⋃ n, E n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_iUnion_atTop hE)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨m, hm⟩ := (hcont.eventually (lt_mem_nhds ha)).exists
    filter_upwards [(hlocal m).eventually (lt_mem_nhds hm), eventually_ge_atTop m] with n hn hmn
    exact hn.trans_le (measureReal_mono (hE hmn))
  · intro b hb
    filter_upwards [hcont.eventually (gt_mem_nhds hb)] with n hn
    exact (hdom n).trans_lt hn

/-- Decreasing wired events may grow with the volume if every finite law
 dominates the limiting law on that event. -/
theorem decreasing_event_diagonal_tendsto (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (E : ℕ → Set X) (hE : Antitone E) (hmeas : ∀ n, MeasurableSet (E n))
    (hlocal : ∀ m, Tendsto (fun n => (μs n).toMeasure.real (E m)) atTop (𝓝 (μ.toMeasure.real (E m))))
    (hdom : ∀ n, μ.toMeasure.real (E n) ≤ (μs n).toMeasure.real (E n)) :
    Tendsto (fun n => (μs n).toMeasure.real (E n)) atTop (𝓝 (μ.toMeasure.real (⋂ n, E n))) := by
  have hcont : Tendsto (fun n => μ.toMeasure.real (E n)) atTop (𝓝 (μ.toMeasure.real (⋂ n, E n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_measure_iInter_atTop (fun n => (hmeas n).nullMeasurableSet) hE ⟨0, measure_ne_top _ _⟩)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hcont.eventually (lt_mem_nhds ha)] with n hn
    exact hn.trans_le (hdom n)
  · intro b hb
    obtain ⟨m, hm⟩ := (hcont.eventually (gt_mem_nhds hb)).exists
    filter_upwards [(hlocal m).eventually (gt_mem_nhds hm), eventually_ge_atTop m] with n hn hmn
    exact (measureReal_mono (hE hmn)).trans_lt hn

end
end PottsDiscontinuity.Potts
