module

public import PottsDiscontinuity.FK.LimitTranslation

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.RCInfinite

open PottsDiscontinuity.FK

noncomputable section

/-- Every frozen free limit is also the weak limit along each nested exhaustive
sequence of translated square boxes. -/
theorem free_box_exhaustion
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (c : ℕ → LatticeVertex) (r : ℕ → ℕ)
    (hnest : ∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1)))
    (hexhaust : ∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) :
    Tendsto (fun n => boxProbabilityMeasure θ (c n) (r n)) atTop
      (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) := by
  change IsProbabilityMeasure μ ∧ _ at hμ
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  obtain ⟨ν₀, hν₀, _⟩ := freeBoxLimit_existsUnique (q := θ)
  have hν₀origin : Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n)
      atTop (𝓝 ν₀) :=
    hν₀ (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested
      origin_latticeBox_exhaustive
  have hRCν₀ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 ν₀.toMeasure :=
    isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν₀ hν₀origin
  have hRCν : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 ν.toMeasure := by
    exact hμ
  have hmeasure : ν.toMeasure = ν₀.toMeasure :=
    PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 0
      ν.toMeasure ν₀.toMeasure hRCν hRCν₀
  have hprob : ν = ν₀ := ProbabilityMeasure.toMeasure_injective hmeasure
  change Tendsto (fun n => boxProbabilityMeasure θ (c n) (r n)) atTop (𝓝 ν)
  rw [hprob]
  exact hν₀ c r hnest hexhaust

/-- Every frozen wired limit is also the weak limit along each nested exhaustive
sequence of translated square boxes. -/
theorem wired_box_exhaustion
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (c : ℕ → LatticeVertex) (r : ℕ → ℕ)
    (hnest : ∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1)))
    (hexhaust : ∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) :
    Tendsto (fun n => wiredBoxProbabilityMeasure θ (c n) (r n)) atTop
      (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) := by
  change IsProbabilityMeasure μ ∧ _ at hμ
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  obtain ⟨ν₀, hν₀, _⟩ := wiredBoxLimit_existsUnique θ
  have hν₀origin : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n)
      atTop (𝓝 ν₀) :=
    hν₀ (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested
      origin_latticeBox_exhaustive
  have hRCν₀ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 ν₀.toMeasure :=
    isRCInfiniteVolumeLimit_of_wiredBox_tendsto θ ν₀ hν₀origin
  have hRCν : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 ν.toMeasure := by
    exact hμ
  have hmeasure : ν.toMeasure = ν₀.toMeasure :=
    PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 1
      ν.toMeasure ν₀.toMeasure hRCν hRCν₀
  have hprob : ν = ν₀ := ProbabilityMeasure.toMeasure_injective hmeasure
  change Tendsto (fun n => wiredBoxProbabilityMeasure θ (c n) (r n)) atTop (𝓝 ν)
  rw [hprob]
  exact hν₀ c r hnest hexhaust

/-- Translation invariance for every frozen limit, re-exported in the
infinite-volume random-cluster namespace. -/
theorem translation_invariant
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit p q i μ)
    (a : LatticeVertex) :
    μ.map (latticeConfigurationTranslate a) = μ :=
  PottsDiscontinuity.FK.isRCInfiniteVolumeLimit_translation_invariant
    p q hq i μ hμ a

end
end PottsDiscontinuity.RCInfinite
