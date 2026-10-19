module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.IsPottsInfiniteVolumeLimit
public import PottsDiscontinuity.Frozen.Defs.IsRCInfiniteVolumeLimit

/-!
# Uniqueness of cylinder limits

A finite measure on a product of countable discrete spaces is determined by its values on the
cylinder atoms `{σ | ∀ x ∈ A, σ x = ξ x}`. Consequently the infinite-volume measures characterized
by `IsPottsInfiniteVolumeLimit` and `IsRCInfiniteVolumeLimit` are unique (author ruling R3).

Provenance: proofs first written by an independent statement reviewer in a transient check file
(2026-10-18) and moved here unchanged apart from layout.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity

theorem ext_of_cylinders {ι S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    (μ ν : Measure (ι → S)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ξ₀ : ι → S)
    (h : ∀ (A : Finset ι) (ξ : ι → S),
      μ {σ | ∀ x ∈ A, σ x = ξ x} = ν {σ | ∀ x ∈ A, σ x = ξ x}) : μ = ν := by
  classical
  let C : Set (Set (ι → S)) := {s | ∃ (A : Finset ι) (ξ : ι → S), s = {σ | ∀ x ∈ A, σ x = ξ x}}
  have hmeas : ∀ (A : Finset ι) (ξ : ι → S), MeasurableSet {σ : ι → S | ∀ x ∈ A, σ x = ξ x} := by
    intro A ξ
    have : {σ : ι → S | ∀ x ∈ A, σ x = ξ x} = ⋂ x ∈ A, {σ | σ x = ξ x} := by
      ext σ; simp
    rw [this]
    refine MeasurableSet.biInter A.countable_toSet fun x _ => ?_
    have hx : MeasurableSet ((fun f : ι → S => f x) ⁻¹' {ξ x}) :=
      (measurable_pi_apply x) (measurableSet_singleton (ξ x))
    exact hx
  have hgen : (inferInstance : MeasurableSpace (ι → S)) = MeasurableSpace.generateFrom C := by
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
    · refine iSup_le fun i => ?_
      refine MeasurableSpace.comap_le_iff_le_map.2 ?_
      intro T hT
      have : (fun σ : ι → S => σ i) ⁻¹' T = ⋃ t : T, {σ : ι → S | σ i = t} := by
        ext σ; simp
      show MeasurableSet[MeasurableSpace.generateFrom C] ((fun σ : ι → S => σ i) ⁻¹' T)
      rw [this]
      refine MeasurableSet.iUnion fun t => ?_
      apply MeasurableSpace.measurableSet_generateFrom
      refine ⟨{i}, fun _ => t, ?_⟩
      ext σ; simp
    · rintro s ⟨A, ξ, rfl⟩
      exact hmeas A ξ
  have hpi : IsPiSystem C := by
    rintro s ⟨A₁, ξ₁, rfl⟩ t ⟨A₂, ξ₂, rfl⟩ ⟨σ₀, h₁, h₂⟩
    refine ⟨A₁ ∪ A₂, fun x => if x ∈ A₁ then ξ₁ x else ξ₂ x, ?_⟩
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_union]
    constructor
    · rintro ⟨hs, ht⟩ x (hx | hx)
      · simp [hx, hs x hx]
      · by_cases hx1 : x ∈ A₁
        · simp [hx1, hs x hx1]
        · simp [hx1, ht x hx]
    · intro hu
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · simpa [hx] using hu x (Or.inl hx)
      · by_cases hx1 : x ∈ A₁
        · have := hu x (Or.inr hx)
          simp only [hx1, ite_true] at this
          rw [this]
          have h1 := h₁ x hx1
          have h2 := h₂ x hx
          rw [← h2, h1]
        · simpa [hx1] using hu x (Or.inr hx)
  refine MeasureTheory.ext_of_generate_finite C hgen hpi ?_ ?_
  · rintro s ⟨A, ξ, rfl⟩
    exact h A ξ
  · simpa using h ∅ ξ₀

theorem potts_limit_unique (q : ℕ) (β : ℝ) (i : Fin (q + 1)) (hq : 0 < q)
    (μ ν : Measure (ℤ × ℤ → Set.Icc 1 q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ) (hν : IsPottsInfiniteVolumeLimit q β i ν) : μ = ν := by
  obtain ⟨hμp, hμl⟩ := hμ
  obtain ⟨hνp, hνl⟩ := hν
  have := hμp
  have := hνp
  refine ext_of_cylinders μ ν (fun _ => ⟨1, by simp; omega⟩) ?_
  intro A ξ
  have := tendsto_nhds_unique (hμl A ξ) (hνl A ξ)
  have h2 : (μ {σ | ∀ x ∈ A, σ x = ξ x}).toReal = (ν {σ | ∀ x ∈ A, σ x = ξ x}).toReal := this
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h2

theorem rc_limit_unique (p : Set.Icc (0:ℝ) 1) (q : Set.Ioi (0:ℝ)) (i : Fin 2)
    (μ ν : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q i μ) (hν : IsRCInfiniteVolumeLimit p q i ν) : μ = ν := by
  obtain ⟨hμp, hμl⟩ := hμ
  obtain ⟨hνp, hνl⟩ := hν
  have := hμp
  have := hνp
  refine ext_of_cylinders μ ν (fun _ => true) ?_
  intro A ξ
  have := tendsto_nhds_unique (hμl A ξ) (hνl A ξ)
  have h2 : (μ {ω | ∀ e ∈ A, ω e = ξ e}).toReal = (ν {ω | ∀ e ∈ A, ω e = ξ e}).toReal := this
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h2


end PottsDiscontinuity
