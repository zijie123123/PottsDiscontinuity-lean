module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import PottsDiscontinuity.Infra.CylinderUniqueness

/-!
# Compactness from convergence of spin cylinder probabilities

On the compact spin configuration space, convergence of every finite cylinder
probability determines the weak limit of a sequence of probability measures.
This is a reusable compactness bridge for the Potts box laws; it does not assert
the convergence of those laws' cylinder probabilities.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.Potts

noncomputable section

abbrev SpinSpace (q : ℕ) := ℤ × ℤ → Set.Icc 1 q

/-- The spin configurations agreeing with `ξ` on the finite set `A`. -/
def spinCylinder (q : ℕ) (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q) : Set (SpinSpace q) :=
  {σ | ∀ x ∈ A, σ x = ξ x}

/-- A finite spin cylinder is clopen in the product topology. -/
theorem spinCylinder_isClopen (q : ℕ) (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q) :
    IsClopen (spinCylinder q A ξ) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simpa [spinCylinder] using isClopen_univ (X := SpinSpace q)
  | @insert x A hx ih =>
      have hset : spinCylinder q (insert x A) ξ =
          {σ | σ x = ξ x} ∩ spinCylinder q A ξ := by
        ext σ
        simp [spinCylinder]
      rw [hset]
      exact ((isClopen_discrete ({ξ x} : Set (Set.Icc 1 q))).preimage
        (continuous_apply x)).inter ih

abbrev SpinCylinderIndex (q : ℕ) := Finset (ℤ × ℤ) × SpinSpace q

/-- The finite-cylinder probability coordinates of a spin-space probability measure. -/
def spinCylinderCoordinates (q : ℕ) (μ : ProbabilityMeasure (SpinSpace q)) :
    SpinCylinderIndex q → NNReal :=
  fun i => μ (spinCylinder q i.1 i.2)

theorem continuous_spinCylinderCoordinates (q : ℕ) :
    Continuous (spinCylinderCoordinates q) := by
  refine continuous_pi fun i => ?_
  rw [continuous_iff_continuousAt]
  intro μ
  exact ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto tendsto_id
    (spinCylinder_isClopen q i.1 i.2)

theorem spinCylinderCoordinates_injective (q : ℕ) (hq : 2 ≤ q) :
    Function.Injective (spinCylinderCoordinates q) := by
  classical
  intro μ ν h
  apply ProbabilityMeasure.toMeasure_injective
  apply PottsDiscontinuity.ext_of_cylinders (μ : Measure (SpinSpace q))
    (ν : Measure (SpinSpace q)) (fun _ => ⟨1, by omega, by omega⟩)
  intro A ξ
  have hc : μ (spinCylinder q A ξ) = ν (spinCylinder q A ξ) := congrFun h (A, ξ)
  simpa only [spinCylinder, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    congrArg (fun x : NNReal => (x : ENNReal)) hc

/-- If every finite spin cylinder has a limiting probability, the whole sequence
converges weakly to the unique probability measure with those cylinder values.

This theorem supplies only the compactness and uniqueness step. Its cylinder
convergence hypothesis must be established separately for the Potts box laws.
-/
theorem probabilityMeasures_tendsto_of_spinCylinder_tendsto (q : ℕ) (hq : 2 ≤ q)
    (μs : ℕ → ProbabilityMeasure (SpinSpace q))
    (cyl : SpinCylinderIndex q → NNReal)
    (hcyl : ∀ A ξ,
      Tendsto (fun n => μs n (spinCylinder q A ξ)) atTop (𝓝 (cyl (A, ξ)))) :
    ∃! μ : ProbabilityMeasure (SpinSpace q),
      Tendsto μs atTop (𝓝 μ) ∧
        ∀ A ξ, μ (spinCylinder q A ξ) = cyl (A, ξ) := by
  classical
  obtain ⟨μ, φ, hφ, hsub⟩ := CompactSpace.tendsto_subseq μs
  have hμcyl (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q) :
      μ (spinCylinder q A ξ) = cyl (A, ξ) := by
    have hweak := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hsub
      (spinCylinder_isClopen q A ξ)
    have hgiven := (hcyl A ξ).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique hweak hgiven
  let κ : ProbabilityMeasure (SpinSpace q) → SpinCylinderIndex q → NNReal :=
    spinCylinderCoordinates q
  have hκcont : Continuous κ := continuous_spinCylinderCoordinates q
  have hκinj : Function.Injective κ := spinCylinderCoordinates_injective q hq
  have hκembed : IsClosedEmbedding κ := hκcont.isClosedEmbedding hκinj
  have hcoords : Tendsto (fun n => κ (μs n)) atTop (𝓝 (κ μ)) := by
    apply tendsto_pi_nhds.2
    intro i
    rcases i with ⟨A, ξ⟩
    change Tendsto (fun n => μs n (spinCylinder q A ξ)) atTop
      (𝓝 (μ (spinCylinder q A ξ)))
    rw [hμcyl A ξ]
    exact hcyl A ξ
  have hweak : Tendsto μs atTop (𝓝 μ) := hκembed.tendsto_nhds_iff.mpr hcoords
  refine ⟨μ, ⟨hweak, hμcyl⟩, ?_⟩
  intro ν hν
  exact tendsto_nhds_unique hν.1 hweak

end

end PottsDiscontinuity.Potts
