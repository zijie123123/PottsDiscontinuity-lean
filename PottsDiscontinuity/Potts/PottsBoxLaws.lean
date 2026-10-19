module

public import PottsDiscontinuity.FK.EndpointLimits
public import PottsDiscontinuity.Potts.BoolMeasureBridge
public import PottsDiscontinuity.Potts.LimitCompactness
public import PottsDiscontinuity.Potts.LiteralBoundary

/-! Actual Potts box laws on a common spin configuration space. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

local instance boxLawBoundaryFintype (V : Finset (ℤ × ℤ)) : Fintype (BoundaryVertex V) := Fintype.ofFinite _
local instance finiteSpinMeasurable (q : ℕ) (V : Finset (ℤ × ℤ)) :
    MeasurableSpace (SpinConfiguration q V) := ⊤
local instance finiteSpinDiscrete (q : ℕ) (V : Finset (ℤ × ℤ)) :
    DiscreteMeasurableSpace (SpinConfiguration q V) := ⟨fun _ => trivial⟩

theorem sum_pottsProb (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ)) (β : ℝ) (i : Fin (q + 1)) :
    ∑ σ : SpinConfiguration q V, pottsProb q V β i σ = 1 := by
  rw [← sum_literalJointProbability q hq V β i]
  apply Finset.sum_congr rfl
  intro σ _
  exact (literalJointProbability_spin_marginal q hq V β i σ).symm

theorem pottsProb_nonneg (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ)) (β : ℝ)
    (hβ : 0 < β) (i : Fin (q + 1)) (σ : SpinConfiguration q V) : 0 ≤ pottsProb q V β i σ := by
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  rw [← literalJointProbability_spin_marginal q hq V β i σ]
  exact Finset.sum_nonneg (fun ω _ => constraintJointProbability_nonneg hβ (literalAgreement q V i) σ ω)

/-- The normalized frozen finite Potts probability mass function. -/
def pottsFiniteLaw (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ)) (β : ℝ)
    (hβ : 0 < β) (i : Fin (q + 1)) : PMF (SpinConfiguration q V) :=
  PMF.ofFintype (fun σ => ENNReal.ofReal (pottsProb q V β i σ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun σ _ => pottsProb_nonneg q hq V β hβ i σ),
      sum_pottsProb q hq, ENNReal.ofReal_one])

@[simp] theorem pottsFiniteLaw_apply (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ)) (β : ℝ)
    (hβ : 0 < β) (i : Fin (q + 1)) (σ : SpinConfiguration q V) :
    pottsFiniteLaw q hq V β hβ i σ = ENNReal.ofReal (pottsProb q V β i σ) := rfl

/-- Extend the finite spin state by colour one outside the sampled box.
Every cylinder eventually lies inside the box, so the extension preserves its finite law. -/
def spinExtension (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ))
    (σ : SpinConfiguration q V) : SpinSpace q :=
  fun x => if hx : x ∈ V then σ ⟨x, hx⟩ else ⟨1, le_rfl, by omega⟩

@[simp] theorem spinExtension_at (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ))
    (σ : SpinConfiguration q V) (x : ↥(V : Set (ℤ × ℤ))) :
    spinExtension q hq V σ x.val = σ x := by simp [spinExtension]

def pottsBoxProbabilityMeasure (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (n : ℕ) : ProbabilityMeasure (SpinSpace q) :=
  ⟨((pottsFiniteLaw q hq (box n) β hβ i).map (spinExtension q hq (box n))).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

/-- Exact agreement with the frozen finite cylinder sum once its support is inside. -/
theorem pottsBoxProbabilityMeasure_cylinder (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (n : ℕ) (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q)
    (hA : A ⊆ box n) :
    (pottsBoxProbabilityMeasure q hq β hβ i n).toMeasure.real (spinCylinder q A ξ) =
      ∑ σ : SpinConfiguration q (box n),
        if ∀ x ∈ A, ∃ h : x ∈ box n, σ ⟨x, h⟩ = ξ x then pottsProb q (box n) β i σ else 0 := by
  change (((pottsFiniteLaw q hq (box n) β hβ i).map (spinExtension q hq (box n))).toMeasure _).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top (spinCylinder_isClopen q A ξ).isOpen.measurableSet]
  rw [← Measure.real, finite_pmf_measureReal_sum]
  apply Finset.sum_congr
  · ext σ; simp
  · intro σ _
    rw [pottsFiniteLaw_apply, ENNReal.toReal_ofReal (pottsProb_nonneg q hq (box n) β hβ i σ)]
    have he : spinExtension q hq (box n) σ ∈ spinCylinder q A ξ ↔
        ∀ x ∈ A, ∃ h : x ∈ box n, σ ⟨x, h⟩ = ξ x := by
      constructor
      · intro h x hx
        exact ⟨hA hx, by simpa only [← spinExtension_at q hq (box n) σ ⟨x, hA hx⟩] using h x hx⟩
      · intro h x hx
        obtain ⟨hx', hs⟩ := h x hx
        simpa only [spinExtension_at q hq (box n) σ ⟨x, hx'⟩] using hs
    by_cases h : spinExtension q hq (box n) σ ∈ spinCylinder q A ξ
    · simp only [Set.mem_preimage, h, ite_true]
      exact (ite_eq_left (he.mp h)).symm
    · simp only [Set.mem_preimage, h, mt he.mpr h, ite_false]

/-- Weak convergence of the actual Potts box laws implies exactly the frozen
infinite-volume predicate, for the full sequence of boxes. -/
theorem isPottsInfiniteVolumeLimit_of_box_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : Tendsto (pottsBoxProbabilityMeasure q hq β hβ i) atTop (𝓝 μ)) :
    IsPottsInfiniteVolumeLimit q β i μ.toMeasure := by
  refine ⟨μ.prop, ?_⟩
  intro A ξ
  have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ (spinCylinder_isClopen q A ξ)
  have hr : Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ i n).toMeasure.real (spinCylinder q A ξ))
      atTop (𝓝 (μ.toMeasure.real (spinCylinder q A ξ))) := by
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp ht
  apply hr.congr'
  have hs : ∀ᶠ n : ℕ in atTop, A ⊆ box n :=
    (eventually_all_finset A).mpr (fun x _ => FK.eventually_mem_box x)
  filter_upwards [hs] with n hn
  exact pottsBoxProbabilityMeasure_cylinder q hq β hβ i n A ξ hn

end
end PottsDiscontinuity.Potts
