module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.DualCylinderLaw
public import PottsDiscontinuity.Duality.WiredDomainLimit
public import PottsDiscontinuity.FK.FreeBoxLimitV1

/-! Infinite-volume free/wired duality for the actual frozen box limits. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK FK.Medial MeasureTheory Filter Topology
noncomputable section

/-- Lower left corner of the origin-centered primal box. -/
def originBoxAnchor (n : ℕ) : LatticeVertex := (-(n : ℤ), -(n : ℤ))

lemma originBoxRectangle_eq (n : ℕ) :
    latticeRectangle (originBoxAnchor n) (2 * n) (2 * n) = box n := by
  simpa only [originBoxAnchor, zero_sub, Prod.fst_zero, Prod.snd_zero] using
    (latticeRectangle_box_eq (0, 0) n).trans (latticeBox_origin_eq_box n)

/-- Every fixed original lattice edge eventually belongs to the genuine dual
edge carrier, rather than merely to the larger ambient induced graph. -/
lemma eventually_edge_in_trueDual (e : squareLattice.edgeSet) :
    ∀ᶠ n : ℕ in atTop, e ∈ Set.range
      (rectangleDualEdgeToSquareEdge (originBoxAnchor n) (2 * n) (2 * n)) := by
  filter_upwards [eventually_edge_lift_box (wholePlaneDualCrossingEdgeEquiv e)] with n hn
  rw [← originBoxRectangle_eq n] at hn
  obtain ⟨f, hf⟩ := hn
  let d := rectanglePrimalDualEdgeEquiv (originBoxAnchor n) (2 * n) (2 * n) f
  refine ⟨rectangleDualGraphEdgeEquiv _ _ _ d, ?_⟩
  apply wholePlaneDualCrossingEdgeEquiv.injective
  have he : wholePlaneDualCrossingEdgeEquiv
      (rectangleDualEdgeToSquareEdge (originBoxAnchor n) (2 * n) (2 * n)
        (rectangleDualGraphEdgeEquiv _ _ _ d)) =
      rectanglePrimalEdgeToSquareEdge (originBoxAnchor n) (2 * n) (2 * n) f := by
    rw [rectangleDualEdgeToSquareEdge_carrier]
    change wholePlaneBondEdgeEquiv (primalBondOfDual
      (wholePlaneBondEdgeEquiv.symm (wholePlaneBondEdgeEquiv d.crossingBond))) = _
    rw [Equiv.symm_apply_apply]
    exact rectangleDualEdge_crossing_originalEdge _ _ _ d
  rw [he]
  exact Subtype.ext hf

lemma dualExpanded_origin_inner (n : ℕ) :
    latticeBox (0, 0) n ⊆ rectangleDualExpanded (originBoxAnchor n) (2 * n) (2 * n) := by
  intro x hx
  simp only [mem_latticeBox, rectangleDualExpanded, mem_latticeRectangle,
    originBoxAnchor, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at hx ⊢
  omega

lemma dualExpanded_origin_outer (n : ℕ) :
    rectangleDualExpanded (originBoxAnchor n) (2 * n) (2 * n) ⊆
      latticeBox (0, 0) (n + 1) := by
  intro x hx
  simp only [mem_latticeBox, rectangleDualExpanded, mem_latticeRectangle,
    originBoxAnchor, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at hx ⊢
  omega

/-- The actual whole-plane dual transform pushes the frozen free measure at p
to the frozen wired measure at p*, for arbitrary interior p and q ≥ 1. -/
theorem free_map_dual_eq_wired (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁) :
    μ₀.map wholePlaneDualConfigurationHomeomorph = μ₁ := by
  let ν₀ : ProbabilityMeasure LatticeConfiguration := ⟨μ₀, hμ₀.1⟩
  let ν₁ : ProbabilityMeasure LatticeConfiguration := ⟨μ₁, hμ₁.1⟩
  obtain ⟨ν, hν, _⟩ := freeBoxLimit_existsUnique θ
  have hνorigin := hν (fun _ => (0, 0)) (fun n => n)
    origin_latticeBox_nested origin_latticeBox_exhaustive
  have heq : ν₀ = ν := ProbabilityMeasure.toMeasure_injective
    (rc_limit_unique θ.toP θ.toQ 0 μ₀ ν.toMeasure hμ₀
      (isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν hνorigin))
  have hfree : Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 ν₀) := by
    rw [heq]; exact hνorigin
  have hdual := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hfree
    wholePlaneDualConfigurationHomeomorph.continuous
  have hwired := wiredDomainProbabilityMeasure_tendsto_of_box_sandwich
    (dualParameters θ) μ₁ hμ₁
    (fun n => rectangleDualExpanded (originBoxAnchor n) (2 * n) (2 * n))
    dualExpanded_origin_inner dualExpanded_origin_outer
  have hprob : ν₀.map wholePlaneDualConfigurationHomeomorph = ν₁ := by
    apply LatticeConfiguration.probabilityMeasure_eq_of_allOpen
    intro F
    have h₀ := LatticeConfiguration.tendsto_allOpen_of_weak hdual F
    have h₁ := LatticeConfiguration.tendsto_allOpen_of_weak hwired F
    apply tendsto_nhds_unique h₀
    apply h₁.congr'
    have hF := (eventually_all_finset F).2 fun e _ => eventually_edge_in_trueDual e
    filter_upwards [hF] with n hn
    apply ENNReal.coe_injective
    simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    have h := freeRectangle_dual_allOpen θ (originBoxAnchor n) (2 * n) (2 * n) F hn
    have hb : freeRectangleProbabilityMeasure θ (originBoxAnchor n) (2 * n) (2 * n) =
        boxProbabilityMeasure θ (0, 0) n := by
      simpa only [originBoxAnchor, Prod.fst_zero, Prod.snd_zero, zero_sub] using
        freeRectangleProbabilityMeasure_box θ (0, 0) n
    rw [hb] at h
    exact h.symm
  exact congrArg ProbabilityMeasure.toMeasure hprob

/-- At the exact frozen critical parameter, the free and wired measures are
exchanged by the actual planar dual transform with unchanged p and q. -/
theorem free_map_dual_eq_wired_at_critical (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ₁) :
    μ₀.map wholePlaneDualConfigurationHomeomorph = μ₁ := by
  apply free_map_dual_eq_wired (criticalParameters q) μ₀ μ₁ hμ₀
  simpa only [dualParameters_criticalParameters] using hμ₁

end
end PottsDiscontinuity.Duality
