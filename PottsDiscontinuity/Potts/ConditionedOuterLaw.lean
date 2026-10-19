module

public import PottsDiscontinuity.Potts.GhostBoxLimit

/-! The full conditioned outer law, including its boundary connection data. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace

 theorem cornerClosureEvent_support (θ : FK.Parameters) (n : ℕ) :
    ∃ C ∈ cornerClosureEvent n,
      C ∈ (FK.law (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))) θ (outerBoxWiring n)).support := by
  refine ⟨∅, Finset.disjoint_empty_right _, ?_⟩
  exact (FK.law_pos _ θ (outerBoxWiring n) ∅).ne'

/-- The actual outer FK law conditioned on the four closed corner bonds. -/
def conditionedOuterLaw (θ : FK.Parameters) (n : ℕ) :
    PMF (FK.Configuration (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ)))) :=
  (FK.law _ θ (outerBoxWiring n)).filter (cornerClosureEvent n) (cornerClosureEvent_support θ n)

def conditionedOuterBoxProbabilityMeasure (θ : FK.Parameters) (n : ℕ) :
    ProbabilityMeasure FK.LatticeConfiguration :=
  ⟨((conditionedOuterLaw θ n).map (openExtension (box (n + 1)))).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

/-- Exact conditional probability on the common whole-lattice carrier. -/
theorem conditionedOuterBox_allOpen (θ : FK.Parameters) (n : ℕ)
    (F : Finset squareLattice.edgeSet) :
    (conditionedOuterBoxProbabilityMeasure θ n).toMeasure.real (FK.LatticeConfiguration.allOpen F) =
      (FK.measure _ θ (outerBoxWiring n)
        (openBoxCylinderEvent (n + 1) F ∩ cornerClosureEvent n)).toReal /
      (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal := by
  change (((conditionedOuterLaw θ n).map (openExtension (box (n + 1)))).toMeasure _).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (FK.LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  change ((FK.law _ θ (outerBoxWiring n)).filter _ _).toMeasure.real _ = _
  rw [finite_filter_measureReal]
  congr 3
  ext C
  exact openExtension_mem_allOpen (n + 1) C F

/-- The conditioned full outer laws have the same wired weak limit. -/
theorem conditionedOuterBox_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 μ)) :
    Tendsto (conditionedOuterBoxProbabilityMeasure (fkParameters q hq β hβ)) atTop (𝓝 μ) := by
  have hinj : Function.Injective FK.cylinderProbabilityCoordinates := by
    intro μ ν h
    exact FK.LatticeConfiguration.probabilityMeasure_eq_of_allOpen (fun F => congrFun h F)
  have hemb := FK.continuous_cylinderProbabilityCoordinates.isClosedEmbedding hinj
  apply hemb.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro F
  apply NNReal.tendsto_coe.mp
  have hghost := ghostBox_allOpen_tendsto q hq β hβ μ hμ F
  have heq : ∀ᶠ n : ℕ in atTop,
      (conditionedOuterBoxProbabilityMeasure (fkParameters q hq β hβ) n).toMeasure.real
        (FK.LatticeConfiguration.allOpen F) =
      (ghostBoxProbabilityMeasure q hq β hβ n).toMeasure.real (FK.LatticeConfiguration.allOpen F) := by
    have hs : ∀ᶠ n : ℕ in atTop, ∀ e ∈ F, ∃ f, FK.frozenEdgeEmbedding (box n) f = e := by
      apply (eventually_all_finset F).mpr
      intro e _
      exact (FK.eventually_edge_lift_box e).mono (fun n hn => by
        obtain ⟨f, hf⟩ := hn
        exact ⟨f, Subtype.ext hf⟩)
    filter_upwards [hs, eventually_gt_atTop 0] with n hn hn0
    rw [conditionedOuterBox_allOpen, ghostBoxProbabilityMeasure_allOpen_eq_conditional q hq β hβ n hn0 F hn]
  have ht := hghost.congr' (heq.mono (fun _ h => h.symm))
  simpa only [FK.cylinderProbabilityCoordinates, Function.comp_def,
    ProbabilityMeasure.measureReal_eq_coe_coeFn] using ht

/-- The conditional density is bounded by the reciprocal of the four-edge
finite-energy constant, uniformly in the volume. -/
theorem conditionedOuterLaw_density (θ : FK.Parameters) (n : ℕ) (hn : 0 < n)
    (S : Set (FK.Configuration (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))))) :
    (1 - FK.edgeParameter θ) ^ 4 * (conditionedOuterLaw θ n).toMeasure.real S ≤
      (FK.measure _ θ (outerBoxWiring n) S).toReal := by
  change (1 - FK.edgeParameter θ) ^ 4 *
    ((FK.law _ θ (outerBoxWiring n)).filter _ _).toMeasure.real S ≤ _
  rw [finite_filter_measureReal]
  have hb := cornerClosureEvent_probability_lower_bound θ n hn
  have hbpos : 0 < (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal :=
    (pow_pos (FK.one_sub_edgeParameter_pos θ) 4).trans_le hb
  have ha : 0 ≤ (FK.measure _ θ (outerBoxWiring n) (S ∩ cornerClosureEvent n)).toReal /
      (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal :=
    div_nonneg ENNReal.toReal_nonneg hbpos.le
  calc
    _ ≤ (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal *
        ((FK.measure _ θ (outerBoxWiring n) (S ∩ cornerClosureEvent n)).toReal /
          (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal) :=
      mul_le_mul_of_nonneg_right hb ha
    _ = (FK.measure _ θ (outerBoxWiring n) (S ∩ cornerClosureEvent n)).toReal := by
      rw [mul_comm, div_mul_cancel₀ _ hbpos.ne']
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_left)

theorem conditionedOuterBox_density (θ : FK.Parameters) (n : ℕ) (hn : 0 < n)
    (S : Set FK.LatticeConfiguration) (hS : MeasurableSet S) :
    (1 - FK.edgeParameter θ) ^ 4 * (conditionedOuterBoxProbabilityMeasure θ n).toMeasure.real S ≤
      (openBoxProbabilityMeasure θ (n + 1)).toMeasure.real S := by
  change (1 - FK.edgeParameter θ) ^ 4 *
    (((conditionedOuterLaw θ n).map (openExtension (box (n + 1)))).toMeasure S).toReal ≤
      (((FK.law _ θ (outerBoxWiring n)).map (openExtension (box (n + 1)))).toMeasure S).toReal
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hS,
    PMF.toMeasure_map_apply _ _ _ measurable_from_top hS]
  exact conditionedOuterLaw_density θ n hn _

end
end PottsDiscontinuity.Potts
