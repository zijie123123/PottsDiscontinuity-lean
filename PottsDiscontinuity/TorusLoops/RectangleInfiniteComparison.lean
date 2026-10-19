module

public import PottsDiscontinuity.FK.FreeBoxPositiveAssociation

/-!
# Increasing events under the free box limit

Finite free FK boxes are monotone on every clopen increasing event of the
whole-lattice configuration space. The same comparison passes to the unique
free infinite-volume limit.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.FK
open PottsDiscontinuity.FK.Internal

noncomputable section

local instance rectangleInfiniteComparisonGenericEdgeFintype
    {V : Type*} [Finite V] {G : SimpleGraph V} : Fintype G.edgeSet := Fintype.ofFinite _

local instance rectangleInfiniteComparisonGenericEdgeDecidableEq
    {V : Type*} [Finite V] {G : SimpleGraph V} : DecidableEq G.edgeSet := Classical.decEq _

private theorem originBoxEdgeEmbedding_compatible {r s : ℕ}
    (hrs : r ≤ s)
    (hGH : (boxGraph (0, 0) r).map
        (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) ≤ boxGraph (0, 0) s)
    (e : (boxGraph (0, 0) r).edgeSet) :
    boxEdgeEmbedding (0, 0) s
        (embeddedEdgeEmbedding (boxGraph (0, 0) r) (boxGraph (0, 0) s)
          (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) hGH e) =
      boxEdgeEmbedding (0, 0) r e := by
  apply Subtype.ext
  change Sym2.map (fun v : BoxVertex (0, 0) s => v.val)
      (Sym2.map (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) e.val) =
    Sym2.map (fun v : BoxVertex (0, 0) r => v.val) e.val
  rw [Sym2.map_map]
  congr 1

private theorem boxConfiguration_restriction_le {r s : ℕ} (hrs : r ≤ s)
    (hGH : (boxGraph (0, 0) r).map
        (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) ≤ boxGraph (0, 0) s)
    (B : Configuration (boxGraph (0, 0) s)) :
    boxConfiguration (0, 0) r
        (embeddedConfigurationRestriction (boxGraph (0, 0) r) (boxGraph (0, 0) s)
          (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) hGH B) ≤
      boxConfiguration (0, 0) s B := by
  intro e he
  rw [boxConfiguration_open_iff] at he ⊢
  obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp he
  have hmem := (mem_embeddedConfigurationRestriction _ _ _ _ B a).mp ha
  apply Finset.mem_map.mpr
  refine ⟨embeddedEdgeEmbedding (boxGraph (0, 0) r) (boxGraph (0, 0) s)
    (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) hGH a, hmem, ?_⟩
  calc
    boxEdgeEmbedding (0, 0) s
        (embeddedEdgeEmbedding (boxGraph (0, 0) r) (boxGraph (0, 0) s)
          (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) hGH a) =
      boxEdgeEmbedding (0, 0) r a := originBoxEdgeEmbedding_compatible hrs hGH a
    _ = e := hae

private theorem fkLaw_measure_toReal_eq_expectation
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (q : Parameters) (ξ : BoundaryCondition V)
    (S : Set (Configuration G)) :
    (measure G q ξ S).toReal =
      FiniteProbability.expectation (law G q ξ)
        (S.indicator (fun _ => (1 : ℝ))) := by
  rw [measure_toReal_eq_indicator_sum]
  unfold FiniteProbability.expectation
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : A ∈ S
  · simp [Set.indicator, h, law_apply,
      ENNReal.toReal_ofReal (configurationProbability_pos G q ξ A).le]
  · simp [Set.indicator, h]

private theorem boxProbabilityMeasure_event_eq_expectation (q : Parameters)
    (r : ℕ) (E : Set LatticeConfiguration) (hE : MeasurableSet E) :
    (((boxProbabilityMeasure q (0, 0) r : ProbabilityMeasure LatticeConfiguration) E : NNReal) : ℝ) =
      FiniteProbability.expectation (law (boxGraph (0, 0) r) q (BoundaryCondition.free ∅))
        (Set.indicator ({A | boxConfiguration (0, 0) r A ∈ E} :
          Set (Configuration (boxGraph (0, 0) r))) (fun _ => (1 : ℝ))) := by
  have hpre :
      ((boxProbabilityMeasure q (0, 0) r : Measure LatticeConfiguration) E) =
        measure (boxGraph (0, 0) r) q (BoundaryCondition.free ∅)
          {A | boxConfiguration (0, 0) r A ∈ E} := by
    change ((law (boxGraph (0, 0) r) q (BoundaryCondition.free ∅)).map
      (boxConfiguration (0, 0) r)).toMeasure E = _
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hE]
    rfl
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  rw [Measure.real_def]
  rw [hpre]
  exact fkLaw_measure_toReal_eq_expectation q (BoundaryCondition.free ∅) _

/-- The free origin-box laws are increasing on every clopen increasing event
of the actual whole-lattice configuration space. -/
theorem boxProbabilityMeasure_clopen_upper_mono (q : Parameters)
    (r s : ℕ) (hrs : r ≤ s) (E : Set LatticeConfiguration)
    (hEclopen : IsClopen E) (hEupper : IsUpperSet E) :
    boxProbabilityMeasure q (0, 0) r E ≤ boxProbabilityMeasure q (0, 0) s E := by
  classical
  let f := boxVertexEmbedding (latticeBox_mono (0, 0) hrs)
  have hGH : (boxGraph (0, 0) r).map f ≤ boxGraph (0, 0) s :=
    boxGraph_map_boxVertexEmbedding (latticeBox_mono (0, 0) hrs)
  let S : Set (Configuration (boxGraph (0, 0) r)) :=
    {A | boxConfiguration (0, 0) r A ∈ E}
  let F : Configuration (boxGraph (0, 0) r) → ℝ :=
    S.indicator (fun _ => (1 : ℝ))
  have hF0 : ∀ A, 0 ≤ F A := by
    intro A
    by_cases hA : A ∈ S <;> simp [F, hA]
  have hF : Monotone F := by
    intro A B hAB
    by_cases hA : A ∈ S
    · have hB : B ∈ S := hEupper (boxConfiguration_mono (0, 0) r hAB)
        (by simpa [S] using hA)
      simp [F, hA, hB]
    · simp only [F, Set.indicator_of_notMem hA]
      exact hF0 B
  have hcmp := embedded_free_expectation_le (boxGraph (0, 0) r) (boxGraph (0, 0) s)
    f hGH q ∅ ∅ F hF0 hF
  have hrestrict :
      FiniteProbability.expectation (law (boxGraph (0, 0) s) q (BoundaryCondition.free ∅))
        (fun B => F (embeddedConfigurationRestriction (boxGraph (0, 0) r)
          (boxGraph (0, 0) s) f hGH B)) ≤
      FiniteProbability.expectation (law (boxGraph (0, 0) s) q (BoundaryCondition.free ∅))
        (Set.indicator ({B | boxConfiguration (0, 0) s B ∈ E} :
          Set (Configuration (boxGraph (0, 0) s))) (fun _ => (1 : ℝ))) := by
    apply FiniteProbability.expectation_mono
    intro B
    have horder := boxConfiguration_restriction_le hrs hGH B
    by_cases hsmall : boxConfiguration (0, 0) r
        (embeddedConfigurationRestriction (boxGraph (0, 0) r) (boxGraph (0, 0) s) f hGH B) ∈ E
    · have hlarge : boxConfiguration (0, 0) s B ∈ E := hEupper horder hsmall
      simp [F, S, Set.indicator, hsmall, hlarge]
    · by_cases hlarge : boxConfiguration (0, 0) s B ∈ E <;>
        simp [F, S, Set.indicator, hsmall, hlarge]
  have hprob_r := boxProbabilityMeasure_event_eq_expectation q r E hEclopen.2.measurableSet
  have hprob_s := boxProbabilityMeasure_event_eq_expectation q s E hEclopen.2.measurableSet
  have hreal :
      (((boxProbabilityMeasure q (0, 0) r E : NNReal) : ℝ)) ≤
        (((boxProbabilityMeasure q (0, 0) s E : NNReal) : ℝ)) := by
    rw [hprob_r, hprob_s]
    exact hcmp.trans hrestrict
  exact NNReal.coe_le_coe.mp hreal

/-- Every finite free origin-box probability of a clopen increasing event is
bounded by its probability under the unique free infinite-volume limit. -/
theorem freeBoxLimit_clopen_upper_ge_box (q : Parameters)
    (r : ℕ) (E : Set LatticeConfiguration)
    (hEclopen : IsClopen E) (hEupper : IsUpperSet E) :
    boxProbabilityMeasure q (0, 0) r E ≤
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)) E := by
  let μ : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  have hweak : Tendsto (fun n => boxProbabilityMeasure q (0, 0) n) atTop (𝓝 μ) :=
    (Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).1
      (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  have hnr : Tendsto (fun n : ℕ => n + r) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hweakShift : Tendsto (fun n => boxProbabilityMeasure q (0, 0) (n + r)) atTop
      (𝓝 μ) := hweak.comp hnr
  have hprob : Tendsto (fun n => boxProbabilityMeasure q (0, 0) (n + r) E) atTop
      (𝓝 (μ E)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweakShift hEclopen
  have hfixed (n : ℕ) :
      boxProbabilityMeasure q (0, 0) r E ≤ boxProbabilityMeasure q (0, 0) (n + r) E :=
    boxProbabilityMeasure_clopen_upper_mono q r (n + r) (by omega) E hEclopen hEupper
  have hlim := le_of_tendsto_of_tendsto' tendsto_const_nhds hprob hfixed
  simpa [μ] using hlim

end
end PottsDiscontinuity.TorusLoops
