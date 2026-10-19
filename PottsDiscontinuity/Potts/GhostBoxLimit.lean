module

public import PottsDiscontinuity.Potts.GhostBoxConditional

/-! The literal ghost edge law converges to the wired FK box limit. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace

/-- The explicit finite-energy comparison squeeze for every supported cylinder. -/
theorem ghostBox_allOpen_squeeze (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, ∃ f, FK.frozenEdgeEmbedding (box (n - 1)) f = e) :
    let θ := fkParameters q hq β hβ
    let u := (openBoxProbabilityMeasure θ (n + 1)).toMeasure.real (FK.LatticeConfiguration.allOpen F)
    let c := (openBoxProbabilityMeasure θ (n - 1)).toMeasure.real (FK.LatticeConfiguration.allOpen F)
    let g := (ghostBoxProbabilityMeasure q hq β hβ n).toMeasure.real (FK.LatticeConfiguration.allOpen F)
    u - (c - u) / (1 - FK.edgeParameter θ) ^ 4 ≤ g ∧ g ≤ u := by
  dsimp only
  let θ := fkParameters q hq β hβ
  let S := openBoxCylinderEvent (n - 1) F
  have hmn : n - 1 < n := by omega
  have hF' : ∀ e ∈ F, ∃ f, FK.frozenEdgeEmbedding (box n) f = e := by
    intro e he
    obtain ⟨f, hf⟩ := hF e he
    exact ⟨FK.embeddedEdgeEmbedding _ _ (nestedBoxEmbedding (show n - 1 ≤ n by omega))
      (nestedBox_map_le _) f, (nestedEdgeEmbedding_compatible _ f).trans hf⟩
  have hrestrict := nestedBoxEvent_openBoxCylinderEvent (show n - 1 ≤ n + 1 by omega) F hF
  have hs := corner_corrected_box_squeeze θ hmn S (openBoxCylinderEvent_upper _ _)
  dsimp only at hs
  change nestedBoxEvent _ S = openBoxCylinderEvent (n + 1) F at hrestrict
  rw [hrestrict] at hs
  rw [ghostBoxProbabilityMeasure_allOpen_eq_conditional q hq β hβ n (by omega) F hF']
  simp only [Measure.real, openBoxProbabilityMeasure_allOpen]
  exact hs

/-- All increasing cylinder probabilities of the literal ghost law converge
 to those of any weak wired-box limit. -/
theorem ghostBox_allOpen_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 μ)) (F : Finset squareLattice.edgeSet) :
    Tendsto (fun n => (ghostBoxProbabilityMeasure q hq β hβ n).toMeasure.real
      (FK.LatticeConfiguration.allOpen F)) atTop (𝓝 (μ.toMeasure.real (FK.LatticeConfiguration.allOpen F))) := by
  let θ := fkParameters q hq β hβ
  have hw : Tendsto (fun n => (openBoxProbabilityMeasure θ n).toMeasure.real
      (FK.LatticeConfiguration.allOpen F)) atTop (𝓝 (μ.toMeasure.real (FK.LatticeConfiguration.allOpen F))) := by
    have ht := FK.LatticeConfiguration.tendsto_allOpen_of_weak hμ F
    have ht' := NNReal.continuous_coe.continuousAt.tendsto.comp ht
    simpa only [openBoxProbabilityMeasure_eq_wired, ProbabilityMeasure.measureReal_eq_coe_coeFn,
      Function.comp_def] using ht'
  have hu := hw.comp (tendsto_add_atTop_nat 1)
  have hc := hw.comp (tendsto_sub_atTop_nat 1)
  have hl := hu.sub ((hc.sub hu).div_const ((1 - FK.edgeParameter θ) ^ 4))
  simp only [sub_self, zero_div, sub_zero] at hl
  have hevent : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
      ∀ e ∈ F, ∃ f, FK.frozenEdgeEmbedding (box (n - 1)) f = e := by
    have hs : ∀ᶠ m : ℕ in atTop, ∀ e ∈ F, ∃ f, FK.frozenEdgeEmbedding (box m) f = e := by
      apply (eventually_all_finset F).2
      intro e _
      exact (FK.eventually_edge_lift_box e).mono (fun n hn => by
        obtain ⟨f, hf⟩ := hn
        exact ⟨f, Subtype.ext hf⟩)
    exact (eventually_ge_atTop 1).and ((tendsto_sub_atTop_nat 1).eventually hs)
  have hb := hevent.mono (fun n hn => ghostBox_allOpen_squeeze q hq β hβ n hn.1 F hn.2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu (hb.mono fun _ h => h.1)
    (hb.mono fun _ h => h.2)

end
end PottsDiscontinuity.Potts
