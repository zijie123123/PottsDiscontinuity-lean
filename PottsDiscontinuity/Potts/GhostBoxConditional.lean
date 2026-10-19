module

public import PottsDiscontinuity.Potts.BoolMeasureBridge
public import PottsDiscontinuity.Potts.GhostBoxCylinders
public import PottsDiscontinuity.Potts.GhostBoxLaw

/-! Exact conditional cylinder probabilities for the literal ghost boundary. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace
local instance conditionalBoundaryFintype (n : ℕ) : Fintype (BoundaryVertex (box n)) := Fintype.ofFinite _
local instance conditionalOuterEdgeFintype (n : ℕ) : Fintype (OuterBoxEdge n) := Fintype.ofFinite _
local instance conditionalGhostMeasurable (n : ℕ) : MeasurableSpace (LiteralBond (box n) → Bool) := ⊤
local instance conditionalGhostDiscrete (n : ℕ) : DiscreteMeasurableSpace (LiteralBond (box n) → Bool) :=
  ⟨fun _ => trivial⟩

theorem nestedRestriction_bool_read (n : ℕ) (Ω : OuterBoxEdge n → Bool) :
    FK.embeddedConfigurationRestriction _ _ (nestedBoxEmbedding (Nat.le_succ n))
      (nestedBox_map_le (Nat.le_succ n)) (FK.boolConfigurationEquiv _ Ω) =
    FK.boolConfigurationEquiv _ (fun e => readLiteralBonds n Ω (.inl e)) := by
  ext e
  rw [FK.mem_embeddedConfigurationRestriction, FK.mem_boolConfigurationEquiv,
    FK.mem_boolConfigurationEquiv]
  rfl

theorem ghostBoxProbabilityMeasure_allOpen_sum (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (n : ℕ) (F : Finset squareLattice.edgeSet) :
    (ghostBoxProbabilityMeasure q hq β hβ n).toMeasure.real (FK.LatticeConfiguration.allOpen F) =
      ∑ ω, ghostRCProbability q (box n) β ω *
        (if ghostBoxConfiguration n ω ∈ FK.LatticeConfiguration.allOpen F then 1 else 0) := by
  change (((ghostRCLaw q hq (box n) β hβ).map (ghostBoxConfiguration n)).toMeasure _).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (FK.LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  rw [← Measure.real, finite_pmf_measureReal_sum]
  apply Finset.sum_congr
  · ext ω; simp
  · intro ω _
    rw [ghostRCLaw_apply, ENNReal.toReal_ofReal (ghostRCProbability_nonneg q hq (box n) β hβ ω)]
    by_cases h : ghostBoxConfiguration n ω ∈ FK.LatticeConfiguration.allOpen F <;> simp [h]

/-- Every supported increasing cylinder has exactly the conditioned outer
wired probability, with the literal one-edge-per-boundary-vertex correction. -/
theorem ghostBoxProbabilityMeasure_allOpen_eq_conditional
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (n : ℕ) (hn : 0 < n)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, ∃ f, FK.frozenEdgeEmbedding (box n) f = e) :
    (ghostBoxProbabilityMeasure q hq β hβ n).toMeasure.real (FK.LatticeConfiguration.allOpen F) =
      (FK.measure _ (fkParameters q hq β hβ) (outerBoxWiring n)
        (openBoxCylinderEvent (n + 1) F ∩ cornerClosureEvent n)).toReal /
      (FK.measure _ (fkParameters q hq β hβ) (outerBoxWiring n) (cornerClosureEvent n)).toReal := by
  let f := fun ω : LiteralBond (box n) → Bool =>
    if ghostBoxConfiguration n ω ∈ FK.LatticeConfiguration.allOpen F then (1 : ℝ) else 0
  have hid := ghost_expectation_eq_conditioned_wired_box q hq β hβ n hn f
  rw [ghostBoxProbabilityMeasure_allOpen_sum]
  change (∑ ω, ghostRCProbability q (box n) β ω * f ω) = _
  rw [← hid]
  have hread (Ω : OuterBoxEdge n → Bool) :
      ghostBoxConfiguration n (readLiteralBonds n Ω) ∈ FK.LatticeConfiguration.allOpen F ↔
        FK.boolConfigurationEquiv _ Ω ∈ openBoxCylinderEvent (n + 1) F := by
    rw [ghostBoxConfiguration, openExtension_mem_allOpen]
    rw [← nestedRestriction_bool_read]
    exact Set.ext_iff.mp (nestedBoxEvent_openBoxCylinderEvent (Nat.le_succ n) F hF)
      (FK.boolConfigurationEquiv _ Ω)
  rw [fk_measureReal_eq_bool_sum, fk_measureReal_eq_bool_sum]
  apply congrArg₂ (fun (a : ℝ) (b : ℝ) => a / b)
  · apply Finset.sum_congr
    · ext Ω; simp
    · intro Ω _
      have hp := FK.configurationProbability_eq_rcProb (fkParameters q hq β hβ) (box (n + 1)) 1 Ω
      change FK.configurationProbability _ _ (outerBoxWiring n) _ = _ at hp
      rw [hp]
      by_cases hB : outerCornerClosed n Ω
      · have hb := (outerCornerClosed_iff_mem n Ω).mp hB
        by_cases hA : ghostBoxConfiguration n (readLiteralBonds n Ω) ∈ FK.LatticeConfiguration.allOpen F
        · simp [hB, hb, (hread Ω).mp hA, f, hA]
        · have ha := mt (hread Ω).mpr hA
          simp [hB, hb, ha, f, hA]
      · have hb := mt (outerCornerClosed_iff_mem n Ω).mpr hB
        simp [hB, hb]
  · apply Finset.sum_congr
    · ext Ω; simp
    · intro Ω _
      have hp := FK.configurationProbability_eq_rcProb (fkParameters q hq β hβ) (box (n + 1)) 1 Ω
      change FK.configurationProbability _ _ (outerBoxWiring n) _ = _ at hp
      rw [hp]
      by_cases hB : outerCornerClosed n Ω
      · have hb := (outerCornerClosed_iff_mem n Ω).mp hB
        simp [hB, hb]
      · have hb := mt (outerCornerClosed_iff_mem n Ω).mpr hB
        simp [hB, hb]

end
end PottsDiscontinuity.Potts
