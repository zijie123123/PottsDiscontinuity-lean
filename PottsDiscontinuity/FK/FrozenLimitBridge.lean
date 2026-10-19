/- Original bridge proofs for the frozen random-cluster cylinder definition.
The graph-edge embedding follows the same source. -/
module

public import PottsDiscontinuity.FK.BoxLaw
public import PottsDiscontinuity.FK.EndpointLimits
public import PottsDiscontinuity.FK.IncreasingEvents

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK

noncomputable section

/-- The original whole-lattice edge represented by an edge of a finite induced domain. -/
def frozenEdgeEmbedding (S : Finset (ℤ × ℤ)) :
    (squareLattice.induce (S : Set (ℤ × ℤ))).edgeSet ↪ squareLattice.edgeSet :=
  (show squareLattice.induce (S : Set (ℤ × ℤ)) ↪g squareLattice from
    { toFun := Subtype.val, inj' := Subtype.val_injective, map_rel_iff' := Iff.rfl }).mapEdgeSet

/-- A finite prescribed pattern on the original lattice edges. -/
def patternCylinder (A : Finset squareLattice.edgeSet)
    (ξ : squareLattice.edgeSet → Bool) : Set LatticeConfiguration :=
  {ω | ∀ e ∈ A, ω e = ξ e}

/-- Every finite edge pattern is clopen in the product topology. -/
theorem patternCylinder_isClopen (A : Finset squareLattice.edgeSet)
    (ξ : squareLattice.edgeSet → Bool) : IsClopen (patternCylinder A ξ) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa [patternCylinder] using isClopen_univ (X := LatticeConfiguration)
  | insert e A he ih =>
      have h : patternCylinder (insert e A) ξ =
          {ω : LatticeConfiguration | ω e = ξ e} ∩ patternCylinder A ξ := by
        ext ω
        simp [patternCylinder]
      rw [h]
      exact ((isClopen_discrete ({ξ e} : Set Bool)).preimage (continuous_apply e)).inter ih

/-- The exact frozen finite law, mapped by any chosen whole-lattice extension. -/
def frozenExtendedProbabilityMeasure (θ : Parameters) (S : Finset (ℤ × ℤ)) (i : Fin 2)
    (ext : Configuration (squareLattice.induce (S : Set (ℤ × ℤ))) → LatticeConfiguration) :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨((law _ θ (frozenBoundaryCondition S i)).map ext).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

attribute [local instance] configurationMeasurableSpace

open Classical in
/-- Once the pattern lies in the domain, extension gives exactly the frozen finite cylinder sum. -/
theorem frozenExtendedProbabilityMeasure_pattern (θ : Parameters)
    (S : Finset (ℤ × ℤ)) (i : Fin 2)
    (ext : Configuration (squareLattice.induce (S : Set (ℤ × ℤ))) → LatticeConfiguration)
    (hExt : ∀ C f, ext C (frozenEdgeEmbedding S f) = decide (f ∈ C))
    (A : Finset squareLattice.edgeSet) (ξ : squareLattice.edgeSet → Bool)
    (hA : ∀ e ∈ A, ∃ f, frozenEdgeEmbedding S f = e) :
    (frozenExtendedProbabilityMeasure θ S i ext).toMeasure.real (patternCylinder A ξ) =
      ∑ ω : (squareLattice.induce (S : Set (ℤ × ℤ))).edgeSet → Bool,
        if ∀ e ∈ A, ∃ f : (squareLattice.induce (S : Set (ℤ × ℤ))).edgeSet,
            Sym2.map Subtype.val f.1 = e.1 ∧ ω f = ξ e
        then rcProb S θ.toP θ.toQ i ω else 0 := by
  classical
  have hpoint (ω : (squareLattice.induce (S : Set (ℤ × ℤ))).edgeSet → Bool) :
      ext (boolConfigurationEquiv _ ω) ∈ patternCylinder A ξ ↔
        ∀ e ∈ A, ∃ f : (squareLattice.induce (S : Set (ℤ × ℤ))).edgeSet,
          Sym2.map Subtype.val f.1 = e.1 ∧ ω f = ξ e := by
    have hvalue (f : (squareLattice.induce (S : Set (ℤ × ℤ))).edgeSet) :
        ext (boolConfigurationEquiv _ ω) (frozenEdgeEmbedding S f) = ω f := by
      rw [hExt]
      simp only [mem_boolConfigurationEquiv]
      cases ω f <;> rfl
    constructor
    · intro h e he
      obtain ⟨f, hf⟩ := hA e he
      refine ⟨f, congrArg Subtype.val hf, ?_⟩
      rw [← hvalue, hf]
      exact h e he
    · intro h e he
      obtain ⟨f, hf, hω⟩ := h e he
      have hf' : frozenEdgeEmbedding S f = e := Subtype.ext hf
      rw [← hf', hvalue]
      simpa only [hf'] using hω
  change (((law _ θ (frozenBoundaryCondition S i)).map ext).toMeasure
    (patternCylinder A ξ)).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (patternCylinder_isClopen A ξ).isOpen.measurableSet]
  change (measure _ θ (frozenBoundaryCondition S i) (ext ⁻¹' patternCylinder A ξ)).toReal = _
  rw [measure_toReal_eq_indicator_sum]
  symm
  refine Finset.sum_bij (fun ω _ => boolConfigurationEquiv _ ω) ?_ ?_ ?_ ?_
  · intro ω _
    simp only [Finset.mem_univ]
  · intro ω _ η _ h
    exact (boolConfigurationEquiv _).injective h
  · intro C _
    exact ⟨(boolConfigurationEquiv _).symm C, Finset.mem_univ _,
      (boolConfigurationEquiv _).apply_symm_apply C⟩
  · intro ω _
    rw [configurationProbability_eq_rcProb]
    simp only [Set.indicator, Set.mem_preimage, hpoint]
    split <;> simp

open Classical in
/-- Weak convergence of extensions preserving sampled edges implies the exact frozen cylinder limit. -/
theorem isRCInfiniteVolumeLimit_of_extended_tendsto (θ : Parameters) (i : Fin 2)
    (S : ℕ → Finset (ℤ × ℤ)) (hS : ∀ n, S n = box n)
    (ext : ∀ n, Configuration (squareLattice.induce (S n : Set (ℤ × ℤ))) → LatticeConfiguration)
    (hExt : ∀ n C f, ext n C (frozenEdgeEmbedding (S n) f) = decide (f ∈ C))
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (fun n => frozenExtendedProbabilityMeasure θ (S n) i (ext n))
      atTop (𝓝 μ)) : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ.toMeasure := by
  have hS' : S = box := funext hS
  subst S
  constructor
  · exact μ.prop
  · intro A ξ
    have hconv := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ
      (patternCylinder_isClopen A ξ)
    have hreal : Tendsto
        (fun n => (frozenExtendedProbabilityMeasure θ (box n) i (ext n)).toMeasure.real
          (patternCylinder A ξ)) atTop (𝓝 (μ.toMeasure.real (patternCylinder A ξ))) := by
      simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
        NNReal.continuous_coe.continuousAt.tendsto.comp hconv
    refine hreal.congr' ?_
    have hsupp : ∀ᶠ n : ℕ in atTop, ∀ e ∈ A,
        ∃ f : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet,
          Sym2.map Subtype.val f.1 = e.1 :=
      (eventually_all_finset A).2 fun e _ => eventually_edge_lift_box e
    filter_upwards [hsupp] with n hn
    have hA : ∀ e ∈ A, ∃ f, frozenEdgeEmbedding (box n) f = e := by
      intro e he
      obtain ⟨f, hf⟩ := hn e he
      exact ⟨f, Subtype.ext hf⟩
    have h := frozenExtendedProbabilityMeasure_pattern θ (box n) i (ext n)
      (hExt n) A ξ hA
    rw [h]
    refine Finset.sum_congr ?_ ?_
    · ext ω
      simp only [Finset.mem_univ]
    · intro ω _
      split_ifs <;> rfl

end
end PottsDiscontinuity.FK
