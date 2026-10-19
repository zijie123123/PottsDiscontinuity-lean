module

public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.UniformOn

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Set Topology
open scoped symmDiff
open scoped ENNReal

noncomputable section

/-- An event of a product field which reads only the coordinates in `F`. -/
def DependsOnIndices {I C : Type*} (F : Finset I) (A : Set (I → C)) : Prop :=
  ∀ u v, (∀ i ∈ F, u i = v i) → (u ∈ A ↔ v ∈ A)

theorem DependsOnIndices.mono {I C : Type*} {F G : Finset I} {A : Set (I → C)}
    (h : DependsOnIndices F A) (hFG : F ⊆ G) : DependsOnIndices G A := by
  intro u v huv
  exact h u v (fun i hi => huv i (hFG hi))

theorem DependsOnIndices.compl {I C : Type*} {F : Finset I} {A : Set (I → C)}
    (h : DependsOnIndices F A) : DependsOnIndices F Aᶜ := by
  intro u v huv
  exact not_congr (h u v huv)

theorem DependsOnIndices.union {I C : Type*} [DecidableEq I] {F G : Finset I}
    {A B : Set (I → C)} (hA : DependsOnIndices F A) (hB : DependsOnIndices G B) :
    DependsOnIndices (F ∪ G) (A ∪ B) := by
  intro u v huv
  apply or_congr
  · exact hA u v (fun i hi => huv i (Finset.mem_union.mpr (.inl hi)))
  · exact hB u v (fun i hi => huv i (Finset.mem_union.mpr (.inr hi)) )

theorem dependsOnIndices_sdiff {I C : Type*} [DecidableEq I] {F G : Finset I}
    {A B : Set (I → C)} (hA : DependsOnIndices F A) (hB : DependsOnIndices G B) :
    DependsOnIndices (F ∪ G) (A \ B) := by
  intro u v huv
  simp only [Set.mem_sdiff]
  exact and_congr (hA u v (fun i hi => huv i (Finset.mem_union.mpr (.inl hi))))
    (not_congr (hB u v (fun i hi => huv i (Finset.mem_union.mpr (.inr hi)))))

def finiteIndexEvents {I C : Type*} : Set (Set (I → C)) :=
  {A | ∃ F : Finset I, DependsOnIndices F A}

theorem finiteIndexEvents_isSetRing {I C : Type*} [DecidableEq I] :
    IsSetRing (finiteIndexEvents (I := I) (C := C)) where
  empty_mem := ⟨∅, by intro u v _; simp⟩
  union_mem := by
    rintro A B ⟨F, hF⟩ ⟨G, hG⟩
    exact ⟨F ∪ G, hF.union hG⟩
  sdiff_mem := by
    rintro A B ⟨F, hF⟩ ⟨G, hG⟩
    exact ⟨F ∪ G, dependsOnIndices_sdiff hF hG⟩

def finiteCoordinateRestrict {I C : Type*} (F : Finset I) (u : I → C) :
    (↥F → C) := fun i => u i.1

def finiteCoordinateExtend {I C : Type*} [DecidableEq I]
    (F : Finset I) (c₀ : C) (u : ↥F → C) : I → C :=
  fun i => if h : i ∈ F then u ⟨i, h⟩ else c₀

private theorem finiteCoordinateRestrict_measurable {I C : Type*}
    [MeasurableSpace C] (F : Finset I) :
    Measurable (finiteCoordinateRestrict F : (I → C) → (↥F → C)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply i.1

private theorem measurableSet_of_finite_type {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Finite X] (A : Set X) : MeasurableSet A := by
  classical
  have hA : A = ⋃ x : A, ({x.1} : Set X) := by ext x; simp
  rw [hA]
  exact MeasurableSet.iUnion fun x => MeasurableSet.singleton x.1

private theorem finiteIndexEvent_measurable {I C : Type*} [Countable I] [Finite C]
    [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq I]
    (c₀ : C) {A : Set (I → C)} (hA : A ∈ finiteIndexEvents (I := I) (C := C)) :
    MeasurableSet A := by
  obtain ⟨F, hF⟩ := hA
  let r : (I → C) → (↥F → C) := finiteCoordinateRestrict F
  let e : (↥F → C) → (I → C) := finiteCoordinateExtend F c₀
  have heq : A = r ⁻¹' (e ⁻¹' A) := by
    ext u
    change u ∈ A ↔ e (r u) ∈ A
    apply hF u (e (r u)) ?_
    intro i hi
    simp [e, r, finiteCoordinateExtend, finiteCoordinateRestrict, hi]
  rw [heq]
  have hEA : MeasurableSet (e ⁻¹' A) := measurableSet_of_finite_type _
  exact finiteCoordinateRestrict_measurable F hEA

private theorem finiteCoordinateCylinder_generateFrom {I C : Type*} [Countable I]
    [Finite C] [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq I]
    (c₀ : C) :
    (inferInstance : MeasurableSpace (I → C)) =
      MeasurableSpace.generateFrom (finiteIndexEvents (I := I) (C := C)) := by
  classical
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · refine iSup_le fun i => ?_
    refine MeasurableSpace.comap_le_iff_le_map.2 ?_
    intro T hT
    have heq : (fun u : I → C => u i) ⁻¹' T = ⋃ c : T, {u | u i = c.1} := by
      ext u
      simp
    show MeasurableSet[MeasurableSpace.generateFrom
      (finiteIndexEvents (I := I) (C := C))] ((fun u : I → C => u i) ⁻¹' T)
    rw [heq]
    refine MeasurableSet.iUnion fun c => ?_
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨{i}, ?_⟩
    intro u v huv
    change u i = c.1 ↔ v i = c.1
    rw [huv i (by simp)]
  · intro A hA
    exact finiteIndexEvent_measurable (I := I) (C := C) c₀ hA

private theorem finiteIndexEvent_approx {I C : Type*} [Countable I] [Finite C]
    [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq I]
    (μ : Measure (I → C)) [IsFiniteMeasure μ] (c₀ : C)
    {A : Set (I → C)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ B, B ∈ finiteIndexEvents (I := I) (C := C) ∧ μ (B ∆ A) < ε := by
  have hcover : ∃ D : Set (Set (I → C)), D.Countable ∧
      D ⊆ finiteIndexEvents (I := I) (C := C) ∧ μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, Set.countable_singleton _, ?_, by simp⟩
    intro B hB
    subst B
    exact ⟨∅, by intro u v _; simp⟩
  exact exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (finiteIndexEvents_isSetRing (I := I) (C := C)) hcover
    (finiteCoordinateCylinder_generateFrom (I := I) (C := C) c₀) hA hε

theorem abs_measureReal_sub_le_symmDiff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |μ.real A - μ.real B| ≤ μ.real (A ∆ B) := by
  have h := (MeasuredSets.lipschitzWith_measureReal (μ := μ)).dist_le_mul
    (⟨A, hA⟩ : MeasuredSets μ) (⟨B, hB⟩ : MeasuredSets μ)
  change |μ.real A - μ.real B| ≤ (1 : ℝ) * μ.real (A ∆ B) at h
  simpa only [one_mul] using h

def iidFieldMeasure {I C : Type*} [MeasurableSpace C]
    (ν : Measure C) : Measure (I → C) := Measure.infinitePi (fun _ => ν)

def iidFieldShift {I C : Type*} (e : I ≃ I) (u : I → C) : I → C :=
  fun i => u (e.symm i)

theorem iidFieldShift_measurePreserving {I C : Type*} [MeasurableSpace C]
    (ν : Measure C) [IsProbabilityMeasure ν] (e : I ≃ I) :
    MeasurePreserving (iidFieldShift e) (iidFieldMeasure ν) (iidFieldMeasure ν) := by
  constructor
  · exact measurable_pi_iff.mpr fun i => measurable_pi_apply (e.symm i)
  · have hfun : iidFieldShift e =
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : I => C) e) := by
      funext u i
      simp [iidFieldShift, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    rw [hfun]
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : I => ν) e

theorem iidField_independent_supported_events {I C : Type*} [DecidableEq I]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    (ν : Measure C) [IsProbabilityMeasure ν] (c₀ : C) (F G : Finset I)
    (hFG : Disjoint F G) (A B : Set (I → C))
    (hA : DependsOnIndices F A) (hB : DependsOnIndices G B) :
    iidFieldMeasure ν (A ∩ B) = iidFieldMeasure ν A * iidFieldMeasure ν B := by
  classical
  let μ : Measure (I → C) := iidFieldMeasure ν
  let projF : (I → C) → (↥F → C) := finiteCoordinateRestrict F
  let projG : (I → C) → (↥G → C) := finiteCoordinateRestrict G
  let extF : (↥F → C) → (I → C) := finiteCoordinateExtend F c₀
  let extG : (↥G → C) → (I → C) := finiteCoordinateExtend G c₀
  have hAeq : A = projF ⁻¹' (extF ⁻¹' A) := by
    ext u
    change u ∈ A ↔ extF (projF u) ∈ A
    apply hA u (extF (projF u))
    intro i hi
    simp [extF, projF, finiteCoordinateExtend, finiteCoordinateRestrict, hi]
  have hBeq : B = projG ⁻¹' (extG ⁻¹' B) := by
    ext u
    change u ∈ B ↔ extG (projG u) ∈ B
    apply hB u (extG (projG u))
    intro i hi
    simp [extG, projG, finiteCoordinateExtend, finiteCoordinateRestrict, hi]
  have hEval : ProbabilityTheory.iIndepFun (fun i (u : I → C) => u i) μ := by
    exact ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : I => ν)
      (X := fun _ (c : C) => c) (by fun_prop)
  have hProj := hEval.indepFun_finset F G hFG (fun i => measurable_pi_apply i)
  rw [hAeq, hBeq]
  exact hProj.measure_inter_preimage_eq_mul (extF ⁻¹' A) (extG ⁻¹' B)
    (measurableSet_of_finite_type _) (measurableSet_of_finite_type _)

theorem DependsOnIndices.preimage_iidFieldShift {I C : Type*} {F : Finset I}
    {A : Set (I → C)} (hA : DependsOnIndices F A) (e : I ≃ I) :
    DependsOnIndices (F.map e.symm.toEmbedding) (iidFieldShift e ⁻¹' A) := by
  intro u v huv
  change iidFieldShift e u ∈ A ↔ iidFieldShift e v ∈ A
  apply hA
  intro i hi
  have himage : e.symm i ∈ F.map e.symm.toEmbedding :=
    Finset.mem_map.mpr ⟨i, hi, rfl⟩
  have heq := huv (e.symm i) himage
  simpa [iidFieldShift] using heq

theorem iidField_mixing_of_finite_separation {I C : Type*} [Countable I] [DecidableEq I]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    (ν : Measure C) [IsProbabilityMeasure ν] (c₀ : C)
    (e : (ℤ × ℤ) → I ≃ I)
    (hsep : ∀ F G : Finset I, ∀ᶠ a : ℤ × ℤ in cofinite,
      Disjoint F (G.map (e a).symm.toEmbedding))
    {A B : Set (I → C)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun a : ℤ × ℤ =>
      (iidFieldMeasure ν).real (A ∩ iidFieldShift (e a) ⁻¹' B)) cofinite
      (𝓝 ((iidFieldMeasure ν).real A * (iidFieldMeasure ν).real B)) := by
  let μ : Measure (I → C) := iidFieldMeasure ν
  have hμprob : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ => ν))
    infer_instance
  let := hμprob
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A', hA'fin, hA'err⟩ := finiteIndexEvent_approx μ c₀ hA
    (ENNReal.ofReal_pos.mpr hδ)
  obtain ⟨B', hB'fin, hB'err⟩ := finiteIndexEvent_approx μ c₀ hB
    (ENNReal.ofReal_pos.mpr hδ)
  have hA'meas : MeasurableSet A' := finiteIndexEvent_measurable c₀ hA'fin
  have hB'meas : MeasurableSet B' := finiteIndexEvent_measurable c₀ hB'fin
  have hA'errR : μ.real (A' ∆ A) < δ := by
    have ht := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hA'err
    simpa [δ, Measure.real_def, ENNReal.toReal_ofReal hδ.le] using ht
  have hB'errR : μ.real (B' ∆ B) < δ := by
    have ht := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hB'err
    simpa [δ, Measure.real_def, ENNReal.toReal_ofReal hδ.le] using ht
  obtain ⟨F, hF⟩ := hA'fin
  obtain ⟨G, hG⟩ := hB'fin
  have hsepFG := hsep F G
  filter_upwards [hsepFG] with a ha
  let Ta : (I → C) → (I → C) := iidFieldShift (e a)
  have hT : MeasurePreserving Ta μ μ := by
    simpa [Ta, μ, iidFieldMeasure] using iidFieldShift_measurePreserving ν (e a)
  have hBshift : DependsOnIndices (G.map (e a).symm.toEmbedding) (Ta ⁻¹' B') :=
    hG.preimage_iidFieldShift (e a)
  have hind := iidField_independent_supported_events ν c₀ F
    (G.map (e a).symm.toEmbedding) ha A' (Ta ⁻¹' B') hF hBshift
  have hBerrShift : μ.real ((Ta ⁻¹' B) ∆ (Ta ⁻¹' B')) = μ.real (B' ∆ B) := by
    have hpre : (Ta ⁻¹' B) ∆ (Ta ⁻¹' B') = Ta ⁻¹' (B ∆ B') := by
      exact (Set.preimage_symmDiff (f := Ta) B B').symm
    calc
      _ = μ.real (Ta ⁻¹' (B ∆ B')) := by rw [hpre]
      _ = μ.real (B ∆ B') := by
        simp only [Measure.real_def]
        rw [← Measure.map_apply hT.measurable (hB.symmDiff hB'meas), hT.map_eq]
      _ = μ.real (B' ∆ B) := by rw [symmDiff_comm]
  have hJointSet : (A ∩ (Ta ⁻¹' B)) ∆ (A' ∩ (Ta ⁻¹' B')) ⊆
      (A ∆ A') ∪ ((Ta ⁻¹' B) ∆ (Ta ⁻¹' B')) := by
    intro u hu
    simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union, Set.mem_preimage] at hu ⊢
    tauto
  have hJointErr : |μ.real (A ∩ Ta ⁻¹' B) - μ.real (A' ∩ Ta ⁻¹' B')| ≤
      μ.real (A ∆ A') + μ.real (B' ∆ B) := by
    have hleft : MeasurableSet (A ∩ Ta ⁻¹' B) := hA.inter (hT.measurable hB)
    have hright : MeasurableSet (A' ∩ Ta ⁻¹' B') := hA'meas.inter (hT.measurable hB'meas)
    have hdiff := abs_measureReal_sub_le_symmDiff μ hleft hright
    calc
      _ ≤ μ.real ((A ∩ (Ta ⁻¹' B)) ∆ (A' ∩ (Ta ⁻¹' B'))) := hdiff
      _ ≤ μ.real ((A ∆ A') ∪ ((Ta ⁻¹' B) ∆ (Ta ⁻¹' B'))) := measureReal_mono hJointSet
      _ ≤ μ.real (A ∆ A') + μ.real ((Ta ⁻¹' B) ∆ (Ta ⁻¹' B')) := measureReal_union_le _ _
      _ = _ := by rw [hBerrShift]
  have hProbProdErr : |μ.real A * μ.real B - μ.real A' * μ.real B'| ≤
      μ.real (A ∆ A') + μ.real (B' ∆ B) := by
    have hAerr₀ := abs_measureReal_sub_le_symmDiff μ hA'meas hA
    have hBerr₀ := abs_measureReal_sub_le_symmDiff μ hB'meas hB
    have hAerr : |μ.real A - μ.real A'| ≤ μ.real (A ∆ A') := by
      simpa only [abs_sub_comm, symmDiff_comm] using hAerr₀
    have hBerr : |μ.real B - μ.real B'| ≤ μ.real (B' ∆ B) := by
      simpa [abs_sub_comm] using hBerr₀
    have hA₀ : 0 ≤ μ.real A := measureReal_nonneg
    have hB₀ : 0 ≤ μ.real B := measureReal_nonneg
    have hA'₀ : 0 ≤ μ.real A' := measureReal_nonneg
    have hA'₁ : μ.real A' ≤ 1 := measureReal_le_one
    have hB₁ : μ.real B ≤ 1 := measureReal_le_one
    calc
      _ = |(μ.real A - μ.real A') * μ.real B + μ.real A' * (μ.real B - μ.real B')| := by
        congr 1
        ring
      _ ≤ |(μ.real A - μ.real A') * μ.real B| +
          |μ.real A' * (μ.real B - μ.real B')| := abs_add_le _ _
      _ = |μ.real A - μ.real A'| * μ.real B +
          μ.real A' * |μ.real B - μ.real B'| := by
        rw [abs_mul, abs_of_nonneg hB₀, abs_mul, abs_of_nonneg hA'₀]
      _ ≤ _ := by
        have h1 : |μ.real A - μ.real A'| * μ.real B ≤ μ.real (A ∆ A') := by
          calc
            _ ≤ |μ.real A - μ.real A'| * 1 :=
              mul_le_mul_of_nonneg_left hB₁ (abs_nonneg (μ.real A - μ.real A'))
            _ = |μ.real A - μ.real A'| := by ring
            _ ≤ _ := hAerr
        have h2 : μ.real A' * |μ.real B - μ.real B'| ≤ μ.real (B' ∆ B) := by
          calc
            _ ≤ 1 * |μ.real B - μ.real B'| :=
              mul_le_mul_of_nonneg_right hA'₁ (abs_nonneg (μ.real B - μ.real B'))
            _ = |μ.real B - μ.real B'| := by ring
            _ ≤ _ := hBerr
        linarith
  have htarget : μ.real (A' ∩ (Ta ⁻¹' B')) = μ.real A' * μ.real B' := by
    have hreal := congrArg ENNReal.toReal hind
    rw [ENNReal.toReal_mul] at hreal
    have hreal' : μ.real (A' ∩ (Ta ⁻¹' B')) =
        μ.real A' * μ.real (Ta ⁻¹' B') := by
      simpa [μ, Measure.real_def] using hreal
    have hmass : μ.real (Ta ⁻¹' B') = μ.real B' := by
      simp only [Measure.real_def]
      rw [← Measure.map_apply hT.measurable hB'meas, hT.map_eq]
    rw [hmass] at hreal'
    exact hreal'
  rw [htarget] at hJointErr
  have hbound : |μ.real (A ∩ Ta ⁻¹' B) - μ.real A * μ.real B| < ε := by
    have hA'errR' : μ.real (A ∆ A') < δ := by
      simpa only [symmDiff_comm] using hA'errR
    have hsum : μ.real (A ∆ A') + μ.real (B' ∆ B) < 2 * δ := by
      linarith [hA'errR', hB'errR]
    calc
      _ ≤ |μ.real (A ∩ (Ta ⁻¹' B)) - μ.real (A' ∩ (Ta ⁻¹' B'))| +
          |μ.real A' * μ.real B' - μ.real A * μ.real B| := by
            calc
              _ ≤ |μ.real (A ∩ (Ta ⁻¹' B)) - μ.real (A' ∩ (Ta ⁻¹' B'))| +
                  |μ.real (A' ∩ (Ta ⁻¹' B')) - μ.real A * μ.real B| :=
                abs_sub_le (μ.real (A ∩ (Ta ⁻¹' B)))
                  (μ.real (A' ∩ (Ta ⁻¹' B'))) (μ.real A * μ.real B)
              _ = _ := by rw [htarget]
      _ ≤ 2 * (μ.real (A ∆ A') + μ.real (B' ∆ B)) := by
        have hprod : |μ.real A' * μ.real B' - μ.real A * μ.real B| ≤
            μ.real (A ∆ A') + μ.real (B' ∆ B) := by
          simpa [abs_sub_comm, mul_comm] using hProbProdErr
        rw [htarget]
        nlinarith [hJointErr, hprod]
      _ < ε := by dsimp [δ] at hsum ⊢; nlinarith
  simpa [μ, Ta, Real.dist_eq] using hbound

end
end PottsDiscontinuity.PottsThm
