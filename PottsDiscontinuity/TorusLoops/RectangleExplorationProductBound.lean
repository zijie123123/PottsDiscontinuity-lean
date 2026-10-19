module

public import PottsDiscontinuity.TorusLoops.RectangleExplorationProduct

/-!
# Probability bounds for sequential rectangle exploration

This module turns the weighted one-step estimate into a bound on distinct
rooted crossings, one exact old-cluster observation at a time.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK

open scoped Classical

variable {N M : ℕ}

/-- Adding a new root to the distinct-crossing event implies the old event and
that the new root lies outside every old root cluster. -/
theorem rectangleDistinctRootCrossingEvent_append_projection
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (u : FaceVertex N M true) (A : Configuration (rectangleBaseGraph hN hM))
    (hA : A ∈ rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])) :
    A ∈ rectangleDistinctRootCrossingEvent hN hM roots ∧
      u ∉ rectangleRootClusterUnion hN hM roots A := by
  rcases hA with ⟨hcross, hnodup, hdistinct⟩
  have happend : ∀ x ∈ roots, x ∈ roots ++ [u] := by
    intro x hx
    exact List.mem_append.mpr (Or.inl hx)
  have hrootNodup : roots.Nodup := (List.nodup_append'.mp hnodup).1
  have hdisjoint := List.disjoint_of_nodup_append hnodup
  have hu_not_roots : u ∉ roots := by
    intro hu
    have hne := (List.disjoint_iff_ne.mp hdisjoint) u hu u
      (List.mem_singleton_self u)
    exact hne rfl
  have hroot_event : A ∈ rectangleDistinctRootCrossingEvent hN hM roots := by
    refine ⟨?_, hrootNodup, ?_⟩
    · intro x hx
      exact hcross x (happend x hx)
    · intro x hx y hy hxy
      exact hdistinct x (happend x hx) y (happend y hy) hxy
  refine ⟨hroot_event, ?_⟩
  intro huU
  rcases huU with ⟨x, hx, hxu⟩
  have hxu_ne : x ≠ u := by
    intro h
    subst x
    exact hu_not_roots hx
  exact hdistinct x (happend x hx) u
    (List.mem_append.mpr (Or.inr (List.mem_singleton_self u))) hxu_ne hxu

/-- A removed state consistent with an occurring labeled observation has that
same complete observation. -/
theorem rectangleObservationRemovedStateEvent_observation_eq
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (b : rectangleRootObservationIndex hN hM roots)
    (K : RemovedConfiguration (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedEdges hN hM
        (rectangleLabeledObservationVertexSet b.val)))
    (hK : K ∈ rectangleObservationRemovedStateEvent hN hM roots b.val) :
    rectangleLabeledRootClusterObservation hN hM roots K.val = b.val := by
  obtain ⟨B, hB⟩ := b.property
  apply Finset.ext
  intro pair
  change pair ∈ roots.toFinset.image
      (fun root => (root, rectangleRootClusterFinset hN hM K.val root)) ↔
    pair ∈ b.val
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨root, hroot, hpair⟩
    have hrecord :
        (root, rectangleRootClusterFinset hN hM K.val root) ∈ b.val :=
      hK.1 root (by simpa using hroot)
    exact hpair ▸ hrecord
  · intro hp
    have hpB : pair ∈ rectangleLabeledRootClusterObservation hN hM roots B := by
      have heq := congrArg (fun O => pair ∈ O) hB
      exact heq.mpr hp
    rcases Finset.mem_image.mp hpB with ⟨root, hroot, hpair⟩
    have hrecord :
        (root, rectangleRootClusterFinset hN hM K.val root) ∈ b.val :=
      hK.1 root (by simpa using hroot)
    have hrecordB :
        (root, rectangleRootClusterFinset hN hM K.val root) ∈
          rectangleLabeledRootClusterObservation hN hM roots B := by
      have heq := congrArg (fun O =>
        (root, rectangleRootClusterFinset hN hM K.val root) ∈ O) hB
      exact heq.mpr hrecord
    rcases Finset.mem_image.mp hrecordB with ⟨root', hroot', hrecordEq⟩
    have hrootEq : root' = root := by
      exact congrArg Prod.fst hrecordEq
    subst root'
    have hKpairEq :
        (root, rectangleRootClusterFinset hN hM K.val root) = pair :=
      hrecordEq.symm.trans hpair
    apply Finset.mem_image.mpr
    exact ⟨root, by simpa using hroot, hKpairEq⟩

/-- Configurations whose exact removed state is consistent with an occurring
observation belong to that observation's full configuration fiber. -/
theorem rectangleObservationRemovedState_preimage_subset_fiber
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (b : rectangleRootObservationIndex hN hM roots) :
    {A | rectangleComplementRemovedState hN hM
      (rectangleLabeledObservationVertexSet b.val) A ∈
        rectangleObservationRemovedStateEvent hN hM roots b.val} ⊆
      {A | rectangleRootObservationIndexOf hN hM roots A = b} := by
  obtain ⟨B, hB⟩ := b.property
  have hU : rectangleLabeledObservationVertexSet b.val =
      rectangleRootClusterUnion hN hM roots B := by
    exact (congrArg rectangleLabeledObservationVertexSet hB).symm.trans
      (rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots B)
  intro A hA
  let K := rectangleComplementRemovedState hN hM
    (rectangleLabeledObservationVertexSet b.val) A
  have hobsK := rectangleObservationRemovedStateEvent_observation_eq
    hN hM roots b K hA
  have hclosed : ∀ ⦃x y : FaceVertex N M true⦄,
      (openGraph (rectangleBaseGraph hN hM) K.val).Adj x y →
        x ∈ rectangleLabeledObservationVertexSet b.val ∧
          y ∈ rectangleLabeledObservationVertexSet b.val := hA.2
  have hcluster : ∀ root, root ∈ roots →
      rectangleRootClusterFinset hN hM K.val root =
        rectangleRootClusterFinset hN hM A root := by
    intro root hroot
    have hrootU : root ∈ rectangleLabeledObservationVertexSet b.val := by
      rw [hU]
      exact ⟨root, hroot, SimpleGraph.Reachable.rfl⟩
    exact rectangleRemovedState_clusterFinset_eq_of_open_edges_inside
      hN hM (rectangleLabeledObservationVertexSet b.val) A root hrootU hclosed
  have hobsA : rectangleLabeledRootClusterObservation hN hM roots A =
      rectangleLabeledRootClusterObservation hN hM roots K.val := by
    apply Finset.ext
    intro pair
    change pair ∈ roots.toFinset.image
        (fun root => (root, rectangleRootClusterFinset hN hM A root)) ↔
      pair ∈ roots.toFinset.image
        (fun root => (root, rectangleRootClusterFinset hN hM K.val root))
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨root, hroot, hpair⟩
      apply Finset.mem_image.mpr
      refine ⟨root, hroot, ?_⟩
      exact (congrArg (fun C => (root, C)) (hcluster root (by simpa using hroot))).trans hpair
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨root, hroot, hpair⟩
      apply Finset.mem_image.mpr
      refine ⟨root, hroot, ?_⟩
      exact (congrArg (fun C => (root, C)) (hcluster root (by simpa using hroot))).symm.trans hpair
  apply Subtype.ext
  exact hobsA.trans hobsK

/-- The new-root transfer is stable under replacing its cluster union by any
extensionally equal explored vertex set. -/
theorem rectangleRootCrossing_complement_of_clusterUnion_eq
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) (u : FaceVertex N M true)
    (U : Set (FaceVertex N M true))
    (hU : U = rectangleRootClusterUnion hN hM roots A)
    (huU : u ∉ U)
    (hseparate : ∀ x ∈ roots,
      ¬ ActualConnected (rectangleBaseGraph hN hM) A x u)
    (hcross : A ∈ rectangleRootCrossingEvent hN hM u) :
    rectangleComplementRootCrossingEvent hN hM U u huU
      (embeddedConfigurationRestriction (rectangleComplementGraph hN hM U)
        (rectangleBaseGraph hN hM) (rectangleComplementEmbedding U)
        (rectangleComplementGraph_map_le hN hM U) A) := by
  subst U
  exact rectangleRootCrossing_complement_of_distinct_roots
    hN hM roots A u hseparate hcross

/-- Old observations on which the new root is still unexplored. -/
def rectangleEligibleRootObservation (hN : Even N) (hM : Even M)
    (roots : List (FaceVertex N M true)) (u : FaceVertex N M true) :
    Set (rectangleRootObservationIndex hN hM roots) :=
  {b | b ∈ rectangleGoodRootObservation hN hM roots ∧
    u ∉ rectangleLabeledObservationVertexSet b.val}

/-- On each old-cluster observation fiber where the new root is outside the
explored union, the event of one more distinct crossing is bounded by the
free one-arm probability times the mass of that fiber. -/
theorem rectangleDistinctRootCrossingEvent_fiber_probability_le
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true)) (u : FaceVertex N M true)
    (hu : u.val.1.val = 0)
    (b : rectangleRootObservationIndex hN hM roots)
    (huU : u ∉ rectangleLabeledObservationVertexSet b.val) :
    let p := law (rectangleBaseGraph hN hM) (rectangleFKParameters q)
      (BoundaryCondition.free ∅)
    (p.toMeasure
      (rectangleDistinctRootCrossingEvent hN hM (roots ++ [u]) ∩
        {A | rectangleRootObservationIndexOf hN hM roots A = b})).toReal ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure
          {A | rectangleRootObservationIndexOf hN hM roots A = b}).toReal := by
  classical
  let G := rectangleBaseGraph hN hM
  let θ := rectangleFKParameters q
  let p := law G θ (BoundaryCondition.free ∅)
  let O := b.val
  let U := rectangleLabeledObservationVertexSet O
  let T := rectangleObservationRemovedStateEvent hN hM roots O
  let H := rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])
  let F := {A | rectangleRootObservationIndexOf hN hM roots A = b}
  let J := rectangleComplementJointEvent hN hM U
    (rectangleComplementRootCrossingEvent hN hM U u huU) T
  have hT : ∀ K ∈ T, ∀ ⦃x y : FaceVertex N M true⦄,
      (openGraph G K.val).Adj x y → x ∈ U ∧ y ∈ U := by
    intro K hK x y hxy
    exact hK.2 hxy
  have hweighted := rectangleWeightedExplorationRootCrossing_le
    hN hM q U u hu huU T hT
  have hsub : H ∩ F ⊆ J := by
    intro A hA
    rcases hA with ⟨hH, hF⟩
    have hprojection := rectangleDistinctRootCrossingEvent_append_projection
      hN hM roots u A hH
    rcases hH with ⟨hcross, hnodup, hdistinct⟩
    have huCross : A ∈ rectangleRootCrossingEvent hN hM u :=
      hcross u (List.mem_append.mpr (Or.inr (List.mem_singleton_self u)))
    have hseparate : ∀ x ∈ roots,
        ¬ ActualConnected G A x u := by
      intro x hx hxu
      exact hprojection.2 ⟨x, hx, hxu⟩
    have hobs : rectangleLabeledRootClusterObservation hN hM roots A = O := by
      exact congrArg Subtype.val hF
    have hUconfig : U = rectangleRootClusterUnion hN hM roots A := by
      exact (congrArg rectangleLabeledObservationVertexSet hobs).symm.trans
        (rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots A)
    have hcomp := rectangleRootCrossing_complement_of_clusterUnion_eq
      hN hM roots A u U hUconfig huU hseparate huCross
    have hcomp' :
        rectangleComplementRootCrossingEvent hN hM U u huU
          (embeddedConfigurationRestriction (rectangleComplementGraph hN hM U)
            G (rectangleComplementEmbedding U)
            (rectangleComplementGraph_map_le hN hM U) A) := by
      exact hcomp
    have hstate : rectangleComplementRemovedState hN hM U A ∈ T := by
      have heq := congrArg (fun X =>
        rectangleComplementRemovedState hN hM
            (rectangleLabeledObservationVertexSet X) A ∈
          rectangleObservationRemovedStateEvent hN hM roots X) hobs
      exact heq.mp (rectangleRemovedState_mem_observationRemovedStateEvent
        hN hM roots A)
    exact ⟨hcomp', hstate⟩
  have hprob (E : Set (Configuration G)) :
      rectangleBaseEventProbability hN hM q E = (p.toMeasure E).toReal := by
    simp [rectangleBaseEventProbability, PottsDiscontinuity.FK.measure,
      p, θ, G]
  have hstateSub :
      (rectangleComplementRemovedState hN hM U ⁻¹' T) ⊆ F := by
    exact rectangleObservationRemovedState_preimage_subset_fiber hN hM roots b
  have hmono : (p.toMeasure (H ∩ F)).toReal ≤ (p.toMeasure J).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (MeasureTheory.measure_mono hsub)
  have hweightedReal : (p.toMeasure J).toReal ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (rectangleComplementRemovedState hN hM U ⁻¹' T)).toReal := by
    unfold rectangleWeightedExplorationConclusion at hweighted
    change rectangleBaseEventProbability hN hM q J ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        rectangleBaseEventProbability hN hM q
          (rectangleComplementRemovedState hN hM U ⁻¹' T) at hweighted
    rw [hprob J, hprob (rectangleComplementRemovedState hN hM U ⁻¹' T)] at hweighted
    exact hweighted
  have hstateMono :
      (p.toMeasure (rectangleComplementRemovedState hN hM U ⁻¹' T)).toReal ≤
        (p.toMeasure F).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (MeasureTheory.measure_mono hstateSub)
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
    simp [rectangleFreeOneArmProbability]
  change (p.toMeasure (H ∩ F)).toReal ≤
    rectangleFreeOneArmProbability q (N / 2 - 1) * (p.toMeasure F).toReal
  calc
    (p.toMeasure (H ∩ F)).toReal ≤ (p.toMeasure J).toReal := hmono
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (rectangleComplementRemovedState hN hM U ⁻¹' T)).toReal := hweightedReal
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) * (p.toMeasure F).toReal :=
      mul_le_mul_of_nonneg_left hstateMono hρ

/-- Summing the eligible observation fibers gives the one-step product bound
for distinct rooted crossings. -/
theorem rectangleDistinctRootCrossingEvent_probability_step
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true)) (u : FaceVertex N M true)
    (hu : u.val.1.val = 0) :
    rectangleBaseEventProbability hN hM q
        (rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])) ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        rectangleBaseEventProbability hN hM q
          (rectangleDistinctRootCrossingEvent hN hM roots) := by
  classical
  let : Fintype (FaceVertex N M true) := Fintype.ofFinite _
  let : Fintype (Finset (FaceVertex N M true × Finset (FaceVertex N M true))) := inferInstance
  let : Finite (rectangleRootObservationIndex hN hM roots) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let : Fintype (rectangleRootObservationIndex hN hM roots) := Fintype.ofFinite _
  let : MeasurableSpace (rectangleRootObservationIndex hN hM roots) := ⊤
  let : MeasurableSingletonClass (rectangleRootObservationIndex hN hM roots) := inferInstance
  let G := rectangleBaseGraph hN hM
  let θ := rectangleFKParameters q
  let p := law G θ (BoundaryCondition.free ∅)
  let f := rectangleRootObservationIndexOf hN hM roots
  let S := rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])
  let T := rectangleEligibleRootObservation hN hM roots u
  let H₀ := rectangleDistinctRootCrossingEvent hN hM roots
  let Hgood := rectangleGoodRootObservation hN hM roots
  have hf : ∀ b, ∃ A ∈ {A | f A = b}, A ∈ p.support := by
    intro b
    simpa [f, p, θ, G] using
      rectangleRootObservationIndex_fiber_has_law_support hN hM q roots b
  have hFiber : ∀ b ∈ T,
      (p.toMeasure (S ∩ {A | f A = b})).toReal ≤
        rectangleFreeOneArmProbability q (N / 2 - 1) *
          (p.toMeasure {A | f A = b}).toReal := by
    intro b hb
    have hEligible : b ∈ rectangleEligibleRootObservation hN hM roots u := by
      exact hb
    rcases hEligible with ⟨_, huU⟩
    simpa [f, S] using
      rectangleDistinctRootCrossingEvent_fiber_probability_le
        hN hM q roots u hu b huU
  have hsum := pmf_joint_le_of_joint_fiber_le_on_T p f hf S T
    (rectangleFreeOneArmProbability q (N / 2 - 1)) hFiber
  have hnewSubset : S ⊆ S ∩ f ⁻¹' T := by
    intro A hA
    refine ⟨hA, ?_⟩
    have hprojection := rectangleDistinctRootCrossingEvent_append_projection
      hN hM roots u A hA
    have hgood : f A ∈ Hgood := by
      exact (rectangleDistinctRootCrossingEvent_iff_good_observation
        hN hM roots A).mp hprojection.1
    have houtside : u ∉ rectangleLabeledObservationVertexSet (f A).val := by
      intro huA
      have hUeq := rectangleLabeledObservationVertexSet_eq_rootClusterUnion
        hN hM roots A
      have huUnion : u ∈ rectangleRootClusterUnion hN hM roots A :=
        (congrArg (fun V => u ∈ V) hUeq).mp huA
      exact hprojection.2 huUnion
    change f A ∈ rectangleGoodRootObservation hN hM roots ∧
      u ∉ rectangleLabeledObservationVertexSet (f A).val
    exact ⟨hgood, houtside⟩
  have hTsub : T ⊆ Hgood := by
    intro b hb
    exact hb.1
  have hH0eq : H₀ = f ⁻¹' Hgood := by
    ext A
    exact rectangleDistinctRootCrossingEvent_iff_good_observation
      hN hM roots A
  have hprob (E : Set (Configuration G)) :
      rectangleBaseEventProbability hN hM q E = (p.toMeasure E).toReal := by
    simp [rectangleBaseEventProbability, PottsDiscontinuity.FK.measure,
      p, θ, G]
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
    simp [rectangleFreeOneArmProbability]
  calc
    rectangleBaseEventProbability hN hM q S = (p.toMeasure S).toReal := hprob S
    _ ≤ (p.toMeasure (S ∩ f ⁻¹' T)).toReal := by
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (MeasureTheory.measure_mono hnewSubset)
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (f ⁻¹' T)).toReal := hsum
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (f ⁻¹' Hgood)).toReal := by
      apply mul_le_mul_of_nonneg_left _ hρ
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (MeasureTheory.measure_mono (Set.preimage_mono hTsub))
    _ = rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure H₀).toReal := by rw [← hH0eq]
    _ = rectangleFreeOneArmProbability q (N / 2 - 1) *
        rectangleBaseEventProbability hN hM q H₀ := by rw [hprob]

private theorem mem_cons_of_mem_append {α : Type*} (u x : α) (roots : List α)
    (h : x ∈ roots ++ [u]) : x ∈ u :: roots := by
  rcases List.mem_append.mp h with hroots | hu
  · exact List.mem_cons.mpr (Or.inr hroots)
  · have hxu : x = u := List.mem_singleton.mp hu
    subst x
    exact List.mem_cons.mpr (Or.inl rfl)

private theorem mem_append_of_mem_cons {α : Type*} (u x : α) (roots : List α)
    (h : x ∈ u :: roots) : x ∈ roots ++ [u] := by
  rcases List.mem_cons.mp h with hxu | hroots
  · subst x
    exact List.mem_append.mpr (Or.inr (List.mem_singleton_self u))
  · exact List.mem_append.mpr (Or.inl hroots)

/-- The distinct-crossing event is unchanged by moving the first root to the
last position in the root list. -/
theorem rectangleDistinctRootCrossingEvent_cons_eq_append
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (u : FaceVertex N M true) :
    rectangleDistinctRootCrossingEvent hN hM (u :: roots) =
      rectangleDistinctRootCrossingEvent hN hM (roots ++ [u]) := by
  ext A
  constructor
  · rintro ⟨hcross, hnodup, hdistinct⟩
    have hparts := List.nodup_cons.mp hnodup
    have hmem : ∀ x, x ∈ roots ++ [u] → x ∈ u :: roots :=
      fun x hx => mem_cons_of_mem_append u x roots hx
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact hcross x (hmem x hx)
    · apply List.nodup_append'.2
      refine ⟨hparts.2, by simp, ?_⟩
      apply List.disjoint_iff_ne.mpr
      intro x hx y hy
      have hyu : y = u := List.mem_singleton.mp hy
      subst y
      intro hxu
      subst x
      exact hparts.1 hx
    · intro x hx y hy hxy
      exact hdistinct x (hmem x hx) y (hmem y hy) hxy
  · rintro ⟨hcross, hnodup, hdistinct⟩
    have hparts := List.nodup_append'.mp hnodup
    have hdisjoint := hparts.2.2
    have hnot : u ∉ roots := by
      intro huRoots
      have hne := (List.disjoint_iff_ne.mp hdisjoint) u huRoots u
        (List.mem_singleton_self u)
      exact hne rfl
    have hmem : ∀ x, x ∈ u :: roots → x ∈ roots ++ [u] :=
      fun x hx => mem_append_of_mem_cons u x roots hx
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact hcross x (hmem x hx)
    · exact List.nodup_cons.mpr ⟨hnot, hparts.1⟩
    · intro x hx y hy hxy
      exact hdistinct x (hmem x hx) y (hmem y hy) hxy

/-- The probability of distinct left-to-right crossings from any finite list
of left-boundary roots is at most the one-arm probability to the list length. -/
theorem rectangleDistinctRootCrossingEvent_probability_le_pow
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true))
    (hleft : ∀ u ∈ roots, u.val.1.val = 0) :
    rectangleBaseEventProbability hN hM q
        (rectangleDistinctRootCrossingEvent hN hM roots) ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) ^ roots.length := by
  classical
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
    simp [rectangleFreeOneArmProbability]
  induction roots with
  | nil =>
      simp [rectangleDistinctRootCrossingEvent, rectangleBaseEventProbability,
        PottsDiscontinuity.FK.measure]
  | cons u roots ih =>
      have hu : u.val.1.val = 0 := hleft u (by simp)
      have htail : ∀ x ∈ roots, x.val.1.val = 0 := by
        intro x hx
        exact hleft x (by simp [hx])
      have hstep := rectangleDistinctRootCrossingEvent_probability_step
        hN hM q roots u hu
      have hperm := rectangleDistinctRootCrossingEvent_cons_eq_append
        hN hM roots u
      have hprobEq :
          rectangleBaseEventProbability hN hM q
              (rectangleDistinctRootCrossingEvent hN hM (u :: roots)) =
            rectangleBaseEventProbability hN hM q
              (rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])) :=
        congrArg (rectangleBaseEventProbability hN hM q) hperm
      rw [hprobEq]
      calc
        rectangleBaseEventProbability hN hM q
            (rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])) ≤
            rectangleFreeOneArmProbability q (N / 2 - 1) *
              rectangleBaseEventProbability hN hM q
                (rectangleDistinctRootCrossingEvent hN hM roots) := hstep
        _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
              rectangleFreeOneArmProbability q (N / 2 - 1) ^ roots.length :=
          mul_le_mul_of_nonneg_left (ih htail) hρ
        _ = rectangleFreeOneArmProbability q (N / 2 - 1) ^ (roots.length + 1) := by
          rw [pow_succ]
          ring

end PottsDiscontinuity.TorusLoops
