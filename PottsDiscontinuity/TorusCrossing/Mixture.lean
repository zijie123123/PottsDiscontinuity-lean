module

public import PottsDiscontinuity.FK.EmbeddedMarginalLaw
public import PottsDiscontinuity.TorusCrossing.Fiber
public import PottsDiscontinuity.TorusCrossing.TorusDict
public import PottsDiscontinuity.TorusRC.MeasureBridge

/-!
# Mixture lifting from an embedded board to the ambient graph

The law of the restriction of the FK measure of `H` to an embedded subgraph `G` is a mixture,
over the state of the remaining edges, of FK laws of `G` with various boundary conditions.  An
inequality between the probabilities of two events of `G` valid for *every* boundary condition
therefore transfers to the ambient measure.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

theorem bind_toMeasure_real {α β : Type*} [Fintype α] [MeasurableSpace β] (p : PMF α)
    (f : α → PMF β) (S : Set β) (hS : MeasurableSet S) :
    ((p.bind f).toMeasure S).toReal = ∑ a, (p a).toReal * ((f a).toMeasure S).toReal := by
  rw [PMF.toMeasure_bind_apply _ _ _ hS, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top p a) (MeasureTheory.measure_ne_top _ _)

attribute [local instance] FK.configurationMeasurableSpace

theorem embedded_mixture_lower {V W : Type*} [Finite V] [Finite W] (G : SimpleGraph V)
    (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H) (θ : FK.Parameters)
    (ξ : FK.BoundaryCondition W) (S T : Set (FK.Configuration G)) (κ : ℝ)
    (h : ∀ η : FK.BoundaryCondition V,
      κ * (FK.measure G θ η S).toReal ≤ (FK.measure G θ η T).toReal) :
    κ * (FK.measure H θ ξ {C | FK.embeddedConfigurationRestriction G H f hGH C ∈ S}).toReal ≤
      (FK.measure H θ ξ {C | FK.embeddedConfigurationRestriction G H f hGH C ∈ T}).toReal := by
  let : Fintype H.edgeSet := Fintype.ofFinite _
  let : Fintype G.edgeSet := Fintype.ofFinite _
  let : DecidableEq H.edgeSet := Classical.decEq _
  let : Fintype (FK.RemovedConfiguration H (FK.subgraphRemovedEdges (G.map f) H)) :=
    Fintype.ofFinite _
  have hmix := FK.law_embeddedConfigurationRestriction_eq_bind_frozenMarginal G H f hGH θ ξ
  have key : ∀ U : Set (FK.Configuration G),
      (FK.measure H θ ξ {C | FK.embeddedConfigurationRestriction G H f hGH C ∈ U}).toReal =
        ∑ K, ((FK.frozenMarginalLaw θ ξ (FK.subgraphRemovedEdges (G.map f) H)) K).toReal *
          (FK.measure G θ (FK.isolatedExtensionPullbackBoundary f (FK.frozenBoundary ξ K.val)) U).toReal := by
    intro U
    have h1 : FK.measure H θ ξ {C | FK.embeddedConfigurationRestriction G H f hGH C ∈ U} =
        ((PMF.map (FK.embeddedConfigurationRestriction G H f hGH) (FK.law H θ ξ)).toMeasure U) := by
      rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top]
      rfl
    rw [h1, hmix, bind_toMeasure_real _ _ _ MeasurableSpace.measurableSet_top]
    rfl
  rw [key S, key T, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro K _
  rw [← mul_assoc, mul_comm κ, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h _) ENNReal.toReal_nonneg

open PottsDiscontinuity.TorusRC Torus

theorem torus_event_image {N M : ℕ} (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (Q : Rect) (hQN : Q.w + 1 ≤ N) (hQM : Q.h + 1 ≤ M)
    (P : Finset Cell → Prop) :
    torusRCConfigurationEquiv hN hM hN4 hM4 '' {A | P (boardOf Q hNp hMp A)} =
      {C | P (openMedials Q.pData (FK.embeddedConfigurationRestriction Q.pG (fullDiamondGraph hN hM)
        (iota Q hN hM hNp hMp hQN hQM) (iota_le Q hN hM hNp hMp hQN hQM) C))} := by
  ext C
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨A, hA, rfl⟩
    rwa [openMedials_restr_torus Q hN hM hNp hMp hN4 hM4 hQN hQM A]
  · intro hC
    obtain ⟨A, rfl⟩ := (torusRCConfigurationEquiv hN hM hN4 hM4).surjective C
    refine ⟨A, ?_, rfl⟩
    rwa [openMedials_restr_torus Q hN hM hNp hMp hN4 hM4 hQN hQM A] at hC

/-- **Torus-level bound**: the probability of the crossing event is at least `κ` times the
probability of the two barriers. -/
theorem torus_bl {N M : ℕ} (q : Set.Ici (1 : ℝ)) (hN : Even N) (hM : Even M) (hNp : 0 < N)
    (hMp : 0 < M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (Q : Rect) {bB bT : ℕ} (hg : Q.Geo bB bT)
    (hQN : Q.w + 1 ≤ N) (hQM : Q.h + 1 ≤ M) :
    (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal *
      torusRCProbability hN hM q {A | Q.barAll bB bT (boardOf Q hNp hMp A)} ≤
    torusRCProbability hN hM q {A | Q.crossEv bB bT (boardOf Q hNp hMp A)} := by
  rw [torusRCProbability_eq_fk_image hN hM hN4 hM4 q,
    torusRCProbability_eq_fk_image hN hM hN4 hM4 q,
    torus_event_image hN hM hNp hMp hN4 hM4 Q hQN hQM,
    torus_event_image hN hM hNp hMp hN4 hM4 Q hQN hQM]
  have := embedded_mixture_lower Q.pG (fullDiamondGraph hN hM) (iota Q hN hM hNp hMp hQN hQM)
    (iota_le Q hN hM hNp hMp hQN hQM) (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅)
    {C' | Q.barAll bB bT (openMedials Q.pData C')} {C' | Q.crossEv bB bT (openMedials Q.pData C')}
    (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal
    (fun η => Rect.board_bl q hg η)
  exact this

end PottsDiscontinuity.TorusCrossing
