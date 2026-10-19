module

public import PottsDiscontinuity.TorusLoops.LoopTailRectangleFK
public import PottsDiscontinuity.TorusLoops.RectangleExplorationProductBound

/-!
# Union bound over disjoint horizontal crossings

The crossing count is covered by root-set events. Each fixed root set is
estimated by the exploration product bound, and the number of possible root
sets is at most exponential in the height of the rectangle.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK
open PottsDiscontinuity.Zhang

open scoped Classical

variable {N M : ℕ}

noncomputable section

local instance rectangleUnionEdgeFintype (hN : Even N) (hM : Even M) :
    Fintype (rectangleBaseGraph hN hM).edgeSet := Fintype.ofFinite _

local instance rectangleUnionEdgeDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (rectangleBaseGraph hN hM).edgeSet := Classical.decEq _

/-- Left-boundary face vertices of the cut rectangle. -/
abbrev RectangleLeftRoot (N M : ℕ) :=
  {u : FaceVertex N M true // u.val.1.val = 0}

/-- The distinct-root crossing event indexed by a finite set of left roots. -/
def rectangleLeftRootSetEvent (hN : Even N) (hM : Even M)
    (S : Finset (RectangleLeftRoot N M)) :
    Set (Configuration (rectangleBaseGraph hN hM)) :=
  rectangleDistinctRootCrossingEvent hN hM (S.toList.map Subtype.val)

private theorem rectangleCutGraph_eq_fullDiamondGraph_closedOnSeams
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    rectangleOpenGraph hN hM A = diamondOpenGraph hN hM true A := by
  ext u w
  rw [rectangleOpenGraph, diamondOpenGraph, SimpleGraph.fromEdgeSet_adj,
    SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨v, hv, _, _, hp⟩, hne⟩
    exact ⟨⟨v, hv, hp⟩, hne⟩
  · rintro ⟨⟨v, hv, hp⟩, hne⟩
    have hx : v.1.val ≠ 0 := by
      intro hz
      rw [hclosed v (Or.inl hz)] at hv
      contradiction
    have hy : v.2.val ≠ 0 := by
      intro hz
      rw [hclosed v (Or.inr hz)] at hv
      contradiction
    exact ⟨⟨v, hv, hx, hy, hp⟩, hne⟩

theorem rectangleFKCrossingEvent_exists_rootSet
    (hN : Even N) (hM : Even M)
    (k : ℕ) (C : Configuration (rectangleBaseGraph hN hM))
    (hC : C ∈ rectangleFKCrossingEvent hN hM k) :
    ∃ S : Finset (RectangleLeftRoot N M), S.card = k ∧
      C ∈ rectangleLeftRootSetEvent hN hM S := by
  classical
  let A := rectangleRCConfigOfConfiguration hN hM C
  let R := rectangleOpenGraph hN hM A
  let K := rectangleCrossingComponents hN hM A
  have hK : k ≤ K.card := hC
  obtain ⟨T, hTK, hTcard⟩ := Finset.exists_subset_card_eq hK
  have hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false := by
    intro v hv
    exact rectangleRCConfigOfConfiguration_closedOnSeams hN hM C v hv
  have hgraph : R = FK.openGraph (rectangleBaseGraph hN hM) C := by
    have hcutDiamond := rectangleCutGraph_eq_fullDiamondGraph_closedOnSeams
      hN hM A hclosed
    have hconfig := rectangleConfigurationOfRC_rectangleRCConfigOfConfiguration
      hN hM C
    have hFKDiamond :=
      PottsDiscontinuity.TorusLoops.rectangleOpenGraph_eq_diamondOpenGraph_closedOnSeams
        hN hM A hclosed
    change rectangleOpenGraph hN hM A =
      FK.openGraph (rectangleBaseGraph hN hM) C
    rw [hcutDiamond, ← hconfig]
    exact hFKDiamond.symm
  let witness : ∀ c : R.ConnectedComponent, c ∈ T →
      ∃ x : RectangleLeftRoot N M, ∃ y : FaceVertex N M true,
        y.val.1.val + 1 = N ∧ R.connectedComponentMk x.val = c ∧ R.Reachable x.val y := by
    intro c hc
    have hcK : c ∈ K := hTK hc
    rcases Finset.mem_filter.mp hcK with ⟨_, x, y, hx, hy, hxc, hreach⟩
    exact ⟨⟨x, hx⟩, y, hy, hxc, hreach⟩
  let chosen : ∀ c : R.ConnectedComponent, c ∈ T → RectangleLeftRoot N M :=
    fun c hc => Classical.choose (witness c hc)
  have chosen_data : ∀ c (hc : c ∈ T),
      ∃ y : FaceVertex N M true, y.val.1.val + 1 = N ∧
        R.connectedComponentMk (chosen c hc).val = c ∧
          R.Reachable (chosen c hc).val y := by
    intro c hc
    exact Classical.choose_spec (witness c hc)
  let S : Finset (RectangleLeftRoot N M) :=
    T.attach.image fun c => chosen c.val c.property
  have hchosen_inj : ∀ a ∈ T.attach, ∀ b ∈ T.attach,
      chosen a.val a.property = chosen b.val b.property → a = b := by
    intro a ha b hb hab
    apply Subtype.ext
    have haData := chosen_data a.val a.property
    have hbData := chosen_data b.val b.property
    have hca := (Classical.choose_spec haData).2.1
    have hcb := (Classical.choose_spec hbData).2.1
    have heq : a.val = b.val := by
      calc
        a.val = R.connectedComponentMk (chosen a.val a.property).val := hca.symm
        _ = R.connectedComponentMk (chosen b.val b.property).val := by rw [hab]
        _ = b.val := hcb
    exact heq
  have hScard : S.card = k := by
    dsimp [S]
    rw [Finset.card_image_iff.mpr hchosen_inj, Finset.card_attach, hTcard]
  refine ⟨S, hScard, ?_⟩
  have hnodup : (S.toList.map Subtype.val).Nodup := by
    apply List.Nodup.map
    · intro x y hxy
      exact Subtype.ext hxy
    · exact Finset.nodup_toList S
  have hallcross : ∀ x ∈ S.toList.map Subtype.val,
      C ∈ rectangleRootCrossingEvent hN hM x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨xr, hxr, rfl⟩
    have hxS : xr ∈ S := by simpa using hxr
    rcases Finset.mem_image.mp hxS with ⟨c, hc, hcx⟩
    have hd := chosen_data c.val c.property
    let y := Classical.choose hd
    have hdSpec := Classical.choose_spec hd
    have hy : y.val.1.val + 1 = N := hdSpec.1
    have hreach := hdSpec.2.2
    refine ⟨y, hy, ?_⟩
    change (FK.openGraph (rectangleBaseGraph hN hM) C).Reachable
      (↑xr) y
    exact hgraph ▸ (hcx ▸ hreach)
  have hdistinct : ∀ x ∈ S.toList.map Subtype.val,
      ∀ y ∈ S.toList.map Subtype.val, x ≠ y →
        ¬ ActualConnected (rectangleBaseGraph hN hM) C x y := by
    intro x hx y hy hxy hconn
    rcases List.mem_map.mp hx with ⟨xr, hxr, rfl⟩
    have hxS : xr ∈ S := by simpa using hxr
    rcases Finset.mem_image.mp hxS with ⟨c, hc, hcx⟩
    rcases List.mem_map.mp hy with ⟨yr, hyr, rfl⟩
    have hyS : yr ∈ S := by simpa using hyr
    rcases Finset.mem_image.mp hyS with ⟨d, hd, hdy⟩
    have hcxdata := chosen_data c.val c.property
    have hdydata := chosen_data d.val d.property
    have hcc := (Classical.choose_spec hcxdata).2.1
    have hdd := (Classical.choose_spec hdydata).2.1
    have hconn' :
        (FK.openGraph (rectangleBaseGraph hN hM) C).Reachable
          (chosen c.val c.property).val (chosen d.val d.property).val := by
      change (FK.openGraph (rectangleBaseGraph hN hM) C).Reachable
        (↑xr) (↑yr) at hconn
      rw [← hcx, ← hdy] at hconn
      exact hconn
    have hreach : R.Reachable (chosen c.val c.property).val
        (chosen d.val d.property).val := hgraph.symm ▸ hconn'
    have heq : c.val = d.val := by
      calc
        c.val = R.connectedComponentMk (chosen c.val c.property).val := hcc.symm
        _ = R.connectedComponentMk (chosen d.val d.property).val :=
          SimpleGraph.ConnectedComponent.sound hreach
        _ = d.val := hdd
    have hcd : c = d := Subtype.ext heq
    subst d
    apply hxy
    exact congrArg Subtype.val (hcx.symm.trans hdy)
  exact ⟨hallcross, hnodup, hdistinct⟩

/-- There are at most `M` choices for a left-boundary face root. -/
theorem rectangleLeftRoot_card_le (N M : ℕ) :
    Fintype.card (RectangleLeftRoot N M) ≤ M := by
  classical
  let f : RectangleLeftRoot N M → Fin M := fun u => u.val.val.2
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact a.property.trans b.property.symm
    · exact hab
  calc
    Fintype.card (RectangleLeftRoot N M) ≤ Fintype.card (Fin M) :=
      Fintype.card_le_of_injective f hf
    _ = M := Fintype.card_fin M

private theorem rectangleFKEventProbability_eq_measure
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (Configuration (rectangleBaseGraph hN hM))) :
    rectangleFKEventProbability hN hM q E =
      (measure (rectangleBaseGraph hN hM) (rectangleFKParameters q)
        (BoundaryCondition.free ∅) E).toReal := by
  rw [measure_toReal_eq_indicator_sum]
  unfold rectangleFKEventProbability rectangleFKEventWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro C hC
  by_cases h : C ∈ E <;> simp [Set.indicator, h, configurationProbability,
    mul_comm]

/-- The free-rectangle probability of at least `k` horizontal crossing
components is at most the number of left-root sets times the exploration
product bound. -/
theorem rectangleFKCrossingEvent_probability_le_rootUnion
    (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (k : ℕ) :
    rectangleFKEventProbability hN hM q (rectangleFKCrossingEvent hN hM k) ≤
      (2 : ℝ) ^ M *
        rectangleFreeOneArmProbability q (N / 2 - 1) ^ k := by
  classical
  let Left := RectangleLeftRoot N M
  let I := {S : Finset Left // S.card = k}
  let event : I → Set (Configuration (rectangleBaseGraph hN hM)) :=
    fun S => rectangleLeftRootSetEvent hN hM S.val
  let μ := measure (rectangleBaseGraph hN hM) (rectangleFKParameters q)
    (BoundaryCondition.free ∅)
  let ρ := rectangleFreeOneArmProbability q (N / 2 - 1)
  have hcardLeft : Fintype.card Left ≤ M := rectangleLeftRoot_card_le N M
  have hcardI : Fintype.card I ≤ 2 ^ M := by
    calc
      Fintype.card I ≤ Fintype.card (Finset Left) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = 2 ^ Fintype.card Left := Fintype.card_finset
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) hcardLeft
  have hsubset : rectangleFKCrossingEvent hN hM k ⊆ ⋃ S : I, event S := by
    intro C hC
    obtain ⟨S, hSk, hCS⟩ :=
      rectangleFKCrossingEvent_exists_rootSet hN hM k C hC
    exact Set.mem_iUnion.mpr ⟨⟨S, hSk⟩, hCS⟩
  have hprobS (S : I) : rectangleBaseEventProbability hN hM q (event S) ≤ ρ ^ k := by
    let roots := S.val.toList.map Subtype.val
    have hleft : ∀ u ∈ roots, u.val.1.val = 0 := by
      intro u hu
      rcases List.mem_map.mp hu with ⟨r, hr, rfl⟩
      exact r.property
    have hprod := rectangleDistinctRootCrossingEvent_probability_le_pow
      hN hM q roots hleft
    have hlen : roots.length = k := by
      simp [roots, S.property]
    simpa [event, rectangleLeftRootSetEvent, roots, hlen, ρ] using hprod
  have hUnionReal : μ.real (rectangleFKCrossingEvent hN hM k) ≤
      ∑ S : I, μ.real (event S) := by
    calc
      μ.real (rectangleFKCrossingEvent hN hM k) ≤
          μ.real (⋃ S : I, event S) := measureReal_mono hsubset
      _ ≤ ∑ S : I, μ.real (event S) := measureReal_iUnion_fintype_le event
  have hsum : (∑ S : I, μ.real (event S)) ≤
      (Fintype.card I : ℝ) * ρ ^ k := by
    calc
      (∑ S : I, μ.real (event S)) ≤ ∑ _S : I, ρ ^ k :=
        Finset.sum_le_sum fun S _ => by
          simpa [μ, Measure.real, rectangleBaseEventProbability] using hprobS S
      _ = (Fintype.card I : ℝ) * ρ ^ k := by simp
  have hcardR : (Fintype.card I : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast hcardI
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    unfold rectangleFreeOneArmProbability
    exact NNReal.coe_nonneg _
  rw [rectangleFKEventProbability_eq_measure hN hM q]
  simpa [μ, Measure.real] using hUnionReal.trans (hsum.trans
    (mul_le_mul_of_nonneg_right hcardR (pow_nonneg hρ k)))

end

end PottsDiscontinuity.TorusLoops
