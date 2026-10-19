module

public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.FK.SubgraphComparison
public import PottsDiscontinuity.TorusLoops.RectangleLaw
public import PottsDiscontinuity.TorusLoops.RectangleRotatedEmbedding

/-!
# Free FK comparison from the cut rectangle to a rotated square box

Every increasing event of the cut rectangle has probability at most that of
its exact restriction event in a containing square box.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK
open PottsDiscontinuity.CorrLength

noncomputable section

variable {N M : ℕ}

local instance rectangleBoxComparisonGenericEdgeFintype
    {V : Type*} [Finite V] {G : SimpleGraph V} : Fintype G.edgeSet :=
  Fintype.ofFinite _

local instance rectangleBoxComparisonGenericEdgeDecidableEq
    {V : Type*} [Finite V] {G : SimpleGraph V} : DecidableEq G.edgeSet :=
  Classical.decEq _

local instance rectangleBoxComparisonRectangleEdgeFintype
    (hN : Even N) (hM : Even M) :
    Fintype (rectangleBaseGraph hN hM).edgeSet := Fintype.ofFinite _

local instance rectangleBoxComparisonRectangleEdgeDecidableEq
    (hN : Even N) (hM : Even M) :
    DecidableEq (rectangleBaseGraph hN hM).edgeSet := Classical.decEq _

local instance rectangleBoxComparisonBoxEdgeFintype (N M : ℕ) :
    Fintype (boxGraph (0, 0) (RectangleRotatedBoxRadius N M)).edgeSet :=
  Fintype.ofFinite _

local instance rectangleBoxComparisonBoxEdgeDecidableEq (N M : ℕ) :
    DecidableEq (boxGraph (0, 0) (RectangleRotatedBoxRadius N M)).edgeSet :=
  Classical.decEq _

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

/-- The event on the containing box that its exact rectangle restriction lies
in `E`. -/
def rectangleBoxRestrictionEvent (hN : Even N) (hM : Even M)
    (E : Set (Configuration (rectangleBaseGraph hN hM))) :
    Set (Configuration (boxGraph (0, 0) (RectangleRotatedBoxRadius N M))) :=
  {B | embeddedConfigurationRestriction (rectangleBaseGraph hN hM)
    (boxGraph (0, 0) (RectangleRotatedBoxRadius N M))
    (rectangleFaceBoxEmbedding hN hM)
    (rectangleBaseGraph_map_rectangleFaceBoxEmbedding hN hM) B ∈ E}

/-- Increasing free FK events on the cut rectangle are dominated by the
corresponding event in the containing square box. -/
theorem rectangleFKEventProbability_le_rectangleBoxRestriction
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (Configuration (rectangleBaseGraph hN hM)))
    (hE : IsUpperSet E) :
    rectangleFKEventProbability hN hM q E ≤
      (measure (boxGraph (0, 0) (RectangleRotatedBoxRadius N M))
        (rectangleFKParameters q) (BoundaryCondition.free ∅)
        (rectangleBoxRestrictionEvent hN hM E)).toReal := by
  let G := rectangleBaseGraph hN hM
  let H := boxGraph (0, 0) (RectangleRotatedBoxRadius N M)
  let f := rectangleFaceBoxEmbedding hN hM
  let hGH := rectangleBaseGraph_map_rectangleFaceBoxEmbedding hN hM
  let R := rectangleBoxRestrictionEvent hN hM E
  let ind := E.indicator (fun _ => (1 : ℝ))
  have hind0 : ∀ A, 0 ≤ ind A := by
    intro A
    by_cases h : A ∈ E <;> simp [ind, h]
  have hind : Monotone ind := by
    intro A B hAB
    by_cases hA : A ∈ E
    · have hB := hE hAB hA
      simp [ind, hA, hB]
    · simp only [ind, Set.indicator_of_notMem hA]
      exact hind0 B
  have hcmp := embedded_free_marginal_comparison G H f hGH
    (rectangleFKParameters q) ∅ ∅ ind hind0 hind
  have hmap : FiniteProbability.expectation
      ((law H (rectangleFKParameters q) (BoundaryCondition.free ∅)).map
        (embeddedConfigurationRestriction G H f hGH)) ind =
      (measure H (rectangleFKParameters q) (BoundaryCondition.free ∅) R).toReal := by
    calc
      FiniteProbability.expectation
          ((law H (rectangleFKParameters q) (BoundaryCondition.free ∅)).map
            (embeddedConfigurationRestriction G H f hGH)) ind =
          FiniteProbability.expectation (law H (rectangleFKParameters q)
            (BoundaryCondition.free ∅))
            (fun B => ind (embeddedConfigurationRestriction G H f hGH B)) :=
              FiniteProbability.expectation_map _ _ _
      _ = FiniteProbability.expectation (law H (rectangleFKParameters q)
            (BoundaryCondition.free ∅)) (R.indicator (fun _ => (1 : ℝ))) := by
              apply congrArg (FiniteProbability.expectation
                (law H (rectangleFKParameters q) (BoundaryCondition.free ∅)))
              funext B
              by_cases h : B ∈ rectangleBoxRestrictionEvent hN hM E
              · have hE' : embeddedConfigurationRestriction G H f hGH B ∈ E := by
                  simpa [G, H, f, hGH, rectangleBoxRestrictionEvent] using h
                simp [ind, R, rectangleBoxRestrictionEvent, G, H, f,
                  Set.indicator, hE']
              · have hE' : embeddedConfigurationRestriction G H f hGH B ∉ E := by
                  intro hmem
                  apply h
                  simpa [G, H, f, hGH, rectangleBoxRestrictionEvent] using hmem
                simp [ind, R, rectangleBoxRestrictionEvent, G, H, f,
                  Set.indicator, hE']
      _ = (measure H (rectangleFKParameters q) (BoundaryCondition.free ∅) R).toReal :=
          (fkLaw_measure_toReal_eq_expectation _ _ _).symm
  have hleft : rectangleFKEventProbability hN hM q E =
      FiniteProbability.expectation (law G (rectangleFKParameters q)
        (BoundaryCondition.free ∅)) ind := by
    calc
      rectangleFKEventProbability hN hM q E =
          (measure G (rectangleFKParameters q) (BoundaryCondition.free ∅) E).toReal :=
        rectangleFKEventProbability_eq_measure hN hM q E
      _ = FiniteProbability.expectation (law G (rectangleFKParameters q)
          (BoundaryCondition.free ∅)) ind :=
        fkLaw_measure_toReal_eq_expectation _ _ _
  rw [hleft]
  exact hcmp.trans_eq hmap

end
end PottsDiscontinuity.TorusLoops
