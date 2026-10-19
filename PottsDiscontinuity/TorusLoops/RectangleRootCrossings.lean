module

public import PottsDiscontinuity.TorusLoops.RectangleTranslatedOneArm
public import PottsDiscontinuity.TorusLoops.RectangleBoxComparison

/-!
# Rooted horizontal crossings of the cut rectangle

The distinct-crossing-count event is not increasing, but a crossing from one
fixed left-boundary vertex to the right boundary is increasing. These rooted
events are the events used in the sequential exploration argument.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK
open PottsDiscontinuity.CorrLength
open PottsDiscontinuity.Zhang

variable {N M : ℕ}

private theorem actualConnected_embeddedConfigurationEmbedding
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V ↪ W) (hGH : G.map f ≤ H)
    (A : Configuration G) (u v : V)
    (h : ActualConnected G A u v) :
    ActualConnected H (embeddedConfigurationEmbedding G H f hGH A) (f u) (f v) := by
  change (openGraph H
    (subgraphConfigurationEmbedding hGH (isolatedExtensionConfigurationEquiv G f A))).Reachable
      (f u) (f v)
  rw [openGraph_subgraphConfigurationEmbedding, openGraph_isolatedExtension]
  exact (reachable_isolatedExtension_apply (openGraph G A) f u v).2 h

/-- A fixed left-boundary vertex is connected by open rectangle edges to the
right boundary. -/
def rectangleRootCrossingEvent (hN : Even N) (hM : Even M)
    (u : FaceVertex N M true) : Set (Configuration (rectangleBaseGraph hN hM)) :=
  {C | ∃ v : FaceVertex N M true, v.val.1.val + 1 = N ∧
    ActualConnected (rectangleBaseGraph hN hM) C u v}

/-- Rooted crossing is increasing in the rectangle open-edge configuration. -/
theorem rectangleRootCrossingEvent_isUpperSet (hN : Even N) (hM : Even M)
    (u : FaceVertex N M true) :
    IsUpperSet (rectangleRootCrossingEvent hN hM u) := by
  intro C D hCD hC
  rcases hC with ⟨v, hv, hconn⟩
  exact ⟨v, hv, actualConnected_mono hCD hconn⟩

private theorem rectangleFaceToRotated_square_x (u : FaceVertex N M true) :
    (u.val.1.val : ℤ) =
      (rotatedToSquareVertex (rectangleFaceToRotated u)).1 -
        (rotatedToSquareVertex (rectangleFaceToRotated u)).2 := by
  have h := congrArg (fun z : RotatedVertex => z.1.1)
    (squareToRotated_rotatedToSquare (rectangleFaceToRotated u))
  simpa [rectangleFaceToRotated, squareToRotatedVertex, rotatedToSquareVertex] using h.symm

private theorem rectangleFaceBox_horizontal_distance (hN : Even N) (hM : Even M)
    (u v : FaceVertex N M true) (hu : u.val.1.val = 0)
    (hv : v.val.1.val + 1 = N) :
    N / 2 - 1 ≤ Zhang.boxRadius
      ((rectangleFaceBoxEmbedding hN hM v).val -
        (rectangleFaceBoxEmbedding hN hM u).val) := by
  let x : LatticeVertex := (rectangleFaceBoxEmbedding hN hM u).val
  let y : LatticeVertex := (rectangleFaceBoxEmbedding hN hM v).val
  have hx : (u.val.1.val : ℤ) = x.1 - x.2 := by
    change (u.val.1.val : ℤ) =
      (rotatedToSquareVertex (rectangleFaceToRotated u)).1 -
        (rotatedToSquareVertex (rectangleFaceToRotated u)).2
    exact rectangleFaceToRotated_square_x u
  have hy : (v.val.1.val : ℤ) = y.1 - y.2 := by
    change (v.val.1.val : ℤ) =
      (rotatedToSquareVertex (rectangleFaceToRotated v)).1 -
        (rotatedToSquareVertex (rectangleFaceToRotated v)).2
    exact rectangleFaceToRotated_square_x v
  have hu' : (u.val.1.val : ℤ) = 0 := by exact_mod_cast hu
  have hv' : (v.val.1.val : ℤ) + 1 = (N : ℤ) := by exact_mod_cast hv
  have hdiff : ((N - 1 : ℕ) : ℤ) = (y.1 - x.1) - (y.2 - x.2) := by
    omega
  have htri : ((N - 1 : ℕ) : ℤ) ≤ |y.1 - x.1| + |y.2 - x.2| := by
    calc
      ((N - 1 : ℕ) : ℤ) = |((N - 1 : ℕ) : ℤ)| := by
        rw [abs_of_nonneg]
        omega
      _ = |(y.1 - x.1) - (y.2 - x.2)| := by rw [hdiff]
      _ ≤ |y.1 - x.1| + |y.2 - x.2| := by
        simpa [abs_sub_comm] using abs_sub_le (y.1 - x.1) 0 (y.2 - x.2)
  have hnat : N - 1 ≤ (y.1 - x.1).natAbs + (y.2 - x.2).natAbs := by
    have hNpos : 1 ≤ N := by omega
    have hcast : (N : ℤ) - 1 ≤
        ((y.1 - x.1).natAbs : ℤ) + ((y.2 - x.2).natAbs : ℤ) := by
      simpa [Nat.cast_sub hNpos, Nat.cast_natAbs, Int.cast_abs, Nat.cast_add] using htri
    exact_mod_cast hcast
  have hmax : (y.1 - x.1).natAbs + (y.2 - x.2).natAbs ≤
      2 * max (y.1 - x.1).natAbs (y.2 - x.2).natAbs := by omega
  obtain ⟨a, ha⟩ := hN
  have hEvenN : ∃ a, N = 2 * a := ⟨a, by omega⟩
  change N / 2 - 1 ≤ max (y.1 - x.1).natAbs (y.2 - x.2).natAbs
  simpa [x, y, boxRadius] using (show N / 2 - 1 ≤
      max (y.1 - x.1).natAbs (y.2 - x.2).natAbs by
    obtain ⟨a, ha⟩ := hEvenN
    omega)

/-- A rooted crossing in the containing-box restriction creates an actual
infinite-lattice connection from the translated root to distance at least
`N/2 - 1`. The radius loss is the square/rotated coordinate conversion. -/
theorem rectangleBoxRestriction_rootCrossing_subset_oneArm
    (hN : Even N) (hM : Even M) (u : FaceVertex N M true)
    (hu : u.val.1.val = 0)
    (B : Configuration (boxGraph (0, 0) (RectangleRotatedBoxRadius N M)))
    (hB : B ∈ rectangleBoxRestrictionEvent hN hM
      (rectangleRootCrossingEvent hN hM u)) :
    latticeConfigurationTranslate
        (-(rectangleFaceBoxEmbedding hN hM u).val)
        (boxConfiguration (0, 0) (RectangleRotatedBoxRadius N M) B) ∈
      Zhang.oneArmEvent (N / 2 - 1) := by
  let G := rectangleBaseGraph hN hM
  let H := boxGraph (0, 0) (RectangleRotatedBoxRadius N M)
  let f := rectangleFaceBoxEmbedding hN hM
  let hGH := rectangleBaseGraph_map_rectangleFaceBoxEmbedding hN hM
  let C := embeddedConfigurationRestriction G H f hGH B
  have hC : C ∈ rectangleRootCrossingEvent hN hM u := by
    simpa [C, G, H, f, hGH, rectangleBoxRestrictionEvent] using hB
  obtain ⟨v, hv, hreach⟩ := hC
  let D := embeddedConfigurationEmbedding G H f hGH C
  have hDC : D ⊆ B := by
    simpa [D, C] using embeddedConfigurationEmbedding_restriction_subset G H f hGH B
  have hreachH : ActualConnected H B (f u) (f v) := by
    apply actualConnected_mono hDC
    exact actualConnected_embeddedConfigurationEmbedding G H f hGH C u v hreach
  let g : BoxVertex (0, 0) (RectangleRotatedBoxRadius N M) ↪ LatticeVertex :=
    (boxGraphEmbedding (0, 0) (RectangleRotatedBoxRadius N M)).toEmbedding
  have hHG : H.map g ≤ squareLattice := by
    intro a b hab
    rw [SimpleGraph.map_adj] at hab
    rcases hab with ⟨a', b', hab', rfl, rfl⟩
    exact (boxGraphEmbedding (0, 0) (RectangleRotatedBoxRadius N M)).map_rel_iff.mpr hab'
  have hreachZ : ActualConnected squareLattice
      (embeddedConfigurationEmbedding H squareLattice g hHG B) (g (f u)) (g (f v)) :=
    actualConnected_embeddedConfigurationEmbedding H squareLattice g hHG B (f u) (f v) hreachH
  let F : Configuration squareLattice :=
    embeddedConfigurationEmbedding H squareLattice g hHG B
  have hEdge : embeddedEdgeEmbedding H squareLattice g hHG =
      boxEdgeEmbedding (0, 0) (RectangleRotatedBoxRadius N M) := by
    apply Function.Embedding.ext
    intro e
    apply Subtype.ext
    rfl
  have hF : F = B.map (boxEdgeEmbedding (0, 0) (RectangleRotatedBoxRadius N M)) := by
    unfold F
    rw [embeddedConfigurationEmbedding_eq_map]
    rw [hEdge]
  have hopen : boxConfiguration (0, 0) (RectangleRotatedBoxRadius N M) B ∈
      LatticeConfiguration.allOpen F := by
    intro e he
    rw [hF] at he
    exact (boxConfiguration_open_iff (0, 0) (RectangleRotatedBoxRadius N M) B e).2 he
  have hconn : boxConfiguration (0, 0) (RectangleRotatedBoxRadius N M) B ∈
      connectionEvent (g (f u)) (g (f v)) := ⟨F, hreachZ, hopen⟩
  let x : LatticeVertex := g (f u)
  let y : LatticeVertex := g (f v)
  have htranslated : latticeConfigurationTranslate (-x)
      (boxConfiguration (0, 0) (RectangleRotatedBoxRadius N M) B) ∈
        connectionEvent (0, 0) (y - x) := by
    have ht := (connectionEvent_translation (-x) x y
      (boxConfiguration (0, 0) (RectangleRotatedBoxRadius N M) B)).mpr hconn
    convert ht using 1; simp [x, y, latticeTranslate, Prod.sub_def]; ring
  have hreachInf := (connectionEvent_iff_rcInfiniteReachable (0, 0) (y - x)
      (latticeConfigurationTranslate (-x)
        (boxConfiguration (0, 0) (RectangleRotatedBoxRadius N M) B))).mp htranslated
  have hx : x = (rectangleFaceBoxEmbedding hN hM u).val := rfl
  have hy : y = (rectangleFaceBoxEmbedding hN hM v).val := rfl
  have hdist := rectangleFaceBox_horizontal_distance hN hM u v hu hv
  refine ⟨y - x, ?_, hreachInf⟩
  simpa [x, y, hx, hy] using hdist

/-- A rooted crossing under the free rectangle law is bounded by the free
infinite-volume one-arm probability at the square radius forced by the
rotated-rectangle displacement. -/
theorem rectangleFKProbability_rootCrossing_le_freeOneArm
    (hN : Even N) (hM : Even M) (u : FaceVertex N M true)
    (hu : u.val.1.val = 0) (q : Set.Ici (1 : ℝ)) :
    rectangleFKEventProbability hN hM q (rectangleRootCrossingEvent hN hM u) ≤
      (((Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique
        (rectangleFKParameters q))) (oneArmEvent (N / 2 - 1)) : NNReal) : ℝ) := by
  let θ := rectangleFKParameters q
  let R := RectangleRotatedBoxRadius N M
  let H := boxGraph (0, 0) R
  let E := translatedOneArmEvent (rectangleFaceBoxEmbedding hN hM u).val (N / 2 - 1)
  let S : Set (Configuration H) := {B | boxConfiguration (0, 0) R B ∈ E}
  have hE : MeasurableSet E := by
    exact (measurableSet_oneArmEvent (N / 2 - 1)).preimage
      (latticeConfigurationTranslationHomeomorph
        (-(rectangleFaceBoxEmbedding hN hM u).val)).continuous.measurable
  have hsubset :
      rectangleBoxRestrictionEvent hN hM (rectangleRootCrossingEvent hN hM u) ⊆ S := by
    intro B hB
    exact rectangleBoxRestriction_rootCrossing_subset_oneArm hN hM u hu B hB
  have hboxEvent :
      measure H θ (BoundaryCondition.free ∅) S =
        (boxProbabilityMeasure θ (0, 0) R : Measure LatticeConfiguration) E := by
    symm
    change ((law H θ (BoundaryCondition.free ∅)).map (boxConfiguration (0, 0) R)).toMeasure E = _
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hE]
    rfl
  have hprobCompare :=
    boxProbabilityMeasure_translatedOneArm_le_freeBoxLimit θ R
      (rectangleFaceBoxEmbedding hN hM u).val (N / 2 - 1)
  rw [freeBoxLimit_translatedOneArm_probability_eq θ
    (rectangleFaceBoxEmbedding hN hM u).val (N / 2 - 1)] at hprobCompare
  have hrealBox : (measure H θ (BoundaryCondition.free ∅) S).toReal =
      (((boxProbabilityMeasure θ (0, 0) R E : NNReal) : ℝ)) := by
    rw [hboxEvent, ← Measure.real_def]
    exact ProbabilityMeasure.measureReal_eq_coe_coeFn
      (boxProbabilityMeasure θ (0, 0) R) E
  have hmeasure :
      measure H θ (BoundaryCondition.free ∅)
          (rectangleBoxRestrictionEvent hN hM (rectangleRootCrossingEvent hN hM u)) ≤
        measure H θ (BoundaryCondition.free ∅) S :=
    MeasureTheory.measure_mono hsubset
  have hrealMono :
      (measure H θ (BoundaryCondition.free ∅)
        (rectangleBoxRestrictionEvent hN hM (rectangleRootCrossingEvent hN hM u))).toReal ≤
        (measure H θ (BoundaryCondition.free ∅) S).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
  have hrect := rectangleFKEventProbability_le_rectangleBoxRestriction
    hN hM q (rectangleRootCrossingEvent hN hM u)
    (rectangleRootCrossingEvent_isUpperSet hN hM u)
  have hleft : rectangleFKEventProbability hN hM q
      (rectangleRootCrossingEvent hN hM u) ≤
        (((boxProbabilityMeasure θ (0, 0) R E : NNReal) : ℝ)) := by
    calc
      _ ≤ (measure H θ (BoundaryCondition.free ∅)
          (rectangleBoxRestrictionEvent hN hM (rectangleRootCrossingEvent hN hM u))).toReal := hrect
      _ ≤ (measure H θ (BoundaryCondition.free ∅) S).toReal := hrealMono
      _ = _ := hrealBox
  have hprobCompareR :
      (((boxProbabilityMeasure θ (0, 0) R E : NNReal) : ℝ)) ≤
        (((Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique θ)
          (oneArmEvent (N / 2 - 1)) : NNReal) : ℝ)) :=
    NNReal.coe_le_coe.mpr hprobCompare
  exact hleft.trans hprobCompareR

end PottsDiscontinuity.TorusLoops
