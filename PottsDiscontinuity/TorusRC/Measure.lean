module

public import PottsDiscontinuity.Torus.DiamondGraph
public import PottsDiscontinuity.FK.Probability

/-!
# The critical random-cluster probability on the indexed diamond torus

Normalize the actual indexed-edge weight `torusRCWeight` of `Torus/DiamondGraph.lean`,
retaining loops and parallel edges
for small periods. No identification with a simple-graph configuration space
is required to define this law.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

theorem criticalParameter_pos (q : Set.Ici (1 : ℝ)) :
    0 < (rcCriticalParameter q).val := by
  have hq : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
  exact div_pos (Real.sqrt_pos.2 hq) (by positivity)

theorem criticalParameter_lt_one (q : Set.Ici (1 : ℝ)) :
    (rcCriticalParameter q).val < 1 := by
  change Real.sqrt q.val / (1 + Real.sqrt q.val) < 1
  exact (div_lt_one (by positivity)).2 (by linarith)

theorem torusRCWeight_pos (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    0 < torusRCWeight hN hM q A := by
  unfold torusRCWeight
  exact mul_pos (mul_pos (pow_pos (criticalParameter_pos q) _)
    (pow_pos (sub_pos.2 (criticalParameter_lt_one q)) _))
    (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _)

/-- Sum over all indexed configurations, including isolated vertices in the weight. -/
noncomputable def torusRCPartition (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : ℝ :=
  FK.FiniteProbability.partition (torusRCWeight hN hM q)

theorem torusRCPartition_pos (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : 0 < torusRCPartition hN hM q :=
  FK.FiniteProbability.partition_pos _ (torusRCWeight_pos hN hM q)

/-- The normalized mass of an indexed configuration. -/
noncomputable def torusRCMass (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) : ℝ :=
  torusRCWeight hN hM q A / torusRCPartition hN hM q

theorem torusRCMass_pos (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    0 < torusRCMass hN hM q A :=
  div_pos (torusRCWeight_pos hN hM q A) (torusRCPartition_pos hN hM q)

theorem sum_torusRCMass (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : ∑ A, torusRCMass hN hM q A = 1 :=
  FK.FiniteProbability.sum_probability _ (torusRCWeight_pos hN hM q)

/-- The probability mass function of the critical indexed diamond-torus law. -/
noncomputable def torusRCPMF (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : PMF (RCConfig N M) :=
  FK.FiniteProbability.pmf _ (torusRCWeight_pos hN hM q)

theorem torusRCPMF_apply (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusRCPMF hN hM q A = ENNReal.ofReal (torusRCMass hN hM q A) := rfl

/-- The critical torus RC probability measure, with the product discrete sigma-field. -/
noncomputable def torusRCMeasure (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : Measure (RCConfig N M) :=
  (torusRCPMF hN hM q).toMeasure

instance torusRCMeasure_isProbabilityMeasure (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : IsProbabilityMeasure (torusRCMeasure hN hM q) := by
  unfold torusRCMeasure
  infer_instance

/-- Real-valued event probability under the critical torus RC measure. -/
noncomputable def torusRCProbability (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) : ℝ :=
  (torusRCMeasure hN hM q).real E

theorem torusRCMeasure_singleton (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusRCMeasure hN hM q {A} = ENNReal.ofReal (torusRCMass hN hM q A) := by
  exact (PMF.toMeasure_apply_singleton _ A (measurableSet_singleton A)).trans
    (torusRCPMF_apply hN hM q A)

theorem torusRCProbability_singleton (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusRCProbability hN hM q {A} = torusRCMass hN hM q A := by
  unfold torusRCProbability Measure.real
  rw [torusRCMeasure_singleton, ENNReal.toReal_ofReal (torusRCMass_pos hN hM q A).le]

end PottsDiscontinuity.TorusRC
