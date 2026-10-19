module

public import PottsDiscontinuity.TorusRC.SelfDualTilt

/-! # Comparing the self-dual tilt with the standard torus law -/

@[expose] public section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

private theorem tiltWeight_pos (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    0 < torusRCTiltWeight hN hM q A := by
  rw [torusRCTiltWeight_eq_standard_div_net]
  exact div_pos (torusRCWeight_pos hN hM q A)
    (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _)

/-- The self-dual tilted partition function on the indexed torus. -/
noncomputable def torusRCTiltPartition (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : ℝ := ∑ A, torusRCTiltWeight hN hM q A

theorem torusRCTiltPartition_pos (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : 0 < torusRCTiltPartition hN hM q := by
  unfold torusRCTiltPartition
  exact Finset.sum_pos (fun A _ => tiltWeight_pos hN hM q A) Finset.univ_nonempty

/-- The unnormalized tilted mass of an event. -/
noncomputable def torusRCTiltEventWeight (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) : ℝ :=
  ∑ A, E.indicator (torusRCTiltWeight hN hM q) A

/-- Event probability for the normalized self-dual tilted weight. -/
noncomputable def torusRCTiltProbability (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) : ℝ :=
  torusRCTiltEventWeight hN hM q E / torusRCTiltPartition hN hM q

private theorem torusRCWeight_eq_tilt_mul_net (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusRCWeight hN hM q A =
      torusRCTiltWeight hN hM q A * q.val ^ rcNetIndicator hN hM A := by
  rw [torusRCTiltWeight_eq_standard_div_net]
  have hq : q.val ^ rcNetIndicator hN hM A ≠ 0 :=
    (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _).ne'
  field_simp [hq]

private theorem netCorrection_bounds (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    1 ≤ q.val ^ rcNetIndicator hN hM A ∧
      q.val ^ rcNetIndicator hN hM A ≤ q.val := by
  have hq : 1 ≤ q.val := q.property
  have hnet : rcNetIndicator hN hM A = 0 ∨ rcNetIndicator hN hM A = 1 := by
    unfold rcNetIndicator
    split <;> simp
  rcases hnet with hnet | hnet
  · simp [hnet, hq]
  · simp [hnet, hq]

private theorem torusRCWeight_tilt_bounds (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusRCTiltWeight hN hM q A ≤ torusRCWeight hN hM q A ∧
      torusRCWeight hN hM q A ≤ q.val * torusRCTiltWeight hN hM q A := by
  rw [torusRCWeight_eq_tilt_mul_net]
  have h := netCorrection_bounds hN hM q A
  refine ⟨?_, ?_⟩
  · calc
      torusRCTiltWeight hN hM q A = torusRCTiltWeight hN hM q A * 1 := by ring
      _ ≤ torusRCTiltWeight hN hM q A * q.val ^ rcNetIndicator hN hM A :=
        mul_le_mul_of_nonneg_left h.1 (tiltWeight_pos hN hM q A).le
  · calc
      torusRCTiltWeight hN hM q A * q.val ^ rcNetIndicator hN hM A ≤
          torusRCTiltWeight hN hM q A * q.val :=
        mul_le_mul_of_nonneg_left h.2 (tiltWeight_pos hN hM q A).le
      _ = q.val * torusRCTiltWeight hN hM q A := by ring

theorem torusRCTiltPartition_le_standard (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) :
    torusRCTiltPartition hN hM q ≤ torusRCPartition hN hM q := by
  unfold torusRCTiltPartition torusRCPartition FK.FiniteProbability.partition
  exact Finset.sum_le_sum fun A _ => (torusRCWeight_tilt_bounds hN hM q A).1

theorem torusRCPartition_le_q_mul_tilt (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) :
    torusRCPartition hN hM q ≤ q.val * torusRCTiltPartition hN hM q := by
  unfold torusRCTiltPartition torusRCPartition FK.FiniteProbability.partition
  calc
    _ ≤ ∑ A, q.val * torusRCTiltWeight hN hM q A :=
      Finset.sum_le_sum fun A _ => (torusRCWeight_tilt_bounds hN hM q A).2
    _ = _ := by rw [Finset.mul_sum]

private theorem torusRCTiltEventWeight_nonneg (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    0 ≤ torusRCTiltEventWeight hN hM q E := by
  unfold torusRCTiltEventWeight
  apply Finset.sum_nonneg
  intro A _
  by_cases hA : A ∈ E
  · simp [Set.indicator, hA]
    exact (tiltWeight_pos hN hM q A).le
  · simp [Set.indicator, hA]

private theorem torusRCTiltEventWeight_le_standard_numerator
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (RCConfig N M)) :
    torusRCTiltEventWeight hN hM q E ≤
      ∑ A, E.indicator (torusRCWeight hN hM q) A := by
  unfold torusRCTiltEventWeight
  apply Finset.sum_le_sum
  intro A _
  by_cases hA : A ∈ E
  · simp [Set.indicator, hA]
    exact (torusRCWeight_tilt_bounds hN hM q A).1
  · simp [Set.indicator, hA]

private theorem torusRCEventWeight_le_q_mul_tilt_numerator
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (RCConfig N M)) :
    (∑ A, E.indicator (torusRCWeight hN hM q) A) ≤
      q.val * torusRCTiltEventWeight hN hM q E := by
  unfold torusRCTiltEventWeight
  calc
    _ ≤ ∑ A, q.val * E.indicator (torusRCTiltWeight hN hM q) A := by
      apply Finset.sum_le_sum
      intro A _
      by_cases hA : A ∈ E
      · simp [Set.indicator, hA]
        exact (torusRCWeight_tilt_bounds hN hM q A).2
      · simp [Set.indicator, hA]
    _ = _ := by rw [Finset.mul_sum]

private theorem torusRCProbability_eq_standard_weight_ratio
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q E =
      (∑ A, E.indicator (torusRCWeight hN hM q) A) /
        torusRCPartition hN hM q := by
  rw [torusRCProbability_eq_sum]
  calc
    _ = ∑ A, E.indicator (torusRCWeight hN hM q) A /
          torusRCPartition hN hM q := by
      apply Finset.sum_congr rfl
      intro A _
      by_cases hA : A ∈ E
      · simp [Set.indicator, hA, torusRCMass]
      · simp [Set.indicator, hA]
    _ = (∑ A, E.indicator (torusRCWeight hN hM q) A) /
          torusRCPartition hN hM q := by
      rw [← Finset.sum_div]

/-- Standard and self-dual tilted event probabilities differ by at most one
factor of `q`, uniformly in the event and the torus periods. -/
theorem torusRCTiltProbability_comparison (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    torusRCTiltProbability hN hM q E / q.val ≤
        torusRCProbability hN hM q E ∧
      torusRCProbability hN hM q E ≤
        q.val * torusRCTiltProbability hN hM q E := by
  have hstdZ := torusRCPartition_pos hN hM q
  have htiltZ := torusRCTiltPartition_pos hN hM q
  have hnumT := torusRCTiltEventWeight_nonneg hN hM q E
  have hdenSupper := torusRCPartition_le_q_mul_tilt hN hM q
  have hdenSlower := torusRCTiltPartition_le_standard hN hM q
  have hnumLower := torusRCTiltEventWeight_le_standard_numerator hN hM q E
  have hnumUpper := torusRCEventWeight_le_q_mul_tilt_numerator hN hM q E
  have hqpos : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
  rw [torusRCTiltProbability, torusRCProbability_eq_standard_weight_ratio]
  constructor
  · have hratio : torusRCTiltEventWeight hN hM q E /
        (q.val * torusRCTiltPartition hN hM q) ≤
          (∑ A, E.indicator (torusRCWeight hN hM q) A) /
            torusRCPartition hN hM q := by
      apply (div_le_div_iff₀
        (mul_pos hqpos htiltZ) hstdZ).2
      calc
        torusRCTiltEventWeight hN hM q E * torusRCPartition hN hM q ≤
            torusRCTiltEventWeight hN hM q E *
              (q.val * torusRCTiltPartition hN hM q) :=
          mul_le_mul_of_nonneg_left hdenSupper hnumT
        _ ≤ (∑ A, E.indicator (torusRCWeight hN hM q) A) *
              (q.val * torusRCTiltPartition hN hM q) :=
          mul_le_mul_of_nonneg_right hnumLower (mul_nonneg hqpos.le htiltZ.le)
    simpa [div_div, mul_comm] using hratio
  · have hratio : (∑ A, E.indicator (torusRCWeight hN hM q) A) /
        torusRCPartition hN hM q ≤
          (q.val * torusRCTiltEventWeight hN hM q E) /
            torusRCTiltPartition hN hM q := by
      apply (div_le_div_iff₀ hstdZ htiltZ).2
      calc
        (∑ A, E.indicator (torusRCWeight hN hM q) A) *
            torusRCTiltPartition hN hM q ≤
          (q.val * torusRCTiltEventWeight hN hM q E) *
            torusRCTiltPartition hN hM q :=
          mul_le_mul_of_nonneg_right hnumUpper htiltZ.le
        _ ≤ (q.val * torusRCTiltEventWeight hN hM q E) *
              torusRCPartition hN hM q :=
          mul_le_mul_of_nonneg_left hdenSlower
            (mul_nonneg hqpos.le hnumT)
    simpa [mul_div_assoc] using hratio

end PottsDiscontinuity.TorusRC
