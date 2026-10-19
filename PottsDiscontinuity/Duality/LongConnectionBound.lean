module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.ConnectionSymmetry
public import PottsDiscontinuity.Duality.PlanarConnectionAlternative

/-! Quantitative bounds on long connections with finitely many possible endpoints. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK MeasureTheory Filter Topology
noncomputable section

/-- A union bound retains the full endpoint count and the exact ℓ¹ distance. -/
theorem free_longConnectionEvent_bound (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|)))
    (S : Finset LatticeVertex) (n : ℕ) :
    μ.real (longConnectionEvent S n) ≤
      (S.card : ℝ) ^ 2 * (C * Real.exp (-c * (n : ℝ))) := by
  classical
  have := hμ.1
  let E := fun u v : LatticeVertex =>
    if (n : ℤ) ≤ |v.1 - u.1| + |v.2 - u.2| then connectionEvent u v else ∅
  have heq : longConnectionEvent S n = ⋃ u ∈ S, ⋃ v ∈ S, E u v := by
    ext ω
    simp [E, longConnectionEvent, and_left_comm]
  have hp (u v : LatticeVertex) : μ.real (E u v) ≤ C * Real.exp (-c * (n : ℝ)) := by
    dsimp [E]
    split_ifs with hn
    · have ht := free_connection_translate θ μ hμ u 0 (v - u)
      simp only [zero_add, sub_add_cancel] at ht
      have ht' : μ.real (connectionEvent u v) = twoPoint μ (v - u) :=
        congrArg ENNReal.toReal ht
      rw [ht']
      apply (hdecay (v - u)).trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
      have hd : (n : ℝ) ≤ |((v - u).1 : ℝ)| + |((v - u).2 : ℝ)| := by
        exact_mod_cast hn
      nlinarith only [mul_le_mul_of_nonneg_left hd hc.le]
    · simp only [measureReal_empty]
      exact mul_nonneg hC (Real.exp_nonneg _)
  rw [heq]
  calc
    μ.real (⋃ u ∈ S, ⋃ v ∈ S, E u v) ≤
        ∑ u ∈ S, μ.real (⋃ v ∈ S, E u v) := measureReal_biUnion_finset_le S _
    _ ≤ ∑ u ∈ S, ∑ v ∈ S, μ.real (E u v) := by
      exact Finset.sum_le_sum fun u _ => measureReal_biUnion_finset_le S _
    _ ≤ ∑ _u ∈ S, ∑ _v ∈ S, C * Real.exp (-c * (n : ℝ)) := by
      exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hp u v
    _ = (S.card : ℝ) ^ 2 * (C * Real.exp (-c * (n : ℝ))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The polynomial endpoint factor is negligible compared with any positive
exponential rate. The shift allows the expanded dual vertex domain. -/
lemma tendsto_square_longConnection_bound (C c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ 4 * (C * Real.exp (-c * (n : ℝ))))
      atTop (𝓝 0) := by
  have hs := (Real.summable_pow_mul_exp_neg_nat_mul 4 hc).tendsto_atTop_zero
  have hshift := hs.comp (tendsto_add_atTop_nat 2)
  have hm := hshift.mul_const (C * Real.exp (2 * c))
  simp only [zero_mul] at hm
  convert hm using 1
  ext n
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
  have he : Real.exp (-c * ((n : ℝ) + 2)) * Real.exp (2 * c) =
      Real.exp (-c * (n : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show ((n : ℝ) + 2) ^ 4 * Real.exp (-c * ((n : ℝ) + 2)) *
      (C * Real.exp (2 * c)) =
        ((n : ℝ) + 2) ^ 4 * C *
          (Real.exp (-c * ((n : ℝ) + 2)) * Real.exp (2 * c)) by ring, he]
  ring

end
end PottsDiscontinuity.Duality
