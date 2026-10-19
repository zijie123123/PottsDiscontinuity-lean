module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.ConnectionSymmetry

/-! A summable union bound for long dual connections across opposite half-planes.
The endpoint on the positive side lies on one of the two adjacent axis rows. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK MeasureTheory
noncomputable section

abbrev OppositeConnectionIndex := (ℕ × LatticeVertex) × Fin 2

/-- An actual connection from (k,-j) to a vertex in the negative half-plane. -/
def oppositeConnectionEvent (t : OppositeConnectionIndex) : Set LatticeConfiguration :=
  {ω | t.1.2.1 < 0 ∧ ω ∈ connectionEvent ((t.1.1 : ℤ),-(t.2.val : ℤ)) t.1.2}

/-- Uniform bound with a summable majorant on the entire countable endpoint carrier. -/
theorem free_oppositeConnection_bound (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|)))
    (t : OppositeConnectionIndex) :
    μ (oppositeConnectionEvent t) ≤ ENNReal.ofReal
      ((C * Real.exp c) * (Real.exp (-c * (t.1.1 : ℝ)) *
        Real.exp (-c * (|(t.1.2.1 : ℝ)| + |(t.1.2.2 : ℝ)|)))) := by
  have := hμ.1
  rcases t with ⟨⟨k,w⟩,j⟩
  by_cases hw : w.1 < 0
  · have heq : oppositeConnectionEvent ((k,w),j) =
        connectionEvent ((k : ℤ),-(j.val : ℤ)) w := by
      ext ω
      simp only [oppositeConnectionEvent,Set.mem_ofPred_eq,hw,true_and]
    rw [heq, ← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    apply ENNReal.ofReal_le_ofReal
    let u : LatticeVertex := ((k : ℤ),-(j.val : ℤ))
    have ht := free_connection_translate θ μ hμ u 0 (w-u)
    simp only [zero_add,sub_add_cancel] at ht
    have htr : μ.real (connectionEvent u w) = twoPoint μ (w-u) := congrArg ENNReal.toReal ht
    change μ.real (connectionEvent u w) ≤ _
    rw [htr]
    apply (hdecay (w-u)).trans
    have hdInt : (k : ℤ) + |w.1| + |w.2| - 1 ≤ |(w-u).1| + |(w-u).2| := by
      dsimp [u]
      have hj := j.isLt
      simp only [abs_eq_max_neg]
      omega
    have hd : (k : ℝ) + |(w.1 : ℝ)| + |(w.2 : ℝ)| - 1 ≤
        |((w-u).1 : ℝ)| + |((w-u).2 : ℝ)| := by exact_mod_cast hdInt
    calc
      C * Real.exp (-c * (|((w-u).1 : ℝ)| + |((w-u).2 : ℝ)|)) ≤
          C * Real.exp (c + (-c * (k : ℝ)) +
            (-c * (|(w.1 : ℝ)| + |(w.2 : ℝ)|))) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
        nlinarith only [mul_le_mul_of_nonneg_left hd hc.le]
      _ = _ := by rw [Real.exp_add,Real.exp_add]; ring
  · have heq : oppositeConnectionEvent ((k,w),j) = ∅ := by
      ext ω
      simp only [oppositeConnectionEvent,Set.mem_ofPred_eq,hw,false_and,Set.mem_empty_iff_false]
    rw [heq,measure_empty]
    exact bot_le

/-- Exponential free decay makes the probabilities summable over all endpoint pairs. -/
theorem free_oppositeConnections_tsum_ne_top (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    ∑' t : OppositeConnectionIndex, μ (oppositeConnectionEvent t) ≠ ⊤ := by
  have hnat : Summable (fun k : ℕ => Real.exp (-c * (k : ℝ))) := by
    simpa only [mul_comm] using (Real.summable_exp_nat_mul_iff.2 (neg_neg_of_pos hc))
  have hlat := summable_exp_neg_l1 hc
  have hprod := hnat.mul_of_nonneg hlat (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)
  have hscaled := hprod.mul_left (C * Real.exp c)
  have hfin : Summable (fun _ : Fin 2 => (1 : ℝ)) := (hasSum_fintype (fun _ : Fin 2 => (1 : ℝ))).summable
  have hscaled_nonneg : ∀ i : ℕ × LatticeVertex,
      0 ≤ (C * Real.exp c) * (Real.exp (-c * (i.1 : ℝ)) *
        Real.exp (-c * (|(i.2.1 : ℝ)| + |(i.2.2 : ℝ)|))) := by
    intro i
    exact mul_nonneg (mul_nonneg hC (Real.exp_nonneg _))
      (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  have hmajor := hscaled.mul_of_nonneg hfin hscaled_nonneg (fun _ => zero_le_one)
  simp only [mul_one] at hmajor
  apply ne_top_of_le_ne_top hmajor.tsum_ofReal_ne_top
  exact ENNReal.tsum_le_tsum (free_oppositeConnection_bound θ μ hμ C c hC hc hdecay)

/-- Only finitely many of these actual long connections occur almost surely. -/
theorem free_ae_finite_oppositeConnections (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    ∀ᵐ ω ∂μ, {t : OppositeConnectionIndex | ω ∈ oppositeConnectionEvent t}.Finite :=
  ae_finite_setOfPred_mem (free_oppositeConnections_tsum_ne_top θ μ hμ C c hC hc hdecay)

end
end PottsDiscontinuity.Duality
