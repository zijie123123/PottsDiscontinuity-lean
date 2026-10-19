module

public import PottsDiscontinuity.Bethe.AsymptoticQuadrature
public import PottsDiscontinuity.Bethe.Theorem23FiniteQuadrature
public import PottsDiscontinuity.Bethe.Theorem23GKernel
public import PottsDiscontinuity.Bethe.Theorem23HalfPartition

/-! # Uniform approximation of the off-diagonal row sums -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- The row Riemann approximation, with the mesh and left endpoint distance
made explicit. The right endpoint is controlled by symmetry in both parities. -/
theorem exists_uniform_rescaled_row_estimate {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ ≤ Δ₀, ∀ (N n : ℕ) (hn : 2 ≤ n), 0 < N →
      ∀ (p : Fin n → ℝ), p ∈ S_n n → ∀ d : ℝ, 0 ≤ d →
      (∀ j : Fin (n / 2), p (discreteHalfNextIndex n j) -
        p (discreteHalfIndex n j) ≤ d) →
      p (discreteHalfPartitionIndex n hn 0) + Real.pi ≤ d →
      ∀ i : Fin (n / 2),
        |(∑ j ∈ Finset.univ.erase i, |discreteBetheMatrixATilde Δ N n p i j|) -
          (discreteBetheG Δ (p (discreteHalfIndex n i)) 0 -
            discreteBetheG Δ (p (discreteHalfIndex n i)) (-Real.pi))| ≤ C * d := by
  obtain ⟨B, hB, hbounds⟩ := exists_uniform_discreteBetheG_deriv_bounds hΔ₀
  refine ⟨B * (2 * Real.pi + 3), by positivity,
    fun Δ hΔ N n hn hN p hp d hd hmesh hleft i => ?_⟩
  classical
  have hvalid := lt_of_le_of_lt hΔ hΔ₀
  let q : Fin (n / 2 + 1) → ℝ := fun j => p (discreteHalfPartitionIndex n hn j)
  let f : ℝ → ℝ := discreteBetheG Δ (p (discreteHalfIndex n i))
  let g : ℝ → ℝ := deriv f
  have hq : StrictMono q := fun j k hjk => hp.2.1 (by exact hjk)
  have hbox (j) : q j ∈ Icc (-Real.pi) Real.pi :=
    ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩
  have hx : p (discreteHalfIndex n i) ∈ Icc (-Real.pi) Real.pi :=
    ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩
  have hdiff (y : ℝ) : DifferentiableAt ℝ f y :=
    (analyticAt_theta_right hvalid _ y).differentiableAt.sub
      (analyticAt_theta_right hvalid _ y).differentiableAt
  have hg (y : ℝ) (hy : y ∈ Icc (-Real.pi) Real.pi) : |g y| ≤ B :=
    (hbounds Δ hΔ).1 _ hx y hy
  have hqm (j : Fin (n / 2)) : q j.succ - q j.castSucc ≤ d := hmesh j
  have hquad := finite_left_riemann_error q hq f g hbox hB.le hqm
    (fun y _ => (hdiff y).hasDerivAt) ((hbounds Δ hΔ).2 _ hx)
  have hlen : q (Fin.last (n / 2)) - q 0 ≤ 2 * Real.pi := by
    linarith [(hbox (Fin.last (n / 2))).2, (hbox 0).1]
  have hquad' : |(∑ j : Fin (n / 2), (q j.succ - q j.castSucc) * g (q j.castSucc)) -
      (f (q (Fin.last (n / 2))) - f (q 0))| ≤ B * d * (2 * Real.pi) :=
    hquad.trans (mul_le_mul_of_nonneg_left hlen (mul_nonneg hB.le hd))
  have hfLip (y) (hy : y ∈ Icc (-Real.pi) Real.pi)
      (z) (hz : z ∈ Icc (-Real.pi) Real.pi) : |f y - f z| ≤ B * |y-z| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le (fun t _ => hdiff t)
        (fun t ht => by simpa only [Real.norm_eq_abs] using hg t ht)
        (convex_Icc _ _) hz hy
  have hzero : (0 : ℝ) ∈ Icc (-Real.pi) Real.pi := ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
  have hminus : -Real.pi ∈ Icc (-Real.pi) Real.pi :=
    ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hend := discreteHalfPartition_endpoint hn p hp hmesh
  have hend' : |q (Fin.last (n / 2)) - 0| ≤ d := by
    change |p (discreteHalfPartitionIndex n hn (Fin.last (n / 2))) - 0| ≤ d
    simpa only [sub_zero, abs_of_nonneg hend.1] using hend.2
  have hstart : |q 0 - (-Real.pi)| ≤ d := by
    rw [sub_neg_eq_add, abs_of_nonneg (by linarith [(hbox 0).1])]
    exact hleft
  have hrightErr := (hfLip _ (hbox (Fin.last (n / 2))) 0 hzero).trans
    (mul_le_mul_of_nonneg_left hend' hB.le)
  have hleftErr := (hfLip _ (hbox 0) (-Real.pi) hminus).trans
    (mul_le_mul_of_nonneg_left hstart hB.le)
  have hdiagErr : |(q i.succ - q i.castSucc) * g (q i.castSucc)| ≤ B * d := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hq.monotone (by exact Fin.castSucc_le_succ i)))]
    calc
      _ ≤ (q i.succ - q i.castSucc) * B :=
        mul_le_mul_of_nonneg_left (hg _ (hbox _)) (sub_nonneg.mpr (hq.monotone (by exact Fin.castSucc_le_succ i)))
      _ ≤ d * B := mul_le_mul_of_nonneg_right (hqm i) hB.le
      _ = _ := mul_comm _ _
  have hrow : (∑ j ∈ Finset.univ.erase i, |discreteBetheMatrixATilde Δ N n p i j|) =
      (∑ j : Fin (n / 2), (q j.succ - q j.castSucc) * g (q j.castSucc)) -
        (q i.succ - q i.castSucc) * g (q i.castSucc) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    rw [abs_of_nonneg (discreteBetheMatrixATilde_offdiag_nonneg hvalid hN p hp i j hij),
      discreteBetheMatrixATilde_offdiag_eq hvalid p hp.2.2 hN i j hij]
    rfl
  rw [hrow]
  have htotal := abs_add_le
    ((∑ j : Fin (n / 2), (q j.succ - q j.castSucc) * g (q j.castSucc)) -
      (f (q (Fin.last (n / 2))) - f (q 0)))
    ((f (q (Fin.last (n / 2))) - f 0) - (f (q 0) - f (-Real.pi)) -
      (q i.succ - q i.castSucc) * g (q i.castSucc))
  have htail₁ := abs_add_le (f (q (Fin.last (n / 2))) - f 0) (-(f (q 0) - f (-Real.pi)))
  have htail₂ := abs_add_le
    ((f (q (Fin.last (n / 2))) - f 0) - (f (q 0) - f (-Real.pi)))
    (-((q i.succ - q i.castSucc) * g (q i.castSucc)))
  simp only [abs_neg] at htail₁ htail₂
  have hid : (∑ j : Fin (n / 2), (q j.succ - q j.castSucc) * g (q j.castSucc)) -
      (q i.succ - q i.castSucc) * g (q i.castSucc) - (f 0 - f (-Real.pi)) =
      ((∑ j : Fin (n / 2), (q j.succ - q j.castSucc) * g (q j.castSucc)) -
        (f (q (Fin.last (n / 2))) - f (q 0))) +
      ((f (q (Fin.last (n / 2))) - f 0) - (f (q 0) - f (-Real.pi)) -
        (q i.succ - q i.castSucc) * g (q i.castSucc)) := by ring
  change |_ - (f 0 - f (-Real.pi))| ≤ _
  rw [hid]
  simp only [sub_eq_add_neg, add_assoc] at htotal htail₁ htail₂ hquad' hrightErr hleftErr hdiagErr ⊢
  nlinarith only [htotal, htail₁, htail₂, hquad', hrightErr, hleftErr, hdiagErr]

/-- The source's off-diagonal row estimate with only the cyclic mesh premise. -/
theorem exists_uniform_rescaled_row_cyclic_estimate {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ ≤ Δ₀, ∀ (N k : ℕ), 0 < N →
      ∀ (p : Fin (k + 1) → ℝ), p ∈ S_n (k + 1) → ∀ d : ℝ, 0 ≤ d →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ d) →
      ∀ i : Fin ((k + 1) / 2),
        |(∑ j ∈ Finset.univ.erase i, |discreteBetheMatrixATilde Δ N (k + 1) p i j|) -
          (discreteBetheG Δ (p (discreteHalfIndex (k + 1) i)) 0 -
            discreteBetheG Δ (p (discreteHalfIndex (k + 1) i)) (-Real.pi))| ≤ C * d := by
  obtain ⟨C, hC, hrow⟩ := exists_uniform_rescaled_row_estimate hΔ₀
  refine ⟨C, hC, fun Δ hΔ N k hN p hp d hd hmesh i => ?_⟩
  have hn : 2 ≤ k + 1 := by have := i.isLt; omega
  have hfirst := (root_mesh_consequences hp hmesh).1
  have hzero : discreteHalfPartitionIndex (k + 1) hn 0 = 0 := rfl
  exact hrow Δ hΔ N (k + 1) hn hN p hp d hd
    (discreteHalf_gap_le_of_cyclic_mesh (by omega) p hmesh)
    (by simpa only [hzero] using hfirst) i

end PottsDiscontinuity.Bethe
