module

public import PottsDiscontinuity.Bethe.Theorem23MeanValue
public import PottsDiscontinuity.Bethe.Theorem23StabilityEstimate

/-! # Comparing the step density with the derivative of the counting function -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem rootPartitionPoint_mem_large {k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (i : Fin (k + 3)) :
    rootPartitionPoint (k + 1) p (by omega) i ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) := by
  unfold rootPartitionPoint
  split
  · have hb := hp.1 ⟨k + 1 - 1, by omega⟩
    constructor <;> linarith [hb.1, hb.2, Real.pi_pos]
  · split
    · have hb := hp.1 ⟨0, by omega⟩
      constructor <;> linarith [hb.1, hb.2, Real.pi_pos]
    · have hb := hp.1 ⟨i.val - 1, by omega⟩
      constructor <;> linarith [hb.1, hb.2, Real.pi_pos]

theorem exists_rootPartition_cell {k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) {t : ℝ} (ht : t ∈ Icc (-Real.pi) Real.pi) :
    ∃ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ t ∧
      t < rootPartitionPoint (k + 1) p (by omega) j.succ := by
  let q := rootPartitionPoint (k + 1) p (by omega)
  have hleft : q 0 ≤ t := by
    have heq : q 0 = p (Fin.last k) - 2 * Real.pi := by
      convert rootPartitionPoint_zero p (by omega) using 1 <;> congr 1
    rw [heq]
    linarith [ht.1, (hp.1 (Fin.last k)).2]
  have hright : t < q (Fin.last (k + 2)) := by
    have heq : q (Fin.last (k + 2)) = p 0 + 2 * Real.pi := by
      convert rootPartitionPoint_end p (by omega) using 1 <;> congr 1
    rw [heq]
    linarith [ht.2, (hp.1 0).1]
  by_contra h
  have hstep (j : Fin (k + 2)) (hj : q j.castSucc ≤ t) : q j.succ ≤ t := by
    by_contra hlt
    exact h ⟨j, hj, lt_of_not_ge hlt⟩
  have hall (i : Fin (k + 3)) : q i ≤ t := Fin.induction hleft hstep i
  exact (not_le.mpr hright) (hall _)

theorem exists_uniform_countingDerivative_lipschitz {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ L : ℝ, 0 < L ∧ ∀ Δ ≤ Δ₀, ∀ (N n : ℕ), 0 < N →
      ∀ (p : Fin n → ℝ), p ∈ S_n n → 2 * n ≤ N →
      ∀ x ∈ Icc (-(3 * Real.pi)) (3 * Real.pi),
      ∀ y ∈ Icc (-(3 * Real.pi)) (3 * Real.pi),
        |betheCountingDerivative Δ N n p x - betheCountingDerivative Δ N n p y| ≤ L * |x - y| := by
  obtain ⟨C, hC, hkernel⟩ := exists_uniform_d1Theta_box_bounds hΔ₀ (3 * Real.pi)
  refine ⟨C / (2 * Real.pi), by positivity, fun Δ hΔ N n hN p hp hs x hx y hy => ?_⟩
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hsize : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
  have hterm (j : Fin n) : |d1Theta Δ x (p j) - d1Theta Δ y (p j)| ≤ C * |x - y| := by
    have hpj : p j ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) := by
      constructor <;> linarith [(hp.1 j).1, (hp.1 j).2, Real.pi_pos]
    simpa using (hkernel Δ hΔ).2 x hx (p j) hpj y hy (p j) hpj
  have hsum : |∑ j : Fin n, (d1Theta Δ x (p j) - d1Theta Δ y (p j))| ≤
      (N : ℝ) * (C * |x - y|) := by
    calc
      _ ≤ ∑ j : Fin n, |d1Theta Δ x (p j) - d1Theta Δ y (p j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, C * |x - y| := Finset.sum_le_sum (fun j _ => hterm j)
      _ = (n : ℝ) * (C * |x - y|) := by simp
      _ ≤ (N : ℝ) * (C * |x - y|) := mul_le_mul_of_nonneg_right hsize (by positivity)
  have hid : betheCountingDerivative Δ N n p x - betheCountingDerivative Δ N n p y =
      (∑ j : Fin n, (d1Theta Δ x (p j) - d1Theta Δ y (p j))) / ((N : ℝ) * (2 * Real.pi)) := by
    rw [Finset.sum_sub_distrib]
    unfold betheCountingDerivative
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hNc (by positivity))]
  apply (div_le_iff₀ (mul_pos hNc (by positivity))).2
  apply hsum.trans_eq
  field_simp

/-- Step-density error is bounded by the counting derivative error plus a mesh
term. Comparing `f_p'(ξ)` directly with `f_p'(t)` avoids evaluating the density
or the weighted norm outside the physical interval. -/
theorem exists_uniform_step_counting_comparison {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀),
      ∀ (N k : ℕ) (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1))
        (hs : 2 * (k + 1) ≤ N), DiscreteBetheEquation Δ N (k + 1) p →
      ∀ (D : ℝ), 0 ≤ D →
      ∀ (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
        |Xi (lamOf Δ) α *
          (rootStepDensity N (k + 1) p hp (by omega) hs (kMap (lamOf Δ) α) -
            rho Δ (kMap (lamOf Δ) α))|)),
      (∀ j : Fin (k + 2),
        rootPartitionPoint (k + 1) p (by omega) j.succ -
          rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
        (fun x => rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x) hbdd ≤
      densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
        (fun x => betheCountingDerivative Δ N (k + 1) p x - rho Δ x)
        (countingError_bddAbove (lt_of_le_of_lt hΔ hΔ₀) N (k + 1) p) + A * D / N := by
  obtain ⟨L, hL, hLip⟩ := exists_uniform_countingDerivative_lipschitz hΔ₀
  obtain ⟨X, hX, hupper⟩ := exists_uniform_Xi_upper_bound hΔ₀
  refine ⟨X * L, mul_pos hX hL, fun Δ hΔ N k p hp hs hBE D hD hbdd hmesh => ?_⟩
  have hNnat : 0 < N := by omega
  have hΔvalid := lt_of_le_of_lt hΔ hΔ₀
  let s := rootStepDensity N (k + 1) p hp (by omega) hs
  let Sf := densityNorm Δ hΔvalid
    (fun x => betheCountingDerivative Δ N (k + 1) p x - rho Δ x)
    (countingError_bddAbove hΔvalid N (k + 1) p)
  have hpoint (α : ℝ) (hα : α ∈ Icc (-Real.pi) Real.pi) :
      |Xi (lamOf Δ) α * (s (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))| ≤
        Sf + (X * L) * D / N := by
    let t := kMap (lamOf Δ) α
    have ht : t ∈ Icc (-Real.pi) Real.pi := kMap_mem_Icc (lamOf_pos hΔvalid) hα
    obtain ⟨j, hcell⟩ := exists_rootPartition_cell hp ht
    obtain ⟨ξ, hξ, hmean⟩ := exists_betheCountingDerivative_cell_mean hΔvalid hNnat p hp hs hBE j
    have hξlarge : ξ ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) :=
      ⟨(rootPartitionPoint_mem_large hp j.castSucc).1.trans hξ.1.le,
        hξ.2.le.trans (rootPartitionPoint_mem_large hp j.succ).2⟩
    have htlarge : t ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) := by
      constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
    have hdist : |ξ - t| ≤ rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc := by
      apply abs_le.2
      constructor <;> linarith [hcell.1, hcell.2, hξ.1, hξ.2]
    have hstep : s t = betheCountingDerivative Δ N (k + 1) p ξ :=
      (rootStepDensity_on_cell hp (by omega) hs j hcell).trans hmean.symm
    have herr : |s t - betheCountingDerivative Δ N (k + 1) p t| ≤ L * (D / (N : ℝ)) := by
      rw [hstep]
      apply (hLip Δ hΔ N (k + 1) hNnat p hp hs ξ hξlarge t htlarge).trans
      exact mul_le_mul_of_nonneg_left (hdist.trans (hmesh j)) hL.le
    have hweighted : |Xi (lamOf Δ) α * (s t - betheCountingDerivative Δ N (k + 1) p t)| ≤
        X * (L * (D / (N : ℝ))) := by
      rw [abs_mul, abs_of_pos (Xi_pos (lamOf_pos hΔvalid) α)]
      exact mul_le_mul (hupper Δ hΔ α) herr (abs_nonneg _) hX.le
    have hfpoint : |Xi (lamOf Δ) α * (betheCountingDerivative Δ N (k + 1) p t - rho Δ t)| ≤ Sf :=
      densityNorm_pointwise_le hΔvalid _ (countingError_bddAbove hΔvalid N (k + 1) p) Sf le_rfl hα
    have hid : Xi (lamOf Δ) α * (s t - rho Δ t) =
        Xi (lamOf Δ) α * (s t - betheCountingDerivative Δ N (k + 1) p t) +
          Xi (lamOf Δ) α * (betheCountingDerivative Δ N (k + 1) p t - rho Δ t) := by ring
    change |Xi (lamOf Δ) α * (s t - rho Δ t)| ≤ _
    rw [hid]
    calc
      _ ≤ |Xi (lamOf Δ) α * (s t - betheCountingDerivative Δ N (k + 1) p t)| +
          |Xi (lamOf Δ) α * (betheCountingDerivative Δ N (k + 1) p t - rho Δ t)| := abs_add_le _ _
      _ ≤ X * (L * (D / (N : ℝ))) + Sf := add_le_add hweighted hfpoint
      _ = _ := by ring
  unfold densityNorm
  apply csSup_le
  · have hzero : (0 : ℝ) ∈ Icc (-Real.pi) Real.pi := by constructor <;> linarith [Real.pi_pos]
    exact ⟨_, ⟨⟨0, hzero⟩, rfl⟩⟩
  · rintro _ ⟨α, rfl⟩
    exact hpoint α α.property

end PottsDiscontinuity.Bethe
