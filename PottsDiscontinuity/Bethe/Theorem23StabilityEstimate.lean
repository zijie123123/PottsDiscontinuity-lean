module

public import PottsDiscontinuity.Bethe.Theorem23ContinuousEstimate
public import PottsDiscontinuity.Bethe.Theorem23Counting

/-! # The counting-function contraction estimate (2.10) -/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem exists_uniform_Xi_upper_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ X : ℝ, 0 < X ∧ ∀ Δ ≤ Δ₀, ∀ α : ℝ, Xi (lamOf Δ) α ≤ X := by
  let lam0 := lamOf Δ₀
  let X := (Real.exp lam0 + 1) / (Real.exp lam0 - 1)
  have hlam0 : 0 < lam0 := lamOf_pos hΔ₀
  have hE : 1 < Real.exp lam0 := by simpa using hlam0
  refine ⟨X, div_pos (by linarith) (by linarith), fun Δ hΔ α => ?_⟩
  have hlam := lamOf_pos (lt_of_le_of_lt hΔ hΔ₀)
  exact (Xi_le_exp_ratio hlam α).trans (exp_ratio_mono hlam0 (lamOf_mono hΔ₀ hΔ))

/-- Uniform estimate (2.10) under an explicit `D/N` mesh bound. Its additive
constant depends on the mesh constant, the cutoff and `r`, and is independent
of the norm of `ρ_p-ρ`. No Bethe equation is needed for this estimate. -/
theorem exists_uniform_counting_contraction {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ m : ℝ, 0 < m ∧ m < 1 ∧ ∀ (r : ℕ) (D : ℝ), 0 ≤ D →
      ∃ E : ℝ, 0 < E ∧ ∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀),
      ∀ (N k : ℕ) (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1))
        (hs : 2 * (k + 1) ≤ N), N = 2 * ((k + 1) + r) →
      ∀ (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
        |Xi (lamOf Δ) α *
          (rootStepDensity N (k + 1) p hp (by omega) hs (kMap (lamOf Δ) α) -
            rho Δ (kMap (lamOf Δ) α))|)),
      (∀ j : Fin (k + 2),
        rootPartitionPoint (k + 1) p (by omega) j.succ -
          rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
        (fun x => betheCountingDerivative Δ N (k + 1) p x - rho Δ x)
        (countingError_bddAbove (lt_of_le_of_lt hΔ hΔ₀) N (k + 1) p) ≤
      (1 - m) * densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
        (fun x => rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x) hbdd + E / N := by
  obtain ⟨m, hm, hm1, hlower⟩ := exists_uniform_double_Xi_lower hΔ₀
  obtain ⟨X, hX, hupper⟩ := exists_uniform_Xi_upper_bound hΔ₀
  obtain ⟨C, hC, hquad⟩ := exists_uniform_step_kernel_quadrature hΔ₀
  refine ⟨m, hm, hm1, fun r D hD => ?_⟩
  let Q := C * D + 2 * C * (2 * r + 1 : ℝ) + C
  let E := X * Q / (2 * Real.pi) + m * (r : ℝ) / (2 * Real.pi)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨E, hE, fun Δ hΔ N k p hp hs hcount hbdd hmesh => ?_⟩
  have hΔvalid := lt_of_le_of_lt hΔ hΔ₀
  have hlam := lamOf_pos hΔvalid
  let s := rootStepDensity N (k + 1) p hp (by omega) hs
  let S := densityNorm Δ hΔvalid (fun x => s x - rho Δ x) hbdd
  have hpoint (α : ℝ) (hα : α ∈ Icc (-Real.pi) Real.pi) :
      |Xi (lamOf Δ) α *
        (betheCountingDerivative Δ N (k + 1) p (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))| ≤ (1 - m) * S + E / N := by
    let x := kMap (lamOf Δ) α
    let T := cBEop Δ s x / (2 * Real.pi)
    have hx : x ∈ Icc (-Real.pi) Real.pi := kMap_mem_Icc hlam hα
    have hq := hquad Δ hΔ x hx N k r p hp hs hcount D hD hmesh
    have hdiff : |betheCountingDerivative Δ N (k + 1) p x - T| ≤
        (Q / (N : ℝ)) / (2 * Real.pi) := by
      have hid : betheCountingDerivative Δ N (k + 1) p x - T =
          (((∑ j, d1Theta Δ x (p j)) / (N : ℝ)) -
            (∫ y in (-Real.pi)..Real.pi, d1Theta Δ x y * s y)) / (2 * Real.pi) := by
        dsimp [betheCountingDerivative, T, cBEop]
        ring
      rw [hid, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_sub_comm]
      exact div_le_div_of_nonneg_right hq (by positivity)
    have hweighted : |Xi (lamOf Δ) α * (betheCountingDerivative Δ N (k + 1) p x - T)| ≤
        X * ((Q / (N : ℝ)) / (2 * Real.pi)) := by
      rw [abs_mul, abs_of_pos (Xi_pos hlam α)]
      exact mul_le_mul (hupper Δ hΔ α) hdiff (abs_nonneg _) hX.le
    have hct := root_step_continuous_contraction hΔvalid p hp hs hcount hm.le
      (hlower Δ hΔ) hbdd hα
    have hid : Xi (lamOf Δ) α *
        (betheCountingDerivative Δ N (k + 1) p x - rho Δ x) =
        Xi (lamOf Δ) α * (betheCountingDerivative Δ N (k + 1) p x - T) +
          Xi (lamOf Δ) α * (T - rho Δ x) := by ring
    change |Xi (lamOf Δ) α * (betheCountingDerivative Δ N (k + 1) p x - rho Δ x)| ≤ _
    rw [hid]
    calc
      _ ≤ |Xi (lamOf Δ) α * (betheCountingDerivative Δ N (k + 1) p x - T)| +
          |Xi (lamOf Δ) α * (T - rho Δ x)| := abs_add_le _ _
      _ ≤ X * ((Q / (N : ℝ)) / (2 * Real.pi)) +
          ((1 - m) * S + m * (r : ℝ) / (2 * Real.pi * (N : ℝ))) :=
        add_le_add hweighted hct
      _ = (1 - m) * S + E / N := by dsimp [E]; ring
  unfold densityNorm
  have hzero : (0 : ℝ) ∈ Icc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  apply csSup_le
  · exact ⟨_, ⟨⟨0, hzero⟩, rfl⟩⟩
  · rintro _ ⟨α, rfl⟩
    exact hpoint α α.property

end PottsDiscontinuity.Bethe
