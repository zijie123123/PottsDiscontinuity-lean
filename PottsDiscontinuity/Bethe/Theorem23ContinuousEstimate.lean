module

public import PottsDiscontinuity.Bethe.Theorem23Contraction
public import PottsDiscontinuity.Bethe.Theorem23Density
public import PottsDiscontinuity.Bethe.Theorem23Mass

/-! # Continuous contraction applied to the discrete density -/

@[expose] public section

open Set MeasureTheory intervalIntegral

namespace PottsDiscontinuity.Bethe

theorem intervalIntegrable_weighted_comp_kMap {lam : ℝ} (hlam : 0 < lam)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-Real.pi) Real.pi) :
    IntervalIntegrable (fun β => Xi lam β * f (kMap lam β)) volume (-Real.pi) Real.pi := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hf ⊢
  exact integrableOn_Xi_mul_comp hlam hf

theorem weighted_cBEop_difference {Δ : ℝ} (hΔ : Δ < -1)
    {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable g volume (-Real.pi) Real.pi) (α : ℝ) :
    Xi (lamOf Δ) α *
        ((cBEop Δ f (kMap (lamOf Δ) α) - cBEop Δ g (kMap (lamOf Δ) α)) / (2 * Real.pi)) =
      -xiConv (2 * lamOf Δ)
        (fun β => Xi (lamOf Δ) β * (f (kMap (lamOf Δ) β) - g (kMap (lamOf Δ) β))) α := by
  have hlam := lamOf_pos hΔ
  have hX := Xi_pos hlam α
  have hc := continuous_d1Theta_right hΔ (kMap (lamOf Δ) α)
  have hdiff : cBEop Δ f (kMap (lamOf Δ) α) - cBEop Δ g (kMap (lamOf Δ) α) =
      cBEop Δ (fun y => f y - g y) (kMap (lamOf Δ) α) - 1 := by
    unfold cBEop
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (hf.continuousOn_mul hc.continuousOn)
      (hg.continuousOn_mul hc.continuousOn)]
    ring
  have hscale : (∫ β in (-Real.pi)..Real.pi,
        Xi (2 * lamOf Δ) (α - β) *
          (2 * Real.pi * (f (kMap (lamOf Δ) β) - g (kMap (lamOf Δ) β)) * Xi (lamOf Δ) β)) =
      (2 * Real.pi) * ∫ β in (-Real.pi)..Real.pi,
        Xi (2 * lamOf Δ) (α - β) *
          (Xi (lamOf Δ) β * (f (kMap (lamOf Δ) β) - g (kMap (lamOf Δ) β))) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext β
    ring
  rw [hdiff, cBEop_kMap hΔ, hscale, xiConv]
  field_simp [ne_of_gt hX]
  ring

/-- Applying the continuous map to the step density contracts its weighted
distance to `ρ`, up to the exact mass-defect contribution. -/
theorem root_step_continuous_contraction {Δ : ℝ} (hΔ : Δ < -1)
    {N k r : ℕ} (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1))
    (hs : 2 * (k + 1) ≤ N) (hcount : N = 2 * ((k + 1) + r))
    {m : ℝ} (hm : 0 ≤ m) (hlower : ∀ t : ℝ, m ≤ Xi (2 * lamOf Δ) t)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N (k + 1) p hp (by omega) hs (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    {α : ℝ} (hα : α ∈ Icc (-Real.pi) Real.pi) :
    |Xi (lamOf Δ) α *
        (cBEop Δ (rootStepDensity N (k + 1) p hp (by omega) hs) (kMap (lamOf Δ) α) /
          (2 * Real.pi) - rho Δ (kMap (lamOf Δ) α))| ≤
      (1 - m) * densityNorm Δ hΔ
        (fun y => rootStepDensity N (k + 1) p hp (by omega) hs y - rho Δ y) hbdd +
        m * (r : ℝ) / (2 * Real.pi * (N : ℝ)) := by
  let s := rootStepDensity N (k + 1) p hp (by omega) hs
  let R := fun β => Xi (lamOf Δ) β * (s (kMap (lamOf Δ) β) - rho Δ (kMap (lamOf Δ) β))
  have his : IntervalIntegrable s volume (-Real.pi) Real.pi := by
    simpa [s] using intervalIntegrable_mul_rootStepDensity p hp (by omega) hs
      (g := fun _ => (1 : ℝ)) continuous_const (-Real.pi) Real.pi
  have hiρ : IntervalIntegrable (rho Δ) volume (-Real.pi) Real.pi :=
    (continuous_rho hΔ).intervalIntegrable _ _
  have hiR : IntervalIntegrable R volume (-Real.pi) Real.pi :=
    intervalIntegrable_weighted_comp_kMap (lamOf_pos hΔ) (his.sub hiρ)
  have hmass : (∫ β in (-Real.pi)..Real.pi, R β) = (r : ℝ) / N := by
    rw [← integral_Icc_comp_kMap (lamOf_pos hΔ) (fun y => s y - rho Δ y)]
    rw [intervalIntegral.integral_sub his hiρ, integral_rho_mass hΔ]
    change (∫ y in (-Real.pi)..Real.pi, rootStepDensity N (k + 1) p hp (by omega) hs y) - _ = _
    rw [root_step_physical_mass hp hs hcount]
    ring
  have hbound : ∀ β ∈ Icc (-Real.pi) Real.pi,
      |R β| ≤ densityNorm Δ hΔ (fun y => s y - rho Δ y) hbdd := by
    intro β hβ
    exact densityNorm_pointwise_le hΔ (fun y => s y - rho Δ y) hbdd _ le_rfl hβ
  have hcontract := xiConv_abs_le_with_mass_defect (by linarith [lamOf_pos hΔ])
    hm hlower hiR hbound α
  have hrho := rho_isCBESolution hΔ (kMap (lamOf Δ) α)
    (kMap_mem_Icc (lamOf_pos hΔ) hα)
  have hid := weighted_cBEop_difference hΔ his hiρ α
  have heq : cBEop Δ (rho Δ) (kMap (lamOf Δ) α) =
      2 * Real.pi * rho Δ (kMap (lamOf Δ) α) := hrho.symm
  rw [heq] at hid
  have hleft : Xi (lamOf Δ) α *
      (cBEop Δ s (kMap (lamOf Δ) α) / (2 * Real.pi) - rho Δ (kMap (lamOf Δ) α)) =
      -xiConv (2 * lamOf Δ) R α := by
    convert hid using 1
    field_simp
  change |Xi (lamOf Δ) α * (cBEop Δ s (kMap (lamOf Δ) α) / (2 * Real.pi) - _)| ≤ _
  rw [hleft, abs_neg]
  have hrNonneg : 0 ≤ (r : ℝ) / N := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [hmass, abs_of_nonneg hrNonneg] at hcontract
  convert hcontract using 1
  ring

end PottsDiscontinuity.Bethe
