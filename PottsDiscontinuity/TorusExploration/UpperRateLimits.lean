module

public import PottsDiscontinuity.TorusRC.ElementaryTail
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! Numerical passage from the finite cylinder estimate to the height limsup. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open TorusRC Filter Topology
noncomputable section

lemma positiveEvenPeriod_tendsto : Tendsto positiveEvenPeriod atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop k] with m hm
  dsimp [positiveEvenPeriod]
  omega

lemma shiftedDiagonalIndex_tendsto :
    Tendsto (fun m => 2*(positiveEvenPeriod m-1)) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop k] with m hm
  dsimp [positiveEvenPeriod]
  omega

/-- The factor two in diagonalSite's frozen indexing is exactly canceled by
reflection's square root. -/
theorem log_sqrt_diagonal_rate (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n) (ξ : ℝ)
    (hRate : Tendsto (fun n => -Real.log (D n)/(n : ℝ)) atTop (𝓝 ξ)) :
    Tendsto (fun m => Real.log (Real.sqrt (D (2*(positiveEvenPeriod m-1)))) /
      (positiveEvenPeriod m : ℝ)) atTop (𝓝 (-ξ)) := by
  have hinv : Tendsto (fun m => 1/(positiveEvenPeriod m : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp positiveEvenPeriod_tendsto
  have hratio : Tendsto (fun m => ((2*(positiveEvenPeriod m-1) : ℕ) : ℝ)/
      (2*(positiveEvenPeriod m : ℝ))) atTop (𝓝 (1 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [] with m
    have hm : 1 ≤ positiveEvenPeriod m := by dsimp [positiveEvenPeriod]; omega
    have hmn : (positiveEvenPeriod m : ℝ) ≠ 0 := by exact_mod_cast (by omega : positiveEvenPeriod m ≠ 0)
    rw [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hm,Nat.cast_one]
    field_simp
  have h := (hRate.comp shiftedDiagonalIndex_tendsto).neg.mul hratio
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [] with m
  simp only [Function.comp_apply]
  rw [Real.log_sqrt (hD _)]
  have hm : 0 < positiveEvenPeriod m := positiveEvenPeriod_pos m
  have hi : 0 < 2*(positiveEvenPeriod m-1) := by dsimp [positiveEvenPeriod]; omega
  have hmn : (positiveEvenPeriod m : ℝ) ≠ 0 := by positivity
  have hin : ((2*(positiveEvenPeriod m-1) : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- A width-dependent finite prefactor has no effect on the height-normalized
upper rate. All probabilities used in the logarithm are honestly positive. -/
theorem log_tail_limsup_le (D p : ℕ → ℝ) (hD : ∀ n, 0 < D n)
    (ξ : ℝ) (hRate : Tendsto (fun n => -Real.log (D n)/(n : ℝ)) atTop (𝓝 ξ))
    (K : ℝ) (hK : 0 < K) (s : ℕ)
    (hp : ∀ᶠ m in atTop, 0 < p m ∧ p m ≤
      K*(Real.sqrt (D (2*(positiveEvenPeriod m-1))))^s) :
    limsup (fun m => ((Real.log (p m)/(positiveEvenPeriod m : ℝ) : ℝ) : EReal)) atTop ≤
      (-((s : ℝ))*ξ : ℝ) := by
  let F : ℕ → ℝ := fun m => Real.log K/(positiveEvenPeriod m : ℝ) +
    (s : ℝ)*(Real.log (Real.sqrt (D (2*(positiveEvenPeriod m-1)))) /
      (positiveEvenPeriod m : ℝ))
  have hconst : Tendsto (fun m => Real.log K/(positiveEvenPeriod m : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log K)).comp positiveEvenPeriod_tendsto
  have hF : Tendsto F atTop (𝓝 (-((s : ℝ))*ξ)) := by
    have h := hconst.add ((log_sqrt_diagonal_rate D (fun n => (hD n).le) ξ hRate).const_mul (s : ℝ))
    simpa only [zero_add,mul_neg,neg_mul] using h
  have hle : ∀ᶠ m in atTop,
      ((Real.log (p m)/(positiveEvenPeriod m : ℝ) : ℝ) : EReal) ≤ (F m : EReal) := by
    filter_upwards [hp] with m hm
    apply EReal.coe_le_coe_iff.mpr
    have hsqrt := Real.sqrt_pos.2 (hD (2*(positiveEvenPeriod m-1)))
    have hlog := Real.log_le_log hm.1 hm.2
    rw [Real.log_mul hK.ne' (pow_pos hsqrt s).ne',Real.log_pow] at hlog
    have hdiv := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg (positiveEvenPeriod m))
    simpa only [F,add_div,mul_div_assoc] using hdiv
  have hFE : Tendsto (fun m => (F m : EReal)) atTop (𝓝 ((-((s : ℝ))*ξ : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr hF
  rw [← hFE.limsup_eq]
  exact limsup_le_limsup hle

end
end PottsDiscontinuity.TorusExploration
