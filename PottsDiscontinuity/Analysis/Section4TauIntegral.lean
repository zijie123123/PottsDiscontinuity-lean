module

public import Mathlib
public import PottsDiscontinuity.Analysis.Section4Series

/-!
# The explicit τ integral in Section 4

The literal τ series is interpreted by its ordered partial sums.  This file uses Abel means of
that series.  The Poisson regularization splits into a sawtooth term and an exponentially
convergent correction, which gives the uniform local bound needed against the singular `P'`.
-/

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

private theorem fourier_one_sub_cos_lower_tau {α : ℝ} (hα : α ∈ Icc (-π) π) :
    2 * α ^ 2 / π ^ 2 ≤ 1 - Real.cos α := by
  have hx : |α / 2| ≤ π / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have habs : |α| ≤ π := abs_le.mpr ⟨by linarith [hα.1], hα.2⟩
    linarith
  have hj := Real.mul_abs_le_abs_sin hx
  have hjSq : ((2 / π) * |α / 2|) ^ 2 ≤ |Real.sin (α / 2)| ^ 2 :=
    (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 hj
  have habshalf : |α / 2| = |α| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [habshalf] at hjSq
  have hsimpl : (2 / π * (|α| / 2)) ^ 2 = α ^ 2 / π ^ 2 := by
    field_simp [Real.pi_ne_zero]
    rw [sq_abs]
  rw [hsimpl, sq_abs] at hjSq
  have hsin := Real.sin_sq_eq_half_sub (α / 2)
  rw [show 2 * (α / 2) = α by ring] at hsin
  calc
    2 * α ^ 2 / π ^ 2 = 2 * (α ^ 2 / π ^ 2) := by ring
    _ ≤ 2 * Real.sin (α / 2) ^ 2 := mul_le_mul_of_nonneg_left hjSq (by norm_num)
    _ = 1 - Real.cos α := by rw [hsin]; ring

 noncomputable def fourierPrimeControl (lam : ℝ) : ℝ :=
  (π / (Real.cosh (2 * lam) - 1) + π ^ 2 / 2) / 2

private theorem fourierPPrime_alpha_bound {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α| * |α| ≤ fourierPrimeControl lam := by
  by_cases hα0 : α = 0
  · have hcosh : 1 < Real.cosh (2 * lam) :=
      Real.one_lt_cosh.mpr (by positivity)
    simp [fourierPPrime, hα0]
    dsimp [fourierPrimeControl]
    positivity
  · have hcosLower := fourier_one_sub_cos_lower_tau hα
    have hαabs : |α| ≤ π := abs_le.mpr ⟨by linarith [hα.1], hα.2⟩
    have hαsq : 0 < α ^ 2 := sq_pos_of_ne_zero hα0
    have hdenLower : 0 < 1 - Real.cos α := by
      have hpos : 0 < 2 * α ^ 2 / π ^ 2 := by positivity
      exact lt_of_lt_of_le hpos hcosLower
    have hcosh : 1 < Real.cosh (2 * lam) :=
      Real.one_lt_cosh.mpr (by positivity)
    have hden1 : 0 < Real.cosh (2 * lam) - Real.cos α := by
      linarith [Real.cos_le_one α]
    have hden1Lower : Real.cosh (2 * lam) - 1 ≤ Real.cosh (2 * lam) - Real.cos α := by
      linarith [Real.cos_le_one α]
    have hcoshden : 0 < Real.cosh (2 * lam) - 1 := by linarith
    have hsin1 : |Real.sin α| ≤ 1 := Real.abs_sin_le_one α
    have hsinα : |Real.sin α| ≤ |α| := Real.abs_sin_le_abs
    have hfirst :
        |Real.sin α| * |α| / (Real.cosh (2 * lam) - Real.cos α) ≤
          π / (Real.cosh (2 * lam) - 1) := by
      apply (div_le_div_iff₀ hden1 hcoshden).2
      have hnum : |Real.sin α| * |α| ≤ π := by
        calc
          |Real.sin α| * |α| ≤ 1 * |α| :=
            mul_le_mul_of_nonneg_right hsin1 (abs_nonneg α)
          _ ≤ 1 * π := mul_le_mul_of_nonneg_left hαabs (by norm_num)
          _ = π := by ring
      calc
        |Real.sin α| * |α| * (Real.cosh (2 * lam) - 1) ≤
            π * (Real.cosh (2 * lam) - 1) := by
              exact mul_le_mul_of_nonneg_right hnum (le_of_lt hcoshden)
        _ ≤ π * (Real.cosh (2 * lam) - Real.cos α) := by
              exact mul_le_mul_of_nonneg_left hden1Lower (by positivity)
    have hsecond :
        |Real.sin α| * |α| / (1 - Real.cos α) ≤ π ^ 2 / 2 := by
      apply (div_le_iff₀ hdenLower).2
      calc
        |Real.sin α| * |α| ≤ α ^ 2 := by
          calc
            |Real.sin α| * |α| ≤ |α| * |α| :=
              mul_le_mul_of_nonneg_right hsinα (abs_nonneg α)
            _ = α ^ 2 := by
              calc
                |α| * |α| = |α| ^ 2 := by ring
                _ = α ^ 2 := sq_abs α
        _ ≤ (π ^ 2 / 2) * (1 - Real.cos α) := by
          have hfactor : 0 < π ^ 2 / 2 := by positivity
          have hmul := mul_le_mul_of_nonneg_left hcosLower (le_of_lt hfactor)
          have hrewrite : (π ^ 2 / 2) * (2 * α ^ 2 / π ^ 2) = α ^ 2 := by
            field_simp [Real.pi_ne_zero]
          rw [← hrewrite]
          exact hmul
    have hformula : fourierPPrime lam α = (1 / 2 : ℝ) *
        (Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
          Real.sin α / (1 - Real.cos α)) := by
      simp [fourierPPrime, hα0]
    rw [hformula]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))]
    calc
      (1 / 2 : ℝ) *
          |Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
            Real.sin α / (1 - Real.cos α)| * |α| ≤
        (1 / 2 : ℝ) *
          (|Real.sin α / (Real.cosh (2 * lam) - Real.cos α)| +
            |Real.sin α / (1 - Real.cos α)|) * |α| :=
            by
              have hab :
                  |Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
                    Real.sin α / (1 - Real.cos α)| ≤
                    |Real.sin α / (Real.cosh (2 * lam) - Real.cos α)| +
                      |Real.sin α / (1 - Real.cos α)| := abs_sub _ _
              have hbase := mul_le_mul_of_nonneg_right hab (abs_nonneg α)
              calc
                (1 / 2 : ℝ) *
                    |Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
                      Real.sin α / (1 - Real.cos α)| * |α| =
                    (1 / 2 : ℝ) *
                      (|Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
                        Real.sin α / (1 - Real.cos α)| * |α|) := by ring
                _ ≤ (1 / 2 : ℝ) *
                    ((|Real.sin α / (Real.cosh (2 * lam) - Real.cos α)| +
                      |Real.sin α / (1 - Real.cos α)|) * |α|) :=
                        mul_le_mul_of_nonneg_left hbase (by norm_num)
                _ = _ := by ring
      _ = (1 / 2 : ℝ) *
            (|Real.sin α| * |α| / (Real.cosh (2 * lam) - Real.cos α) +
              |Real.sin α| * |α| / (1 - Real.cos α)) := by
              rw [abs_div, abs_div, abs_of_pos hden1, abs_of_pos hdenLower]
              ring_nf
      _ ≤ (1 / 2 : ℝ) *
            (π / (Real.cosh (2 * lam) - 1) + π ^ 2 / 2) :=
              mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num)
      _ = fourierPrimeControl lam := by
          dsimp [fourierPrimeControl]
          ring

noncomputable def tauFourierTerm (lam α : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / (π * ((n : ℝ) + 1)) *
    Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) * Real.sin (((n + 1 : ℕ) : ℝ) * α)

noncomputable def tauAbel (lam μ α : ℝ) : ℝ :=
  ∑' n : ℕ, tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1)

noncomputable def tauAbelCorrectionTerm (lam μ α : ℝ) (n : ℕ) : ℝ :=
  (1 / (2 * π) : ℝ) * Real.exp (-μ) ^ (n + 1) *
    Bethe.tauCoeff lam n * Real.sin (((n + 1 : ℕ) : ℝ) * α)

private theorem summable_tauAbelCorrection {lam μ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (α : ℝ) : Summable (tauAbelCorrectionTerm lam μ α) := by
  have hcoeff := Bethe.summable_tauCoeff hlam
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hrle : Real.exp (-μ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  apply Summable.of_norm_bounded (g := fun n => |Bethe.tauCoeff lam n| / (2 * π))
    (hcoeff.abs.div_const (2 * π))
  intro n
  rw [Real.norm_eq_abs, tauAbelCorrectionTerm]
  have hpow : 0 ≤ Real.exp (-μ) ^ (n + 1) := by positivity
  have hsin : |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤ 1 := Real.abs_sin_le_one _
  have h2pi : 0 < 2 * π := by positivity
  have hconst : 0 < (1 / (2 * π) : ℝ) := by positivity
  have hnorm :
      |(1 / (2 * π) : ℝ) * Real.exp (-μ) ^ (n + 1) *
          Bethe.tauCoeff lam n * Real.sin (((n + 1 : ℕ) : ℝ) * α)| =
        (1 / (2 * π)) * |Real.exp (-μ) ^ (n + 1)| *
          |Bethe.tauCoeff lam n| * |Real.sin (((n + 1 : ℕ) : ℝ) * α)| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hconst]
  calc
    |(1 / (2 * π) : ℝ) * Real.exp (-μ) ^ (n + 1) *
        Bethe.tauCoeff lam n * Real.sin (((n + 1 : ℕ) : ℝ) * α)| = _ := hnorm
    _ ≤ (1 / (2 * π)) * 1 * |Bethe.tauCoeff lam n| * 1 := by
          have hpowAbs : |Real.exp (-μ) ^ (n + 1)| ≤ 1 := by
            rw [abs_of_nonneg hpow]
            exact pow_le_one₀ hr.le hrle
          calc
            (1 / (2 * π)) * |Real.exp (-μ) ^ (n + 1)| * |Bethe.tauCoeff lam n| *
                |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤
              (1 / (2 * π)) * 1 * |Bethe.tauCoeff lam n| *
                |Real.sin (((n + 1 : ℕ) : ℝ) * α)| := by
                  calc
                    (1 / (2 * π)) * |Real.exp (-μ) ^ (n + 1)| * |Bethe.tauCoeff lam n| *
                        |Real.sin (((n + 1 : ℕ) : ℝ) * α)| =
                      ((1 / (2 * π)) * |Real.exp (-μ) ^ (n + 1)|) *
                        (|Bethe.tauCoeff lam n| * |Real.sin (((n + 1 : ℕ) : ℝ) * α)|) := by ring
                    _ ≤ ((1 / (2 * π)) * 1) *
                        (|Bethe.tauCoeff lam n| * |Real.sin (((n + 1 : ℕ) : ℝ) * α)|) :=
                          mul_le_mul_of_nonneg_right
                            (mul_le_mul_of_nonneg_left hpowAbs (by positivity))
                            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
                    _ = _ := by ring
            _ ≤ (1 / (2 * π)) * 1 * |Bethe.tauCoeff lam n| * 1 := by
                  exact mul_le_mul_of_nonneg_left hsin (by positivity)
            _ = _ := by ring
    _ = |Bethe.tauCoeff lam n| / (2 * π) := by ring

private theorem tauAbel_eq_sawS_add_correction {lam μ α : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) :
    tauAbel lam μ α = (1 / (2 * π) : ℝ) * Bethe.sawS μ α +
      ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n := by
  let r : ℝ := Real.exp (-μ)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hbase : Summable (fun n : ℕ =>
      2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
        Real.sin (((n + 1 : ℕ) : ℝ) * α)) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => 2 * r ^ (n + 1))
    · have hgeom := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * r)
      refine hgeom.congr fun n => ?_
      rw [pow_succ]
      ring
    · intro n
      rw [Real.norm_eq_abs]
      have hn : 0 < (n : ℝ) + 1 := by positivity
      have hrpow : 0 ≤ r ^ (n + 1) := by positivity
      have hsin : |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤ 1 := Real.abs_sin_le_one _
      have habs :
          |2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
            Real.sin (((n + 1 : ℕ) : ℝ) * α)| =
          2 * r ^ (n + 1) / ((n : ℝ) + 1) *
            |Real.sin (((n + 1 : ℕ) : ℝ) * α)| := by
        rw [abs_mul, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_nonneg hrpow, abs_of_pos hn]
        ring
      rw [habs]
      calc
        2 * r ^ (n + 1) / ((n : ℝ) + 1) * |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤
          2 * r ^ (n + 1) / ((n : ℝ) + 1) * 1 := by gcongr
        _ ≤ 2 * r ^ (n + 1) := by
          have hdenNat : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
          have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hdenNat
          calc
            2 * r ^ (n + 1) / ((n : ℝ) + 1) * 1 =
                (2 * r ^ (n + 1)) / ((n : ℝ) + 1) := by ring
            _ ≤ 2 * r ^ (n + 1) := div_le_self (by positivity) hden
        _ = 2 * r ^ (n + 1) := rfl
  have hcorr := summable_tauAbelCorrection hlam hμ α
  have hbaseScaled := hbase.mul_left (1 / (2 * π) : ℝ)
  have hsumOriginal := hbaseScaled.add hcorr
  have hterm : ∀ n : ℕ,
      tauFourierTerm lam α n * r ^ (n + 1) =
        (1 / (2 * π) : ℝ) *
          (2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
            Real.sin (((n + 1 : ℕ) : ℝ) * α)) +
        tauAbelCorrectionTerm lam μ α n := by
    intro n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hpi : π ≠ 0 := Real.pi_ne_zero
    rw [tauFourierTerm, tauAbelCorrectionTerm]
    dsimp [Bethe.tauCoeff]
    have hcast : lam * ((n + 1 : ℕ) : ℝ) = lam * ((n : ℝ) + 1) := by push_cast; ring
    rw [hcast]
    have hpow : (-1 : ℝ) ^ (n + 1) = -(-1 : ℝ) ^ n := by rw [pow_succ]; ring
    rw [hpow]
    field_simp [hpi, hn]
    ring
  have hsplit : (fun n : ℕ => tauFourierTerm lam α n * r ^ (n + 1)) =
      (fun (n : ℕ) => (1 / (2 * π) : ℝ) *
        (2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
          Real.sin (((n + 1 : ℕ) : ℝ) * α)) +
        tauAbelCorrectionTerm lam μ α n) := by
    funext n
    exact hterm n
  have hsumTau : HasSum (fun n : ℕ => tauFourierTerm lam α n * r ^ (n + 1))
      (∑' n : ℕ,
        ((1 / (2 * π) : ℝ) *
          (2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
            Real.sin (((n + 1 : ℕ) : ℝ) * α)) +
          tauAbelCorrectionTerm lam μ α n)) := by
    exact HasSum.congr_fun hsumOriginal.hasSum (fun n => hterm n)
  have hsumEq := hsumTau.tsum_eq
  have hbaseTsum : Bethe.sawS μ α = ∑' n : ℕ,
      2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
        Real.sin (((n + 1 : ℕ) : ℝ) * α) := by
    simp [Bethe.sawS, r]
  calc
    tauAbel lam μ α = ∑' n : ℕ, tauFourierTerm lam α n * r ^ (n + 1) := by
      simp [tauAbel, r]
    _ = (1 / (2 * π) : ℝ) *
          (∑' n : ℕ, 2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
            Real.sin (((n + 1 : ℕ) : ℝ) * α)) +
          ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n := by
            calc
              _ = ∑' n : ℕ,
                    ((1 / (2 * π) : ℝ) *
                      (2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
                        Real.sin (((n + 1 : ℕ) : ℝ) * α)) +
                      tauAbelCorrectionTerm lam μ α n) := hsumEq
              _ = (∑' n : ℕ,
                    (1 / (2 * π) : ℝ) *
                      (2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
                        Real.sin (((n + 1 : ℕ) : ℝ) * α))) +
                    ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n :=
                  hbaseScaled.tsum_add hcorr
              _ = (1 / (2 * π) : ℝ) *
                    (∑' n : ℕ,
                      2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) *
                        Real.sin (((n + 1 : ℕ) : ℝ) * α)) +
                    ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n := by
                  rw [tsum_mul_left]
    _ = (1 / (2 * π) : ℝ) * Bethe.sawS μ α +
          ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n := by rw [hbaseTsum]

private theorem summable_tauCoeff_weighted {lam : ℝ} (hlam : 0 < lam) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|) := by
  let r : ℝ := Real.exp (-lam)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr]
    exact hr1
  have hpolyNorm : Summable (fun n : ℕ => ‖(n : ℝ) * r ^ n‖) := by
    have h := summable_norm_pow_mul_geometric_of_norm_lt_one (k := 1) hrnorm
    simpa [pow_one] using h
  have hpoly : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    summable_norm_iff.mp hpolyNorm
  have hshift := (summable_nat_add_iff 1
    (f := fun n : ℕ => (n : ℝ) * r ^ n)).mpr hpoly
  have hgeom : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ (n + 1)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hshift
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => 2 * (((n : ℝ) + 1) * r ^ (n + 1))) (hgeom.mul_left 2)
  intro n
  have hcoeff := Bethe.abs_tauCoeff_le lam n
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hrpow : 0 ≤ r ^ (n + 1) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt hm) (abs_nonneg _))]
  calc
    ((n : ℝ) + 1) * |Bethe.tauCoeff lam n| ≤
        ((n : ℝ) + 1) * (2 * r ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hcoeff (le_of_lt hm)
    _ = 2 * (((n : ℝ) + 1) * r ^ (n + 1)) := by ring

noncomputable def tauCoeffWeightedSum (lam : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|

private theorem tauAbelCorrection_abs_bound {lam μ α : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) :
    |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| ≤
      (1 / (2 * π) : ℝ) * |α| * tauCoeffWeightedSum lam := by
  let c : ℝ := 1 / (2 * π)
  have hc : 0 < c := by dsimp [c]; positivity
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hrle : Real.exp (-μ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hpow (n : ℕ) : |Real.exp (-μ) ^ (n + 1)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ hr.le hrle
  have hsin (n : ℕ) :
      |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤ ((n : ℝ) + 1) * |α| := by
    calc
      |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤
          |(((n + 1 : ℕ) : ℝ) * α)| := Real.abs_sin_le_abs
      _ = ((n : ℝ) + 1) * |α| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          congr 1
          push_cast
          ring
  have hcorr := summable_tauAbelCorrection hlam hμ α
  have hnormSum : Summable (fun n : ℕ => |tauAbelCorrectionTerm lam μ α n|) := by
    simpa [Real.norm_eq_abs] using hcorr.norm
  have hmajor : Summable (fun n : ℕ =>
      c * |α| * (((n : ℝ) + 1) * |Bethe.tauCoeff lam n|)) :=
    (summable_tauCoeff_weighted hlam).mul_left (c * |α|)
  have hbound (n : ℕ) :
      |tauAbelCorrectionTerm lam μ α n| ≤
        c * |α| * (((n : ℝ) + 1) * |Bethe.tauCoeff lam n|) := by
    rw [tauAbelCorrectionTerm, abs_mul, abs_mul, abs_mul, abs_of_pos hc]
    calc
      c * |Real.exp (-μ) ^ (n + 1)| * |Bethe.tauCoeff lam n| *
          |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤
        c * 1 * |Bethe.tauCoeff lam n| * (((n : ℝ) + 1) * |α|) := by
            calc
              _ ≤ c * 1 * |Bethe.tauCoeff lam n| *
                    |Real.sin (((n + 1 : ℕ) : ℝ) * α)| := by
                      have hcoeffNonneg : 0 ≤ |Bethe.tauCoeff lam n| := abs_nonneg _
                      calc
                        c * |Real.exp (-μ) ^ (n + 1)| * |Bethe.tauCoeff lam n| *
                            |Real.sin (((n + 1 : ℕ) : ℝ) * α)| =
                          (c * |Real.exp (-μ) ^ (n + 1)|) *
                            (|Bethe.tauCoeff lam n| *
                              |Real.sin (((n + 1 : ℕ) : ℝ) * α)|) := by ring
                        _ ≤ (c * 1) *
                            (|Bethe.tauCoeff lam n| *
                              |Real.sin (((n + 1 : ℕ) : ℝ) * α)|) :=
                              mul_le_mul_of_nonneg_right
                                (mul_le_mul_of_nonneg_left (hpow n) (by positivity))
                                (mul_nonneg hcoeffNonneg (abs_nonneg _))
                        _ = _ := by ring
              _ ≤ _ := by
                    have hcCoeff : 0 ≤ (c * 1) * |Bethe.tauCoeff lam n| :=
                      mul_nonneg (by positivity) (abs_nonneg _)
                    calc
                      (c * 1 * |Bethe.tauCoeff lam n|) *
                          |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤
                        (c * 1 * |Bethe.tauCoeff lam n|) *
                          (((n : ℝ) + 1) * |α|) :=
                            mul_le_mul_of_nonneg_left (hsin n) hcCoeff
                      _ = _ := by ring
      _ = c * |α| * (((n : ℝ) + 1) * |Bethe.tauCoeff lam n|) := by ring
  calc
    |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| ≤
        ∑' n : ℕ, |tauAbelCorrectionTerm lam μ α n| := by
          have hnormTsum :
              ‖∑' n : ℕ, tauAbelCorrectionTerm lam μ α n‖ ≤
                ∑' n : ℕ, ‖tauAbelCorrectionTerm lam μ α n‖ :=
            norm_tsum_le_tsum_norm hnormSum
          simpa only [Real.norm_eq_abs] using hnormTsum
    _ ≤ ∑' n : ℕ,
          c * |α| * (((n : ℝ) + 1) * |Bethe.tauCoeff lam n|) :=
            hnormSum.tsum_le_tsum hbound hmajor
    _ = c * |α| * tauCoeffWeightedSum lam := by
          change
            (∑' n : ℕ, (c * |α|) *
                (((n : ℝ) + 1) * |Bethe.tauCoeff lam n|)) =
              (c * |α|) *
                (∑' n : ℕ, ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|)
          exact tsum_mul_left
    _ = (1 / (2 * π) : ℝ) * |α| * tauCoeffWeightedSum lam := by rfl

private theorem sawS_abs_le_pi {μ α : ℝ} (hμ : 0 < μ) :
    |Bethe.sawS μ α| ≤ π := by
  rw [Bethe.sawS_eq_arctan hμ α, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
  have hlow := Real.neg_pi_div_two_lt_arctan
    (Real.sin α / (Real.exp μ + Real.cos α))
  have hupp := Real.arctan_lt_pi_div_two
    (Real.sin α / (Real.exp μ + Real.cos α))
  have habs : |Real.arctan (Real.sin α / (Real.exp μ + Real.cos α))| ≤ π / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  nlinarith

private theorem sawS_abs_le_two_mul_abs {μ α : ℝ} (hμ : 0 < μ)
    (hα : |α| ≤ π / 2) :
    |Bethe.sawS μ α| ≤ 2 * |α| := by
  rw [Bethe.sawS_eq_arctan hμ α, abs_mul,
    abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
  norm_num
  have hcos : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc (abs_le.mp hα)
  have hden : 1 ≤ Real.exp μ + Real.cos α := by
    have hexp : 1 < Real.exp μ := by simpa using hμ
    linarith
  have hdenPos : 0 < Real.exp μ + Real.cos α := by linarith
  have hratio :
      |Real.sin α / (Real.exp μ + Real.cos α)| ≤ |α| := by
    rw [abs_div, abs_of_pos hdenPos]
    calc
      |Real.sin α| / (Real.exp μ + Real.cos α) ≤ |Real.sin α| / 1 := by
        exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hden
      _ ≤ |α| := by
        simpa only [div_one] using (Real.abs_sin_le_abs (x := α))
  have harctan :
      |Real.arctan (Real.sin α / (Real.exp μ + Real.cos α))| ≤
        |Real.sin α / (Real.exp μ + Real.cos α)| := Real.abs_arctan_le_abs
  have hfinal := harctan.trans hratio
  nlinarith [hfinal, abs_nonneg α]

noncomputable def tauAbelCorrectionCoeff (lam μ : ℝ) (n : ℕ) : ℝ :=
  (1 / (2 * π) : ℝ) * Real.exp (-μ) ^ (n + 1) * Bethe.tauCoeff lam n

private theorem summable_tauAbelCorrectionCoeff {lam μ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) : Summable (tauAbelCorrectionCoeff lam μ) := by
  let c : ℝ := 1 / (2 * π)
  have hc : 0 < c := by dsimp [c]; positivity
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hrle : Real.exp (-μ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hsum : Summable (fun n : ℕ => c * |Bethe.tauCoeff lam n|) := by
    exact (Bethe.summable_tauCoeff hlam).abs.mul_left c
  apply Summable.of_norm_bounded (g := fun n : ℕ => c * |Bethe.tauCoeff lam n|) hsum
  intro n
  rw [Real.norm_eq_abs, tauAbelCorrectionCoeff]
  have hpow : |Real.exp (-μ) ^ (n + 1)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ hr.le hrle
  rw [abs_mul, abs_mul, abs_of_pos hc]
  calc
    c * |Real.exp (-μ) ^ (n + 1)| * |Bethe.tauCoeff lam n| ≤
        c * 1 * |Bethe.tauCoeff lam n| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hc.le) (abs_nonneg _)
    _ = c * |Bethe.tauCoeff lam n| := by ring

private theorem tauAbelCorrection_eq_trigSeries {lam μ α : ℝ} :
    (∑' n : ℕ, tauAbelCorrectionTerm lam μ α n) =
      Bethe.trigSeries 0 (fun _ => 0) (tauAbelCorrectionCoeff lam μ) α := by
  have hterm : ∀ n : ℕ,
      tauAbelCorrectionTerm lam μ α n =
        Bethe.trigTerm (fun _ => 0) (tauAbelCorrectionCoeff lam μ) n α := by
    intro n
    simp [tauAbelCorrectionTerm, tauAbelCorrectionCoeff, Bethe.trigTerm]
  calc
    (∑' n : ℕ, tauAbelCorrectionTerm lam μ α n) =
        ∑' n : ℕ, Bethe.trigTerm (fun _ => 0)
          (tauAbelCorrectionCoeff lam μ) n α := tsum_congr hterm
    _ = Bethe.trigSeries 0 (fun _ => 0) (tauAbelCorrectionCoeff lam μ) α := by
      simp [Bethe.trigSeries, Bethe.trigTerm]

private theorem continuous_tauAbelCorrection {lam μ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) :
    Continuous (fun α => ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n) := by
  have hcont : Continuous
      (Bethe.trigSeries 0 (fun _ => 0) (tauAbelCorrectionCoeff lam μ)) :=
    Bethe.continuous_trigSeries summable_zero
      (summable_tauAbelCorrectionCoeff hlam hμ) 0
  have heq :
      (fun α => ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n) =
        Bethe.trigSeries 0 (fun _ => 0) (tauAbelCorrectionCoeff lam μ) := by
    funext α
    exact tauAbelCorrection_eq_trigSeries
  rw [heq]
  exact hcont

private theorem continuous_tauAbel {lam μ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) :
    Continuous (tauAbel lam μ) := by
  have hsaw : Continuous (Bethe.sawS μ) :=
    continuous_iff_continuousAt.mpr fun α =>
      (Bethe.hasDerivAt_sawS hμ α).continuousAt
  have hcorr := continuous_tauAbelCorrection hlam hμ
  have heq : tauAbel lam μ = fun α =>
      (1 / (2 * π) : ℝ) * Bethe.sawS μ α +
        ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n := by
    funext α
    exact tauAbel_eq_sawS_add_correction hlam hμ
  rw [heq]
  exact (continuous_const.mul hsaw).add hcorr

private theorem measurable_fourierPPrime (lam : ℝ) :
    Measurable (fourierPPrime lam) := by
  unfold fourierPPrime
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

 noncomputable def tauLocalControl (lam : ℝ) : ℝ :=
  1 / π + (1 / (2 * π)) * tauCoeffWeightedSum lam

 noncomputable def tauGlobalControl (lam : ℝ) : ℝ :=
  1 / 2 + (1 / 2) * tauCoeffWeightedSum lam

private theorem tauCoeffWeightedSum_nonneg {lam : ℝ} :
    0 ≤ tauCoeffWeightedSum lam := by
  unfold tauCoeffWeightedSum
  apply tsum_nonneg
  intro n
  positivity

private theorem tauLocalControl_nonneg {lam : ℝ} :
    0 ≤ tauLocalControl lam := by
  have hW := tauCoeffWeightedSum_nonneg (lam := lam)
  dsimp [tauLocalControl]
  positivity

private theorem tauGlobalControl_nonneg {lam : ℝ} :
    0 ≤ tauGlobalControl lam := by
  have hW := tauCoeffWeightedSum_nonneg (lam := lam)
  dsimp [tauGlobalControl]
  positivity

private theorem tauAbel_local_abs_bound {lam μ α : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hα : |α| ≤ π / 2) :
    |tauAbel lam μ α| ≤ tauLocalControl lam * |α| := by
  let c : ℝ := 1 / (2 * π)
  have hc : 0 < c := by dsimp [c]; positivity
  have hdecomp := tauAbel_eq_sawS_add_correction
    (lam := lam) (μ := μ) (α := α) hlam hμ
  have hsaw := sawS_abs_le_two_mul_abs (μ := μ) (α := α) hμ hα
  have hcorr := tauAbelCorrection_abs_bound (lam := lam) (μ := μ) (α := α) hlam hμ
  have hfirst : |c * Bethe.sawS μ α| ≤ c * (2 * |α|) := by
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hsaw hc.le
  calc
    |tauAbel lam μ α| =
        |c * Bethe.sawS μ α + ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| := by
          rw [hdecomp]
    _ ≤ |c * Bethe.sawS μ α| +
        |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| := abs_add_le _ _
    _ ≤ c * (2 * |α|) + c * |α| * tauCoeffWeightedSum lam :=
        add_le_add hfirst (by simpa [c] using hcorr)
    _ = tauLocalControl lam * |α| := by
        dsimp [tauLocalControl, c]
        field_simp [Real.pi_ne_zero]

private theorem tauAbel_global_abs_bound {lam μ α : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hα : α ∈ Icc (-π) π) :
    |tauAbel lam μ α| ≤ tauGlobalControl lam := by
  let c : ℝ := 1 / (2 * π)
  have hc : 0 < c := by dsimp [c]; positivity
  have hW := tauCoeffWeightedSum_nonneg (lam := lam)
  have hαabs : |α| ≤ π := abs_le.mpr ⟨by linarith [hα.1], hα.2⟩
  have hdecomp := tauAbel_eq_sawS_add_correction
    (lam := lam) (μ := μ) (α := α) hlam hμ
  have hsaw := sawS_abs_le_pi (μ := μ) (α := α) hμ
  have hcorr := tauAbelCorrection_abs_bound (lam := lam) (μ := μ) (α := α) hlam hμ
  have hcorr' :
      |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| ≤ c * π *
        tauCoeffWeightedSum lam := by
    calc
      |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| ≤
          c * |α| * tauCoeffWeightedSum lam := by simpa [c] using hcorr
      _ ≤ c * π * tauCoeffWeightedSum lam := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hαabs hc.le) hW
  calc
    |tauAbel lam μ α| =
        |c * Bethe.sawS μ α + ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| := by
          rw [hdecomp]
    _ ≤ |c * Bethe.sawS μ α| +
        |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| := abs_add_le _ _
    _ ≤ c * π + c * π * tauCoeffWeightedSum lam := by
        apply add_le_add
        · rw [abs_mul, abs_of_pos hc]
          exact mul_le_mul_of_nonneg_left hsaw hc.le
        · exact hcorr'
    _ = tauGlobalControl lam := by
        dsimp [tauGlobalControl, c]
        field_simp [Real.pi_ne_zero]

noncomputable def fourierTauProductControl (lam : ℝ) : ℝ :=
  max (fourierPrimeControl lam * tauLocalControl lam)
    ((2 * fourierPrimeControl lam / π) * tauGlobalControl lam)

theorem fourierTauProductControl_nonneg {lam : ℝ} (hlam : 0 < lam) :
    0 ≤ fourierTauProductControl lam := by
  have hcosh : 1 < Real.cosh (2 * lam) := Real.one_lt_cosh.mpr (by positivity)
  have hprime : 0 < fourierPrimeControl lam := by
    dsimp [fourierPrimeControl]
    positivity
  have hlocal := tauLocalControl_nonneg (lam := lam)
  have hglobal := tauGlobalControl_nonneg (lam := lam)
  dsimp [fourierTauProductControl]
  positivity

private theorem fourierPPrime_mul_tauAbel_abs_bound {lam μ α : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α * tauAbel lam μ α| ≤ fourierTauProductControl lam := by
  have hprime := fourierPPrime_alpha_bound hlam hα
  have hprimeNonneg : 0 ≤ fourierPrimeControl lam := by
    have hcosh : 1 < Real.cosh (2 * lam) := Real.one_lt_cosh.mpr (by positivity)
    dsimp [fourierPrimeControl]
    positivity
  have hlocal := tauLocalControl_nonneg (lam := lam)
  have hglobal := tauGlobalControl_nonneg (lam := lam)
  rw [abs_mul]
  by_cases hnear : |α| ≤ π / 2
  · have htau := tauAbel_local_abs_bound hlam hμ hnear
    calc
      |fourierPPrime lam α| * |tauAbel lam μ α| ≤
          |fourierPPrime lam α| * (tauLocalControl lam * |α|) :=
            mul_le_mul_of_nonneg_left htau (abs_nonneg _)
      _ = tauLocalControl lam *
          (|fourierPPrime lam α| * |α|) := by ring
      _ ≤ tauLocalControl lam * fourierPrimeControl lam :=
            mul_le_mul_of_nonneg_left hprime hlocal
      _ = fourierPrimeControl lam * tauLocalControl lam := mul_comm _ _
      _ ≤ fourierTauProductControl lam := le_max_left _ _
  · have hfar : π / 2 ≤ |α| := le_of_not_ge hnear
    have hαabs : 0 < |α| := lt_of_lt_of_le (by positivity) hfar
    have hprimeDiv :
        |fourierPPrime lam α| ≤ fourierPrimeControl lam / |α| :=
      (le_div_iff₀ hαabs).2 (by simpa [mul_comm] using hprime)
    have hprimeFar :
        |fourierPPrime lam α| ≤ 2 * fourierPrimeControl lam / π := by
      calc
        |fourierPPrime lam α| ≤ fourierPrimeControl lam / |α| := hprimeDiv
        _ ≤ fourierPrimeControl lam / (π / 2) :=
            div_le_div_of_nonneg_left hprimeNonneg (by positivity) hfar
        _ = 2 * fourierPrimeControl lam / π := by
            field_simp [Real.pi_ne_zero]
    have htau := tauAbel_global_abs_bound hlam hμ hα
    calc
      |fourierPPrime lam α| * |tauAbel lam μ α| ≤
          |fourierPPrime lam α| * tauGlobalControl lam :=
            mul_le_mul_of_nonneg_left htau (abs_nonneg _)
      _ ≤ (2 * fourierPrimeControl lam / π) * tauGlobalControl lam :=
            mul_le_mul_of_nonneg_right hprimeFar hglobal
      _ ≤ fourierTauProductControl lam := le_max_right _ _

noncomputable def tauAbelSeq (lam α : ℝ) (N : ℕ) : ℝ :=
  tauAbel lam (1 / ((N : ℝ) + 1)) α

private theorem tauAbelSeq_tendsto_tauSeries {lam α : ℝ} (hlam : 0 < lam)
    (hα : |α| < π) : Tendsto (tauAbelSeq lam α) atTop (𝓝 (Bethe.tauSeries lam α)) := by
  let r : ℕ → ℝ := fun N => Real.exp (-(1 / ((N : ℝ) + 1)))
  have hsmall : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hneg : Tendsto (fun N : ℕ => -(1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using hsmall.neg
  have hr0 : Tendsto r atTop (𝓝 1) := by
    have h := (Real.continuous_exp.continuousAt.tendsto).comp hneg
    simpa only [r, Function.comp_def, Real.exp_zero] using h
  have hrlt : ∀ N : ℕ, r N < 1 := by
    intro N
    rw [show r N = Real.exp (-(1 / ((N : ℝ) + 1))) from rfl,
      Real.exp_lt_one_iff]
    have hpos : 0 < 1 / ((N : ℝ) + 1) := by positivity
    linarith
  have hr : Tendsto r atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr0, Filter.Eventually.of_forall hrlt⟩
  have hpartial : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, tauFourierTerm lam α n) atTop
      (𝓝 (Bethe.tauSeries lam α)) := by
    have h := Bethe.tendsto_tauPartial hlam hα
    have hvalue := Bethe.tauSeries_eq hlam hα
    rw [← hvalue] at h
    have hsum : (fun N : ℕ => ∑ n ∈ Finset.range N, tauFourierTerm lam α n) =
        Bethe.tauPartial lam α := by
      funext N
      simp [tauFourierTerm, Bethe.tauPartial]
    rw [hsum]
    exact h
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hpartial
  have habelSeq := habel.comp hr
  have hmul := (tendsto_nhds_of_tendsto_nhdsWithin hr).mul habelSeq
  have hpoint (N : ℕ) : tauAbelSeq lam α N =
      r N * ∑' n : ℕ, tauFourierTerm lam α n * r N ^ n := by
    rw [tauAbelSeq, tauAbel]
    calc
      (∑' n : ℕ, tauFourierTerm lam α n * Real.exp (-(1 / ((N : ℝ) + 1))) ^ (n + 1)) =
          ∑' n : ℕ, r N * (tauFourierTerm lam α n * r N ^ n) := by
            refine tsum_congr fun n => ?_
            dsimp [r]
            rw [pow_succ]
            ring
      _ = r N * ∑' n : ℕ, tauFourierTerm lam α n * r N ^ n := tsum_mul_left
  have hmul' : Tendsto (fun N : ℕ =>
      r N * ∑' n : ℕ, tauFourierTerm lam α n * r N ^ n) atTop
      (𝓝 (1 * Bethe.tauSeries lam α)) := hmul
  have hseq : (fun N : ℕ => tauAbelSeq lam α N) =
      fun N => r N * ∑' n : ℕ, tauFourierTerm lam α n * r N ^ n := by
    funext N
    exact hpoint N
  rw [← hseq] at hmul'
  simpa using hmul'

/-- A uniform bound for the product of the punctured derivative and the literal `τ` series.
The estimate is first proved for Abel means and then passed to their pointwise limit; the two
endpoints use the literal series value zero. -/
theorem fourierPPrime_tauSeries_abs_bound {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α * Bethe.tauSeries lam α| ≤ fourierTauProductControl lam := by
  by_cases hαp : α = π
  · subst α
    calc
      |fourierPPrime lam π * Bethe.tauSeries lam π| = 0 := by
        simp [Bethe.tauSeries_pi]
      _ ≤ fourierTauProductControl lam := fourierTauProductControl_nonneg hlam
  by_cases hαm : α = -π
  · subst α
    calc
      |fourierPPrime lam (-π) * Bethe.tauSeries lam (-π)| = 0 := by
        simp [Bethe.tauSeries_neg_pi]
      _ ≤ fourierTauProductControl lam := fourierTauProductControl_nonneg hlam
  have hαabs : |α| < π := abs_lt.mpr
    ⟨lt_of_le_of_ne hα.1 (Ne.symm hαm), lt_of_le_of_ne hα.2 hαp⟩
  have htau := tauAbelSeq_tendsto_tauSeries hlam hαabs
  have hmul : Tendsto
      (fun N : ℕ => fourierPPrime lam α * tauAbelSeq lam α N) atTop
      (𝓝 (fourierPPrime lam α * Bethe.tauSeries lam α)) := by
    exact (show Tendsto (fun _ : ℕ => fourierPPrime lam α) atTop
        (𝓝 (fourierPPrime lam α)) from tendsto_const_nhds).mul htau
  have hprod : Tendsto
      (fun N : ℕ => |fourierPPrime lam α * tauAbelSeq lam α N|) atTop
      (𝓝 |fourierPPrime lam α * Bethe.tauSeries lam α|) := by
    simpa only [Real.norm_eq_abs] using hmul.norm
  apply le_of_tendsto_of_tendsto' hprod tendsto_const_nhds
  intro N
  have hμ : 0 < 1 / ((N : ℝ) + 1) := by positivity
  simpa [tauAbelSeq, abs_mul] using
    (fourierPPrime_mul_tauAbel_abs_bound hlam hμ hα)

private theorem tauFourierTerm_abs_bound (lam α : ℝ) (n : ℕ) :
    |tauFourierTerm lam α n| ≤ |α| / π := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hsign : |(-1 : ℝ) ^ (n + 1)| = 1 := by simp
  have hden : |π * ((n : ℝ) + 1)| = π * ((n : ℝ) + 1) :=
    abs_of_pos (mul_pos Real.pi_pos hm)
  have hcoeff :
      |(-1 : ℝ) ^ (n + 1) / (π * ((n : ℝ) + 1))| =
        1 / (π * ((n : ℝ) + 1)) := by rw [abs_div, hsign, hden]
  have htanh :
      |Real.tanh (lam * ((n + 1 : ℕ) : ℝ))| ≤ 1 :=
    (Real.abs_tanh_lt_one _).le
  have hsin :
      |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤ ((n : ℝ) + 1) * |α| := by
    calc
      |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤
          |((n + 1 : ℕ) : ℝ) * α| := Real.abs_sin_le_abs
      _ = ((n : ℝ) + 1) * |α| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          congr 1
          push_cast
          ring
  rw [tauFourierTerm, abs_mul, abs_mul, hcoeff]
  calc
    (1 / (π * ((n : ℝ) + 1))) *
        |Real.tanh (lam * ((n + 1 : ℕ) : ℝ))| *
        |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤
      (1 / (π * ((n : ℝ) + 1))) * 1 *
        (((n : ℝ) + 1) * |α|) := by
          gcongr
    _ = |α| / π := by
      field_simp [Real.pi_ne_zero]

private theorem summable_tauAbelTerms {lam μ α : ℝ}
    (hμ : 0 < μ) :
    Summable (fun n : ℕ => tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1)) := by
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hr1 : Real.exp (-μ) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeo : Summable (fun n : ℕ => Real.exp (-μ) ^ (n + 1)) := by
    have h := (summable_geometric_of_lt_one hr.le hr1).mul_left (Real.exp (-μ))
    refine h.congr fun n => ?_
    rw [pow_succ]
    ring
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => (|α| / π) * Real.exp (-μ) ^ (n + 1))
    (hgeo.mul_left (|α| / π))
  intro n
  have hpow : 0 ≤ Real.exp (-μ) ^ (n + 1) := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
  exact mul_le_mul_of_nonneg_right (tauFourierTerm_abs_bound lam α n) hpow

private theorem hasSum_tauAbelTerms {lam μ α : ℝ}
    (hμ : 0 < μ) :
    HasSum (fun n : ℕ => tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1))
      (tauAbel lam μ α) := by
  simpa [tauAbel] using (summable_tauAbelTerms hμ).hasSum

noncomputable def tauCorrectionTerm (lam : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) *
    Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) *
      (Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) - 1)

private theorem tauAbel_integral_term {lam μ : ℝ} (hlam : 0 < lam)
    (n : ℕ) :
    ∫ α in (-π)..π,
        fourierPPrime lam α * tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1) =
      tauCorrectionTerm lam n * Real.exp (-μ) ^ (n + 1) := by
  have hm : 0 < n + 1 := Nat.succ_pos n
  have hmR : 0 < ((n : ℝ) + 1) := by positivity
  have hsine := fourierP_prime_sine_integral hlam (n + 1) hm
  have hsine' :
      ∫ α in (-π)..π, fourierPPrime lam α *
          Real.sin (((n + 1 : ℕ) : ℝ) * α) =
        π * (Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) - 1) := by
    calc
      _ = π * ((1 / π : ℝ) *
          ∫ α in (-π)..π, fourierPPrime lam α *
            Real.sin (((n + 1 : ℕ) : ℝ) * α)) := by field_simp [Real.pi_ne_zero]
      _ = _ := by rw [hsine]
  have hfun :
      (fun α : ℝ => fourierPPrime lam α * tauFourierTerm lam α n *
          Real.exp (-μ) ^ (n + 1)) =
        fun α =>
          (Real.exp (-μ) ^ (n + 1) *
            ((-1 : ℝ) ^ (n + 1) / (π * ((n : ℝ) + 1)) *
              Real.tanh (lam * ((n + 1 : ℕ) : ℝ)))) *
            (fourierPPrime lam α * Real.sin (((n + 1 : ℕ) : ℝ) * α)) := by
    funext α
    simp [tauFourierTerm]
    ring
  rw [hfun, intervalIntegral.integral_const_mul, hsine']
  dsimp [tauCorrectionTerm]
  have hmne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hmR
  field_simp [Real.pi_ne_zero, hmne]

private theorem fourierPPrime_tauAbel_integral {lam μ : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) :
    ∫ α in (-π)..π, fourierPPrime lam α * tauAbel lam μ α =
      ∑' n : ℕ, tauCorrectionTerm lam n * Real.exp (-μ) ^ (n + 1) := by
  let r : ℝ := Real.exp (-μ)
  let B : ℕ → ℝ := fun n => (fourierPrimeControl lam / π) * r ^ (n + 1)
  let F : ℕ → ℝ → ℝ := fun n α =>
    fourierPPrime lam α * tauFourierTerm lam α n * r ^ (n + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hprimePos : 0 < fourierPrimeControl lam := by
    have hcosh : 1 < Real.cosh (2 * lam) := Real.one_lt_cosh.mpr (by positivity)
    dsimp [fourierPrimeControl]
    positivity
  have hgeo : Summable (fun n : ℕ => r ^ (n + 1)) := by
    have h := (summable_geometric_of_lt_one hr.le hr1).mul_left r
    refine h.congr fun n => ?_
    rw [pow_succ]
    ring
  have hB : Summable B := by
    dsimp [B]
    exact hgeo.mul_left (fourierPrimeControl lam / π)
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (F n) (volume.restrict (uIoc (-π) π)) := by
    intro n
    have hcont : Measurable (fun α : ℝ => tauFourierTerm lam α n) := by
      unfold tauFourierTerm
      fun_prop
    have hF : Measurable (F n) := by
      dsimp [F]
      exact (measurable_fourierPPrime lam).mul hcont |>.mul measurable_const
    exact hF.aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ α ∂volume, α ∈ uIoc (-π) π →
      ‖F n α‖ ≤ B n := by
    intro n
    filter_upwards with α
    intro hα
    have hαIoc : α ∈ Ioc (-π) π := by
      simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
    have hIcc : α ∈ Icc (-π) π := Ioc_subset_Icc_self hαIoc
    have hP := fourierPPrime_alpha_bound hlam hIcc
    have hterm := tauFourierTerm_abs_bound lam α n
    have hcoeff :
        |fourierPPrime lam α| * |tauFourierTerm lam α n| ≤
          fourierPrimeControl lam / π := by
      calc
        |fourierPPrime lam α| * |tauFourierTerm lam α n| ≤
            |fourierPPrime lam α| * (|α| / π) :=
              mul_le_mul_of_nonneg_left hterm (abs_nonneg _)
        _ = (|fourierPPrime lam α| * |α|) / π := by ring
        _ ≤ fourierPrimeControl lam / π :=
              div_le_div_of_nonneg_right hP (le_of_lt Real.pi_pos)
    have hpow : 0 ≤ r ^ (n + 1) := by positivity
    change ‖fourierPPrime lam α * tauFourierTerm lam α n * r ^ (n + 1)‖ ≤
      (fourierPrimeControl lam / π) * r ^ (n + 1)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hpow]
    exact mul_le_mul_of_nonneg_right hcoeff hpow
  have hlim : ∀ᵐ α ∂volume, α ∈ uIoc (-π) π →
      HasSum (fun n : ℕ => F n α)
        (fourierPPrime lam α * tauAbel lam μ α) := by
    refine Filter.Eventually.of_forall fun α _ => ?_
    have hs := (hasSum_tauAbelTerms (lam := lam) (μ := μ) (α := α) hμ).mul_left
      (fourierPPrime lam α)
    refine HasSum.congr_fun hs fun n => ?_
    simp [F, r]
    ring
  have hboundInt :
      IntervalIntegrable (fun α : ℝ => ∑' n : ℕ, B n) volume (-π) π := by
    have hconst : (fun α : ℝ => ∑' n : ℕ, B n) = fun _ => ∑' n : ℕ, B n := by
      funext α
      rfl
    rw [hconst]
    exact intervalIntegrable_const
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := F)
    (f := fun α => fourierPPrime lam α * tauAbel lam μ α)
    (fun n α => B n) hmeas hbound
    (Filter.Eventually.of_forall fun α _ => hB) hboundInt hlim
  have hsum' := hsum.tsum_eq
  have hterm : ∀ n : ℕ, ∫ α in (-π)..π, F n α =
      tauCorrectionTerm lam n * Real.exp (-μ) ^ (n + 1) := by
    intro n
    change ∫ α in (-π)..π,
        fourierPPrime lam α * tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1) = _
    exact tauAbel_integral_term hlam n
  rw [← hsum']
  exact tsum_congr hterm

noncomputable def tauCorrectionPartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, tauCorrectionTerm lam n

private theorem tauCorrectionPartial_eq (lam : ℝ) (N : ℕ) :
    tauCorrectionPartial lam N =
      logCoshTauCorrectionPartial lam N := by
  have hfin : Finset.Icc 1 N = (Finset.range N).image Nat.succ := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hm1, hmN⟩
      refine ⟨m - 1, ?_, ?_⟩ <;> omega
    · rintro ⟨n, hn, rfl⟩
      omega
  unfold tauCorrectionPartial logCoshTauCorrectionPartial
  rw [hfin, Finset.sum_image]
  · congr 1
    funext n
    dsimp [tauCorrectionTerm]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    ring_nf
  · intro i hi j hj hij
    exact Nat.succ.inj hij

noncomputable def tauCorrectionAbelSeq (lam : ℝ) (N : ℕ) : ℝ :=
  ∑' n : ℕ, tauCorrectionTerm lam n *
    Real.exp (-(1 / ((N : ℝ) + 1))) ^ (n + 1)

private theorem tauCorrectionAbelSeq_tendsto {lam L : ℝ}
    (hpartial : Tendsto (tauCorrectionPartial lam) atTop (𝓝 L)) :
    Tendsto (tauCorrectionAbelSeq lam) atTop (𝓝 L) := by
  let r : ℕ → ℝ := fun N => Real.exp (-(1 / ((N : ℝ) + 1)))
  have hsmall : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hneg : Tendsto (fun N : ℕ => -(1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using hsmall.neg
  have hr0 : Tendsto r atTop (𝓝 1) := by
    have h := (Real.continuous_exp.continuousAt.tendsto).comp hneg
    simpa only [r, Function.comp_def, Real.exp_zero] using h
  have hrlt : ∀ N : ℕ, r N < 1 := by
    intro N
    rw [show r N = Real.exp (-(1 / ((N : ℝ) + 1))) from rfl,
      Real.exp_lt_one_iff]
    have hpos : 0 < 1 / ((N : ℝ) + 1) := by positivity
    linarith
  have hr : Tendsto r atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr0, Filter.Eventually.of_forall hrlt⟩
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun n => tauCorrectionTerm lam n) hpartial
  have habelSeq := habel.comp hr
  have habelSeq' : Tendsto
      (fun N : ℕ => ∑' n : ℕ, tauCorrectionTerm lam n * r N ^ n) atTop (𝓝 L) := by
    simpa [Function.comp_def] using habelSeq
  have hpoint (N : ℕ) : tauCorrectionAbelSeq lam N =
      r N * ∑' n : ℕ, tauCorrectionTerm lam n * r N ^ n := by
    rw [tauCorrectionAbelSeq]
    calc
      (∑' n : ℕ, tauCorrectionTerm lam n *
          Real.exp (-(1 / ((N : ℝ) + 1))) ^ (n + 1)) =
        ∑' n : ℕ, r N * (tauCorrectionTerm lam n * r N ^ n) := by
          refine tsum_congr fun n => ?_
          dsimp [r]
          rw [pow_succ]
          ring
      _ = r N * ∑' n : ℕ, tauCorrectionTerm lam n * r N ^ n := tsum_mul_left
  have hseq : (fun N : ℕ => tauCorrectionAbelSeq lam N) =
      fun N => r N * ∑' n : ℕ, tauCorrectionTerm lam n * r N ^ n := by
    funext N
    exact hpoint N
  have hmul := hr0.mul habelSeq'
  rw [← hseq] at hmul
  simpa using hmul

private theorem tauCorrectionAbelSeq_tendsto_value {lam : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ, Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (tauCorrectionPartial lam) atTop
        (𝓝 (Real.log (Real.cosh lam) - (lam + 2 * S))) ∧
      Tendsto (tauCorrectionAbelSeq lam) atTop
        (𝓝 (Real.log (Real.cosh lam) - (lam + 2 * S))) := by
  obtain ⟨S, hS, hidentity⟩ := identity43 lam hlam
  have hCorr : Tendsto (logCoshTauCorrectionPartial lam) atTop
      (𝓝 (Real.log (Real.cosh lam) - (lam + 2 * S))) := by
    have hconst : Tendsto (fun _ : ℕ => Real.log (Real.cosh lam)) atTop
        (𝓝 (Real.log (Real.cosh lam))) := tendsto_const_nhds
    have hsub := hconst.sub hidentity
    apply hsub.congr'
    filter_upwards [] with N
    ring
  have hpartial : Tendsto (tauCorrectionPartial lam) atTop
      (𝓝 (Real.log (Real.cosh lam) - (lam + 2 * S))) := by
    exact hCorr.congr' (Filter.Eventually.of_forall fun N =>
      (tauCorrectionPartial_eq lam N).symm)
  exact ⟨S, hS, hpartial, tauCorrectionAbelSeq_tendsto hpartial⟩

/-- The `α`-coordinate value of the explicit series integral in §4.  The correction series is
interpreted by its ordered partial sums; Abel damping identifies the integral with that limit. -/
theorem fourierPPrime_tauSeries_integral {lam : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (logCoshTauCorrectionPartial lam) atTop
        (𝓝 (∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α)) := by
  obtain ⟨S, hS, hPartialCorr, hAbelCorr⟩ := tauCorrectionAbelSeq_tendsto_value hlam
  let F : ℕ → ℝ → ℝ := fun N α => fourierPPrime lam α * tauAbelSeq lam α N
  have hmeas : ∀ N : ℕ,
      AEStronglyMeasurable (F N) (volume.restrict (uIoc (-π) π)) := by
    intro N
    have hμ : 0 < 1 / ((N : ℝ) + 1) := by positivity
    have hcont : Continuous (fun α : ℝ => tauAbel lam (1 / ((N : ℝ) + 1)) α) :=
      continuous_tauAbel hlam hμ
    have hF : Measurable (F N) := by
      dsimp [F, tauAbelSeq]
      exact (measurable_fourierPPrime lam).mul hcont.measurable
    exact hF.aestronglyMeasurable
  have hbound : ∀ N : ℕ, ∀ᵐ α ∂volume, α ∈ uIoc (-π) π →
      ‖F N α‖ ≤ fourierTauProductControl lam := by
    intro N
    filter_upwards with α
    intro hα
    have hαIoc : α ∈ Ioc (-π) π := by
      simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
    have hαIcc : α ∈ Icc (-π) π := Ioc_subset_Icc_self hαIoc
    have hμ : 0 < 1 / ((N : ℝ) + 1) := by positivity
    change ‖fourierPPrime lam α *
        tauAbel lam (1 / ((N : ℝ) + 1)) α‖ ≤ fourierTauProductControl lam
    rw [Real.norm_eq_abs]
    exact fourierPPrime_mul_tauAbel_abs_bound hlam hμ hαIcc
  have hboundInt :
      IntervalIntegrable (fun _ : ℝ => fourierTauProductControl lam) volume (-π) π :=
    intervalIntegrable_const
  have hlim : ∀ᵐ α ∂volume, α ∈ uIoc (-π) π →
      Tendsto (fun N : ℕ => F N α) atTop
        (𝓝 (fourierPPrime lam α * Bethe.tauSeries lam α)) := by
    filter_upwards [Measure.ae_ne volume π] with α hαπ
    intro hα
    have hαIoc : α ∈ Ioc (-π) π := by
      simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
    have hright : α < π := lt_of_le_of_ne hαIoc.2 hαπ
    have hαabs : |α| < π := abs_lt.mpr ⟨by linarith [hαIoc.1], hright⟩
    have htau := tauAbelSeq_tendsto_tauSeries hlam hαabs
    simpa [F, tauAbelSeq] using (tendsto_const_nhds.mul htau)
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := F)
    (f := fun α => fourierPPrime lam α * Bethe.tauSeries lam α)
    (fun _ : ℝ => fourierTauProductControl lam)
    (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbound)
    hboundInt hlim
  have hpoint (N : ℕ) :
      ∫ α in (-π)..π, F N α = tauCorrectionAbelSeq lam N := by
    change ∫ α in (-π)..π,
      fourierPPrime lam α * tauAbel lam (1 / ((N : ℝ) + 1)) α = _
    rw [fourierPPrime_tauAbel_integral hlam (by positivity)]
    dsimp [tauCorrectionAbelSeq]
  have hseqEq : (fun N : ℕ => ∫ α in (-π)..π, F N α) = tauCorrectionAbelSeq lam := by
    funext N
    exact hpoint N
  have hDCT' : Tendsto (tauCorrectionAbelSeq lam) atTop
      (𝓝 (∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α)) := by
    rw [hseqEq] at hDCT
    exact hDCT
  have hvalue := tendsto_nhds_unique hDCT' hAbelCorr
  have hCorr : Tendsto (logCoshTauCorrectionPartial lam) atTop
      (𝓝 (∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α)) := by
    have hCorr' := hPartialCorr.congr'
      (Filter.Eventually.of_forall fun N => tauCorrectionPartial_eq lam N)
    simpa [hvalue] using hCorr'
  exact ⟨S, hS, hCorr⟩

end PottsDiscontinuity
