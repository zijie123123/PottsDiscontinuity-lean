module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# Corollary 3.4: normalized Bethe eigenvalue

The inverse parameter is `ε = 1/Δ`.  The normalized `L` and `M` factors below are the
continuous extensions of `L/(-2Δ)` and `M/(-2Δ)`.  In the odd case, the derivative in the
zero-root eigenvalue formula is written in a rational form that is continuous at `ε=0`.
-/

@[expose] public section

open Finset Complex Filter Topology
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

/-- The derivative of the Bethe phase in its first variable, evaluated at zero. -/
theorem cor34_deriv_theta_at_zero {Δ y : ℝ} (hΔ : Δ < -1) :
    deriv (fun t : ℝ => Bethe.theta Δ t y) 0 =
      -1 + 2 * (1 + Real.cos y - 2 * Δ) /
        ((1 + Real.cos y - 2 * Δ) ^ 2 + (Real.sin y) ^ 2) := by
  let d : ℝ := 1 + Real.cos y - 2 * Δ
  have hd : 0 < d := by
    have hy := Real.neg_one_le_cos y
    dsimp [d]
    linarith
  have hnum : HasDerivAt (fun t : ℝ => Real.sin t - Real.sin y) 1 0 := by
    simpa using (Real.hasDerivAt_sin 0).sub_const (Real.sin y)
  have hcos : HasDerivAt (fun t : ℝ => Real.cos t) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0)
  have hcosY : HasDerivAt (fun _ : ℝ => Real.cos y) (0 : ℝ) 0 :=
    hasDerivAt_const (0 : ℝ) (Real.cos y)
  have hden : HasDerivAt
      (fun t : ℝ => Real.cos t + Real.cos y - 2 * Δ) 0 0 := by
    convert (hcos.add hcosY).sub_const (2 * Δ) using 1; ring
  have hdenPos : 0 < Real.cos 0 + Real.cos y - 2 * Δ := by
    rw [Real.cos_zero]
    simpa [d] using hd
  have hDpos : 0 < 1 + Real.cos y - 2 * Δ := by
    simpa [d] using hd
  have hfrac : HasDerivAt
      (fun t : ℝ => (Real.sin t - Real.sin y) /
        (Real.cos t + Real.cos y - 2 * Δ)) (1 / d) 0 := by
    have h := hnum.div hden (ne_of_gt hdenPos)
    convert h using 1
    rw [Real.sin_zero, Real.cos_zero]
    change 1 / d = (1 * d - (0 - Real.sin y) * 0) / d ^ 2
    field_simp [ne_of_gt hDpos]; ring
  have htan := (Real.hasDerivAt_arctan ((Real.sin 0 - Real.sin y) /
      (Real.cos 0 + Real.cos y - 2 * Δ))).comp 0 hfrac
  have htan' : HasDerivAt
      (fun t : ℝ => Real.arctan ((Real.sin t - Real.sin y) /
        (Real.cos t + Real.cos y - 2 * Δ)))
      (1 / (1 + ((Real.sin 0 - Real.sin y) /
          (Real.cos 0 + Real.cos y - 2 * Δ)) ^ 2) * (1 / d)) 0 := by
    convert htan using 1; rfl
  have hlin : HasDerivAt (fun t : ℝ => y - t) (-1) 0 := by
    convert (hasDerivAt_const 0 y).sub (hasDerivAt_id 0) using 1
    · ext t
      rfl
    · norm_num
  have htheta : HasDerivAt (fun t : ℝ => Bethe.theta Δ t y)
      (-1 + 2 * (1 / (1 + ((Real.sin 0 - Real.sin y) /
          (Real.cos 0 + Real.cos y - 2 * Δ)) ^ 2) * (1 / d))) 0 := by
    unfold Bethe.theta
    convert hlin.add (htan'.const_mul 2) using 1
  have hderiv := htheta.deriv
  rw [Real.sin_zero, Real.cos_zero] at hderiv
  have hEq :
      (1 / (1 + ((-Real.sin y) / d) ^ 2) * (1 / d)) =
        d / (d ^ 2 + (Real.sin y) ^ 2) := by
    field_simp [ne_of_gt hd]
  have hderiv' : deriv (fun t : ℝ => Bethe.theta Δ t y) 0 =
      -1 + 2 * (1 / (1 + ((-Real.sin y) / d) ^ 2) * (1 / d)) := by
    simpa [d] using hderiv
  rw [hEq] at hderiv'
  convert hderiv' using 1; ring

/-- The rational continuation of the derivative correction in the odd zero-root formula. -/
noncomputable def cor34_derivativeCorrection (ε y : ℝ) : ℝ :=
  2 * ε * (ε * (1 + Real.cos y) - 2) /
    ((ε * (1 + Real.cos y) - 2) ^ 2 + ε ^ 2 * (Real.sin y) ^ 2)

/-- Continuous normalized regular `L` factor. -/
noncomputable def cor34_normalizedL (ε x : ℝ) : ℂ :=
  (((-ε / 2 : ℝ) : ℂ)) + ((1 - ε : ℝ) : ℂ) *
    BetheAnsatz.z x / (1 - BetheAnsatz.z x)

/-- Continuous normalized regular `M` factor. -/
noncomputable def cor34_normalizedM (ε x : ℝ) : ℂ :=
  (((-ε / 2 : ℝ) : ℂ)) - ((1 - ε : ℝ) : ℂ) /
    (1 - BetheAnsatz.z x)

/-- Regular eigenvalue expression after division by `(-2Δ)^n`. -/
noncomputable def cor34_normalizedRegularEigenvalue {n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ) : ℂ :=
  (∏ j : Fin n, cor34_normalizedL ε (p j)) +
    ∏ j : Fin n, cor34_normalizedM ε (p j)

/-- Odd zero-root eigenvalue expression after division by `(-2Δ)^n`. -/
noncomputable def cor34_normalizedZeroEigenvalue {N n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ) (l : Fin n) : ℂ :=
  (((-ε : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) *
      ((N : ℝ) - 1 + ∑ j ∈ Finset.univ.erase l,
        (-1 + cor34_derivativeCorrection ε (p j)))) *
    ∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j)

private theorem cor34_momentum_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (j : Fin n) :
    Tendsto (fun ε => BetheAnsatz.z (p ε j)) (𝓝 0)
      (𝓝 (BetheAnsatz.z (p 0 j))) := by
  have heval : ContinuousAt (fun q : Fin n → ℝ => q j) (p 0) :=
    (continuous_apply j).continuousAt
  have hpj : Tendsto (fun ε => p ε j) (𝓝 0) (𝓝 (p 0 j)) :=
    heval.tendsto.comp hp
  have hz : Continuous (fun x : ℝ => BetheAnsatz.z x) := by
    dsimp [BetheAnsatz.z]
    fun_prop
  exact hz.continuousAt.tendsto.comp hpj

/-- The normalized regular `L` factor has the source limit at any nonzero base momentum. -/
theorem cor34_normalizedL_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (j : Fin n) (hz : BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedL ε (p ε j)) (𝓝 0)
      (𝓝 (BetheAnsatz.z (p 0 j) / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hZ := cor34_momentum_tendsto hp j
  have hDen : Tendsto (fun ε : ℝ => (1 : ℂ) - BetheAnsatz.z (p ε j))
      (𝓝 0) (𝓝 (1 - BetheAnsatz.z (p 0 j))) := tendsto_const_nhds.sub hZ
  have hDen0 : 1 - BetheAnsatz.z (p 0 j) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hQuot := hZ.div hDen hDen0
  have hScale : Tendsto (fun ε : ℝ => (((-ε / 2 : ℝ) : ℂ))) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => (((-ε / 2 : ℝ) : ℂ))) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hOneMinus : Tendsto (fun ε : ℝ => (((1 - ε : ℝ) : ℂ))) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun ε : ℝ => (((1 - ε : ℝ) : ℂ))) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hsum := hScale.add (hOneMinus.mul hQuot)
  simpa [cor34_normalizedL, div_eq_mul_inv, mul_assoc] using hsum

/-- The normalized regular `M` factor has the source limit at any nonzero base momentum. -/
theorem cor34_normalizedM_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (j : Fin n) (hz : BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedM ε (p ε j)) (𝓝 0)
      (𝓝 (-1 / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hZ := cor34_momentum_tendsto hp j
  have hDen : Tendsto (fun ε : ℝ => (1 : ℂ) - BetheAnsatz.z (p ε j))
      (𝓝 0) (𝓝 (1 - BetheAnsatz.z (p 0 j))) := tendsto_const_nhds.sub hZ
  have hDen0 : 1 - BetheAnsatz.z (p 0 j) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hOne : Tendsto (fun _ : ℝ => (1 : ℂ)) (𝓝 0) (𝓝 (1 : ℂ)) := tendsto_const_nhds
  have hRecip := hOne.div hDen hDen0
  have hScale : Tendsto (fun ε : ℝ => (((-ε / 2 : ℝ) : ℂ))) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => (((-ε / 2 : ℝ) : ℂ))) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hOneMinus : Tendsto (fun ε : ℝ => (((1 - ε : ℝ) : ℂ))) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun ε : ℝ => (((1 - ε : ℝ) : ℂ))) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hsub := hScale.sub (hOneMinus.mul hRecip)
  simpa [cor34_normalizedM, div_eq_mul_inv, mul_assoc] using hsub

/-- The normalized regular eigenvalue converges for every continuous momentum family whose
base momenta avoid zero. -/
theorem cor34_normalizedRegularEigenvalue_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (hz : ∀ j, BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 ((∏ j : Fin n, BetheAnsatz.z (p 0 j) /
              (1 - BetheAnsatz.z (p 0 j))) +
            ∏ j : Fin n, (-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hL : Tendsto (fun ε => ∏ j : Fin n, cor34_normalizedL ε (p ε j))
      (𝓝 0) (𝓝 (∏ j : Fin n,
        BetheAnsatz.z (p 0 j) / (1 - BetheAnsatz.z (p 0 j)))) := by
    apply tendsto_finsetProd Finset.univ
    intro j hj
    exact cor34_normalizedL_tendsto hp j (hz j)
  have hM : Tendsto (fun ε => ∏ j : Fin n, cor34_normalizedM ε (p ε j))
      (𝓝 0) (𝓝 (∏ j : Fin n,
        (-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) := by
    apply tendsto_finsetProd Finset.univ
    intro j hj
    exact cor34_normalizedM_tendsto hp j (hz j)
  have hsum := hL.add hM
  simpa [cor34_normalizedRegularEigenvalue] using hsum

/-- The rational derivative correction in the odd zero-root formula vanishes continuously
as `ε → 0`, even when the other momenta vary with `ε`. -/
theorem cor34_derivativeCorrection_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (j : Fin n) :
    Tendsto (fun ε => cor34_derivativeCorrection ε (p ε j)) (𝓝 0) (𝓝 0) := by
  have heval : ContinuousAt (fun q : Fin n → ℝ => q j) (p 0) :=
    (continuous_apply j).continuousAt
  have hpj : Tendsto (fun ε => p ε j) (𝓝 0) (𝓝 (p 0 j)) :=
    heval.tendsto.comp hp
  have hcosFun : Continuous Real.cos := by fun_prop
  have hsinFun : Continuous Real.sin := by fun_prop
  have hcos := (hcosFun.continuousAt (x := p 0 j)).tendsto.comp hpj
  have hsin := (hsinFun.continuousAt (x := p 0 j)).tendsto.comp hpj
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0) := tendsto_id
  have hOneCos : Tendsto (fun ε : ℝ => 1 + Real.cos (p ε j)) (𝓝 0)
      (𝓝 (1 + Real.cos (p 0 j))) := tendsto_const_nhds.add hcos
  have hTwo : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝 0) (𝓝 2) := tendsto_const_nhds
  have hInner : Tendsto (fun ε : ℝ => ε * (1 + Real.cos (p ε j)) - 2)
      (𝓝 0) (𝓝 (-2)) := by
    simpa using (hε.mul hOneCos).sub hTwo
  have hSinSq : Tendsto (fun ε : ℝ => (Real.sin (p ε j)) ^ 2)
      (𝓝 0) (𝓝 (Real.sin (p 0 j) ^ 2)) := by
    simpa [pow_two] using hsin.mul hsin
  have hNum : Tendsto
      (fun ε : ℝ => 2 * ε * (ε * (1 + Real.cos (p ε j)) - 2))
      (𝓝 0) (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝 0) (𝓝 2) := tendsto_const_nhds
    simpa using (hconst.mul hε).mul hInner
  have hεsq : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 0) (𝓝 0) := by
    simpa [pow_two] using hε.mul hε
  have hDen : Tendsto
      (fun ε : ℝ => (ε * (1 + Real.cos (p ε j)) - 2) ^ 2 +
        ε ^ 2 * (Real.sin (p ε j)) ^ 2)
      (𝓝 0) (𝓝 (4 : ℝ)) := by
    have hInnerSq := by simpa [pow_two] using hInner.mul hInner
    have hProd := hεsq.mul hSinSq
    convert hInnerSq.add hProd using 1
    · ext ε
      simp [pow_two]
    · norm_num
  have hDen0 : (4 : ℝ) ≠ 0 := by norm_num
  have hquot := hNum.div hDen hDen0
  have hfun : (fun ε : ℝ =>
      (2 * ε * (ε * (1 + Real.cos (p ε j)) - 2)) /
        ((ε * (1 + Real.cos (p ε j)) - 2) ^ 2 +
          ε ^ 2 * (Real.sin (p ε j)) ^ 2)) =
      (fun ε : ℝ => 2 * ε * (ε * (1 + Real.cos (p ε j)) - 2)) /
        (fun ε : ℝ => (ε * (1 + Real.cos (p ε j)) - 2) ^ 2 +
          ε ^ 2 * (Real.sin (p ε j)) ^ 2) := by
    funext ε
    rfl
  rw [← hfun] at hquot
  simpa [cor34_derivativeCorrection] using hquot

/-- The normalized odd zero-root eigenvalue has the source limit for a continuous family when
the nonzero base roots avoid `z=1`. -/
theorem cor34_normalizedZeroEigenvalue_tendsto {N n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (l : Fin n)
    (hz : ∀ j ∈ Finset.univ.erase l, BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε) l) (𝓝 0)
      (𝓝 (((N : ℂ) - (n : ℂ)) *
        ∏ j ∈ Finset.univ.erase l,
          (-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hn : 0 < n := Nat.zero_lt_of_lt l.isLt
  have hDeriv (j : Fin n) (hj : j ∈ Finset.univ.erase l) :
      Tendsto (fun ε : ℝ => -1 + cor34_derivativeCorrection ε (p ε j))
        (𝓝 0) (𝓝 (-1 : ℝ)) := by
    have hc := cor34_derivativeCorrection_tendsto hp j
    simpa using (tendsto_const_nhds.add hc)
  have hSum : Tendsto
      (fun ε : ℝ => ∑ j ∈ Finset.univ.erase l,
        (-1 + cor34_derivativeCorrection ε (p ε j)))
      (𝓝 0) (𝓝 (-((n - 1 : ℕ) : ℝ))) := by
    have h := tendsto_finsetSum (Finset.univ.erase l) hDeriv
    have hcard : (Finset.univ.erase l).card = n - 1 := by simp
    simpa [Finset.sum_const, hcard, Nat.cast_sub (by omega : 1 ≤ n)] using h
  have hReal : Tendsto
      (fun ε : ℝ => (N : ℝ) - 1 +
        ∑ j ∈ Finset.univ.erase l,
          (-1 + cor34_derivativeCorrection ε (p ε j)))
      (𝓝 0) (𝓝 ((N : ℝ) - n)) := by
    have hconst : Tendsto (fun _ : ℝ => (N : ℝ) - 1) (𝓝 0) (𝓝 ((N : ℝ) - 1)) :=
      tendsto_const_nhds
    have h := hconst.add hSum
    have hlim : (N : ℝ) - 1 + -((n - 1 : ℕ) : ℝ) = (N : ℝ) - n := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    simpa only [hlim] using h
  have hcast : Tendsto
      (fun ε : ℝ => (((N : ℝ) - 1 +
        ∑ j ∈ Finset.univ.erase l,
          (-1 + cor34_derivativeCorrection ε (p ε j)) : ℝ) : ℂ))
      (𝓝 0) (𝓝 (((N : ℝ) - n : ℝ) : ℂ)) := by
    have hc : Continuous (fun x : ℝ => (x : ℂ)) := by fun_prop
    exact (hc.continuousAt (x := (N : ℝ) - n)).tendsto.comp hReal
  have hneg : Tendsto (fun ε : ℝ => ((-ε : ℝ) : ℂ)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ((-ε : ℝ) : ℂ)) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hOneMinus : Tendsto (fun ε : ℝ => (((1 - ε : ℝ) : ℂ))) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun ε : ℝ => (((1 - ε : ℝ) : ℂ))) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hfirst := hneg.add (hOneMinus.mul hcast)
  have hM : Tendsto
      (fun ε : ℝ => ∏ j ∈ Finset.univ.erase l,
        cor34_normalizedM ε (p ε j))
      (𝓝 0) (𝓝 (∏ j ∈ Finset.univ.erase l,
        (-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) := by
    apply tendsto_finsetProd (Finset.univ.erase l)
    intro j hj
    exact cor34_normalizedM_tendsto hp j (hz j hj)
  have hfinal := hfirst.mul hM
  simpa [cor34_normalizedZeroEigenvalue, div_eq_mul_inv, mul_assoc] using hfinal

end PottsDiscontinuity.SixVertex
