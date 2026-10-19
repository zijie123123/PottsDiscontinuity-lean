module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Scattering
public import PottsDiscontinuity.SixVertex.Cor34Analytic
public import PottsDiscontinuity.SixVertex.Cor34BetheEigenvalue
public import PottsDiscontinuity.SixVertex.Cor34FinalEquations

/-! # Corollary 3.4: analytic Bethe branches near the endpoint -/

@[expose] public section

open Filter Topology Set

namespace PottsDiscontinuity.SixVertex

private theorem cor34_final_analyticAt_coordinate {n : ℕ}
    {p : ℝ → Fin n → ℝ} {d d₁ : ℝ}
    (hp : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁) (j : Fin n) :
    AnalyticAt ℝ (fun t => p t j) d := by
  have hev : AnalyticAt ℝ (fun v : Fin n → ℝ => v j) (p d) := by
    convert (ContinuousLinearMap.proj (R := ℝ) j).analyticAt (p d) using 1
    ext v
    rfl
  exact hev.comp (hp d hd)

theorem cor34_final_analyticAt_ofReal {f : ℝ → ℝ} {d : ℝ}
    (hf : AnalyticAt ℝ f d) : AnalyticAt ℝ (fun t => (f t : ℂ)) d := by
  have hcast : AnalyticAt ℝ (Complex.ofRealCLM : ℝ → ℂ) (f d) :=
    (Complex.ofRealCLM).analyticAt (f d)
  change AnalyticAt ℝ (Complex.ofRealCLM ∘ f) d
  exact hcast.comp hf

/-- The branch has no zero roots and stays in the principal momentum interval on a slightly
larger interval than the physical range, when the root count is even. -/
theorem cor34_final_even_exists_regular_cutoff {n : ℕ}
    {d₀ d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < d₁) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n) (hn : Even n) :
    ∃ d₂, d₀ < d₂ ∧ d₂ < d₁ ∧
      ∀ d < d₂, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ p d j ≠ 0 := by
  have hp₀ : p d₀ ∈ Bethe.S_n n := hp d₀ le_rfl
  have hnonzero₀ : ∀ j, p d₀ j ≠ 0 :=
    fun j => cor34_even_S_n_roots_nonzero hp₀ hn j
  have hpCont : ContinuousAt p d₀ :=
    (hpAnalytic d₀ hd₀).continuousAt
  have hcoordinate (j : Fin n) :
      ∀ᶠ d in 𝓝 d₀, p d j ∈ Ioo (-Real.pi) Real.pi ∧ p d j ≠ 0 := by
    have hcont : ContinuousAt (fun d => p d j) d₀ :=
      (continuous_apply j).continuousAt.comp hpCont
    have hrange : ∀ᶠ d in 𝓝 d₀, p d j ∈ Ioo (-Real.pi) Real.pi :=
      hcont.eventually (isOpen_Ioo.mem_nhds (hp₀.1 j))
    exact hrange.and (hcont.eventually_ne (hnonzero₀ j))
  have hnear : ∀ᶠ d in 𝓝 d₀, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ p d j ≠ 0 :=
    Filter.eventually_all.2 hcoordinate
  change {d | ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ p d j ≠ 0} ∈ 𝓝 d₀ at hnear
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let d₂ := min ((d₀ + d₁) / 2) (d₀ + δ / 2)
  have hd₀d₂ : d₀ < d₂ := by
    apply lt_min
    · linarith
    · linarith
  have hd₂d₁ : d₂ < d₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨d₂, hd₀d₂, hd₂d₁, ?_⟩
  intro d hd j
  by_cases hphysical : d ≤ d₀
  · have hS := hp d hphysical
    exact ⟨hS.1 j, cor34_even_S_n_roots_nonzero hS hn j⟩
  · have hd₀d : d₀ < d := lt_of_not_ge hphysical
    have hdu : d < d₀ + δ / 2 := lt_of_lt_of_le hd (min_le_right _ _)
    have hdist : dist d d₀ < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hd₀d)]
      linarith
    exact hball (Metric.mem_ball.mpr hdist) j

/-- The odd analytic family keeps its centered zero root identically zero. -/
theorem cor34_final_odd_center_zero_on_analytic_domain {n q : ℕ}
    {d₀ d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < d₁) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q) :
    ∀ d < d₁, p d (⟨q - 1, by omega⟩ : Fin n) = 0 := by
  let l : Fin n := ⟨q - 1, by omega⟩
  have hanalytic : AnalyticOnNhd ℝ (fun d => p d l) (Iio d₁) := by
    intro d hd
    exact cor34_final_analyticAt_coordinate hpAnalytic hd l
  have hzero : AnalyticOnNhd ℝ (fun _ : ℝ => (0 : ℝ)) (Iio d₁) := by
    intro d hd
    exact analyticAt_const
  have heq : EqOn (fun d => p d l) (fun _ => (0 : ℝ)) (Iio d₀) := by
    intro d hd
    exact cor34_odd_S_n_center_zero (hp d hd.le) hnq
  have hext := cor34_identity_theorem_extension hanalytic hzero
    isPreconnected_Iio isOpen_Iio nonempty_Iio
    (fun d hd => lt_trans hd hd₀) heq
  intro d hd
  simpa [l] using hext hd

/-- In the odd case all noncentral roots stay nonzero, and all roots stay in the principal
momentum interval, on a slightly larger interval than the physical range. -/
theorem cor34_final_odd_exists_regular_cutoff {n q : ℕ}
    {d₀ d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < d₁) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q) :
    ∃ d₂, d₀ < d₂ ∧ d₂ < d₁ ∧
      (∀ d < d₂, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧
        (j = (⟨q - 1, by omega⟩ : Fin n) ∨ p d j ≠ 0)) ∧
      (∀ d < d₁, p d (⟨q - 1, by omega⟩ : Fin n) = 0) := by
  let l : Fin n := ⟨q - 1, by omega⟩
  have hp₀ : p d₀ ∈ Bethe.S_n n := hp d₀ le_rfl
  have hcenter₀ : p d₀ l = 0 := cor34_odd_S_n_center_zero hp₀ hnq
  have hnonzero₀ : ∀ j, j = l ∨ p d₀ j ≠ 0 := by
    intro j
    by_cases hj : j = l
    · exact Or.inl hj
    · right
      intro h
      apply hj
      exact (cor34_S_n_injective hp₀) (h.trans hcenter₀.symm)
  have hpCont : ContinuousAt p d₀ :=
    (hpAnalytic d₀ hd₀).continuousAt
  have hcoordinate (j : Fin n) :
      ∀ᶠ d in 𝓝 d₀, p d j ∈ Ioo (-Real.pi) Real.pi ∧ (j = l ∨ p d j ≠ 0) := by
    have hcont : ContinuousAt (fun d => p d j) d₀ :=
      (continuous_apply j).continuousAt.comp hpCont
    have hrange : ∀ᶠ d in 𝓝 d₀, p d j ∈ Ioo (-Real.pi) Real.pi :=
      hcont.eventually (isOpen_Ioo.mem_nhds (hp₀.1 j))
    have hroot : ∀ᶠ d in 𝓝 d₀, j = l ∨ p d j ≠ 0 := by
      by_cases hj : j = l
      · exact Filter.Eventually.of_forall (fun _ => Or.inl hj)
      · exact (hcont.eventually_ne (by
          rcases hnonzero₀ j with heq | hne
          · exact (hj heq).elim
          · exact hne)).mono (fun _ hne => Or.inr hne)
    exact hrange.and hroot
  have hnear : ∀ᶠ d in 𝓝 d₀, ∀ j,
      p d j ∈ Ioo (-Real.pi) Real.pi ∧ (j = l ∨ p d j ≠ 0) :=
    Filter.eventually_all.2 hcoordinate
  change {d | ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧
      (j = l ∨ p d j ≠ 0)} ∈ 𝓝 d₀ at hnear
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let d₂ := min ((d₀ + d₁) / 2) (d₀ + δ / 2)
  have hd₀d₂ : d₀ < d₂ := by
    apply lt_min
    · linarith
    · linarith
  have hd₂d₁ : d₂ < d₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hzero := cor34_final_odd_center_zero_on_analytic_domain hd₀ hpAnalytic hp hnq
  refine ⟨d₂, hd₀d₂, hd₂d₁, ?_, hzero⟩
  intro d hd j
  by_cases hphysical : d ≤ d₀
  · have hS := hp d hphysical
    have hnonzero : j = l ∨ p d j ≠ 0 := by
      by_cases hj : j = l
      · exact Or.inl hj
      · right
        intro hz
        apply hj
        exact (cor34_S_n_injective hS) (hz.trans (cor34_odd_S_n_center_zero hS hnq).symm)
    exact ⟨hS.1 j, hnonzero⟩
  · have hd₀d : d₀ < d := lt_of_not_ge hphysical
    have hdu : d < d₀ + δ / 2 := lt_of_lt_of_le hd (min_le_right _ _)
    have hdist : dist d d₀ < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hd₀d)]
      linarith
    exact hball (Metric.mem_ball.mpr hdist) j

/-- The normalized regular Bethe eigenvalue is analytic wherever all momenta avoid zero and
remain in the principal interval. -/
theorem cor34_final_analyticAt_normalizedRegular {n : ℕ}
    {d d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₁ : d₁ < -1) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁)
    (hrange : ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi)
    (hnonzero : ∀ j, p d j ≠ 0) :
    AnalyticAt ℝ (fun t => cor34_normalizedRegularEigenvalue (1 / t) (p t)) d := by
  have hepsR : AnalyticAt ℝ (fun t : ℝ => 1 / t) d :=
    analyticAt_const.div analyticAt_id
      (ne_of_lt (lt_trans hd (lt_trans hd₁ (by norm_num))))
  have hhalfR : AnalyticAt ℝ (fun t : ℝ => -(1 / t) / 2) d := by
    fun_prop
  have hhalfC : AnalyticAt ℝ (fun t : ℝ => ((-(1 / t) / 2 : ℝ) : ℂ)) d :=
    cor34_final_analyticAt_ofReal hhalfR
  have hcoefR : AnalyticAt ℝ (fun t : ℝ => 1 - 1 / t) d :=
    analyticAt_const.sub hepsR
  have hcoefC : AnalyticAt ℝ (fun t : ℝ => ((1 - 1 / t : ℝ) : ℂ)) d :=
    cor34_final_analyticAt_ofReal hcoefR
  have hZ (j : Fin n) :
      AnalyticAt ℝ (fun t : ℝ => BetheAnsatz.z (p t j)) d := by
    have hpj := cor34_final_analyticAt_coordinate hpAnalytic hd j
    have hpjC : AnalyticAt ℝ (fun t : ℝ => (p t j : ℂ)) d :=
      cor34_final_analyticAt_ofReal hpj
    have harg : AnalyticAt ℝ (fun t : ℝ => Complex.I * (p t j : ℂ)) d := by
      fun_prop
    change AnalyticAt ℝ
      (Complex.exp ∘ fun t : ℝ => Complex.I * (p t j : ℂ)) d
    exact analyticAt_cexp.restrictScalars.comp harg
  have hden (j : Fin n) :
      AnalyticAt ℝ (fun t : ℝ => 1 - BetheAnsatz.z (p t j)) d :=
    analyticAt_const.sub (hZ j)
  have hdenne (j : Fin n) : 1 - BetheAnsatz.z (p d j) ≠ 0 := by
    have hz := BetheAnsatz.z_ne_one (hrange j) (hnonzero j)
    intro h
    exact hz (sub_eq_zero.mp h).symm
  have hL (j : Fin n) :
      AnalyticAt ℝ (fun t : ℝ => cor34_normalizedL (1 / t) (p t j)) d := by
    have hfrac : AnalyticAt ℝ
        (fun t : ℝ => BetheAnsatz.z (p t j) / (1 - BetheAnsatz.z (p t j))) d :=
      (hZ j).div (hden j) (hdenne j)
    have hcalc := hhalfC.add (hcoefC.mul hfrac)
    convert hcalc using 1
    ext t
    simp [cor34_normalizedL, div_eq_mul_inv]
    ring
  have hM (j : Fin n) :
      AnalyticAt ℝ (fun t : ℝ => cor34_normalizedM (1 / t) (p t j)) d := by
    have hfrac : AnalyticAt ℝ
        (fun t : ℝ => ((1 - 1 / t : ℝ) : ℂ) /
          (1 - BetheAnsatz.z (p t j))) d :=
      hcoefC.div (hden j) (hdenne j)
    have hcalc := hhalfC.sub hfrac
    convert hcalc using 1
    ext t
    simp [cor34_normalizedM]
  have hprodL := Finset.univ.analyticAt_fun_prod (fun j _ => hL j)
  have hprodM := Finset.univ.analyticAt_fun_prod (fun j _ => hM j)
  convert hprodL.add hprodM using 1
  ext t
  simp [cor34_normalizedRegularEigenvalue]

private theorem cor34_final_analyticAt_derivativeCorrection {n : ℕ}
    {d d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₁ : d₁ < -1) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁)
    (j : Fin n) :
    AnalyticAt ℝ (fun t => cor34_derivativeCorrection (1 / t) (p t j)) d := by
  have heps : AnalyticAt ℝ (fun t : ℝ => 1 / t) d :=
    analyticAt_const.div analyticAt_id
      (ne_of_lt (lt_trans hd (lt_trans hd₁ (by norm_num))))
  have hpj := cor34_final_analyticAt_coordinate hpAnalytic hd j
  have hcos : AnalyticAt ℝ (fun t => Real.cos (p t j)) d := by fun_prop
  have hsin : AnalyticAt ℝ (fun t => Real.sin (p t j)) d := by fun_prop
  have hnum : AnalyticAt ℝ
      (fun t : ℝ => 2 * (1 / t) * ((1 / t) * (1 + Real.cos (p t j)) - 2)) d := by
    fun_prop
  have hden : AnalyticAt ℝ
      (fun t : ℝ => ((1 / t) * (1 + Real.cos (p t j)) - 2) ^ 2 +
        (1 / t) ^ 2 * (Real.sin (p t j)) ^ 2) d := by
    fun_prop
  have harg : (1 / d) * (1 + Real.cos (p d j)) - 2 < 0 := by
    have hε : 1 / d < 0 := one_div_neg.mpr (lt_trans hd (lt_trans hd₁ (by norm_num)))
    have hcos₀ : 0 ≤ 1 + Real.cos (p d j) := by
      linarith [Real.neg_one_le_cos (p d j)]
    have hmul : (1 / d) * (1 + Real.cos (p d j)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hε.le hcos₀
    linarith
  have hdenPos : 0 <
      ((1 / d) * (1 + Real.cos (p d j)) - 2) ^ 2 +
        (1 / d) ^ 2 * (Real.sin (p d j)) ^ 2 := by
    apply add_pos_of_pos_of_nonneg
    · exact sq_pos_of_ne_zero (ne_of_lt harg)
    · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hquot := hnum.div hden (ne_of_gt hdenPos)
  convert hquot using 1
  ext t
  simp [cor34_derivativeCorrection, div_eq_mul_inv, inv_pow]

/-- The odd normalized zero-root expression is analytic after deleting its centered root. -/
theorem cor34_final_analyticAt_normalizedZero {N n : ℕ}
    {d d₁ : ℝ} {p : ℝ → Fin n → ℝ} (l : Fin n)
    (hd₁ : d₁ < -1) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁)
    (hrange : ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi)
    (hgood : ∀ j, j = l ∨ p d j ≠ 0) :
    AnalyticAt ℝ
      (fun t => cor34_normalizedZeroEigenvalue (N := N) (1 / t) (p t) l) d := by
  have heps : AnalyticAt ℝ (fun t : ℝ => 1 / t) d :=
    analyticAt_const.div analyticAt_id
      (ne_of_lt (lt_trans hd (lt_trans hd₁ (by norm_num))))
  have hhalfR : AnalyticAt ℝ (fun t : ℝ => -(1 / t) / 2) d := by fun_prop
  have hhalfC : AnalyticAt ℝ (fun t : ℝ => ((-(1 / t) / 2 : ℝ) : ℂ)) d :=
    cor34_final_analyticAt_ofReal hhalfR
  have hcoefR : AnalyticAt ℝ (fun t : ℝ => 1 - 1 / t) d :=
    analyticAt_const.sub heps
  have hcoefC : AnalyticAt ℝ (fun t : ℝ => ((1 - 1 / t : ℝ) : ℂ)) d :=
    cor34_final_analyticAt_ofReal hcoefR
  have hZ (j : Fin n) :
      AnalyticAt ℝ (fun t : ℝ => BetheAnsatz.z (p t j)) d := by
    have hpj := cor34_final_analyticAt_coordinate hpAnalytic hd j
    have hpjC : AnalyticAt ℝ (fun t : ℝ => (p t j : ℂ)) d :=
      cor34_final_analyticAt_ofReal hpj
    have harg : AnalyticAt ℝ (fun t : ℝ => Complex.I * (p t j : ℂ)) d := by
      fun_prop
    change AnalyticAt ℝ
      (Complex.exp ∘ fun t : ℝ => Complex.I * (p t j : ℂ)) d
    exact analyticAt_cexp.restrictScalars.comp harg
  have hden (j : Fin n) :
      AnalyticAt ℝ (fun t : ℝ => 1 - BetheAnsatz.z (p t j)) d :=
    analyticAt_const.sub (hZ j)
  have hdenne (j : Fin n) (hj : j ≠ l) :
      1 - BetheAnsatz.z (p d j) ≠ 0 := by
    have hne : p d j ≠ 0 := by
      rcases hgood j with hsame | hne
      · exact (hj hsame).elim
      · exact hne
    have hz := BetheAnsatz.z_ne_one (hrange j) hne
    intro h
    exact hz (sub_eq_zero.mp h).symm
  have hM (j : Fin n) (hj : j ∈ Finset.univ.erase l) :
      AnalyticAt ℝ (fun t : ℝ => cor34_normalizedM (1 / t) (p t j)) d := by
    have hjne : j ≠ l := (Finset.mem_erase.mp hj).1
    have hfrac : AnalyticAt ℝ
        (fun t : ℝ => ((1 - 1 / t : ℝ) : ℂ) /
          (1 - BetheAnsatz.z (p t j))) d :=
      hcoefC.div (hden j) (hdenne j hjne)
    have hcalc := hhalfC.sub hfrac
    convert hcalc using 1
    ext t
    simp [cor34_normalizedM]
  have hcorr (j : Fin n) :
      AnalyticAt ℝ (fun t : ℝ => cor34_derivativeCorrection (1 / t) (p t j)) d :=
    cor34_final_analyticAt_derivativeCorrection hd₁ hpAnalytic hd j
  have hsum : AnalyticAt ℝ
      (fun t : ℝ => (N : ℝ) - 1 +
        ∑ j ∈ Finset.univ.erase l, (-1 + cor34_derivativeCorrection (1 / t) (p t j))) d := by
    have hminusOne : AnalyticAt ℝ (fun _ : ℝ => (-1 : ℝ)) d := analyticAt_const
    have hterm (j : Fin n) : AnalyticAt ℝ
        (fun t : ℝ => -1 + cor34_derivativeCorrection (1 / t) (p t j)) d :=
      hminusOne.add (hcorr j)
    have hfinite := (Finset.univ.erase l).analyticAt_fun_sum
      (fun j _ => hterm j)
    exact analyticAt_const.add hfinite
  have hsumC : AnalyticAt ℝ
      (fun t : ℝ => (((N : ℝ) - 1 +
        ∑ j ∈ Finset.univ.erase l, (-1 + cor34_derivativeCorrection (1 / t) (p t j)) : ℝ) : ℂ)) d :=
    cor34_final_analyticAt_ofReal hsum
  have hminusR : AnalyticAt ℝ (fun t : ℝ => -(1 / t)) d := by fun_prop
  have hminusC : AnalyticAt ℝ (fun t : ℝ => ((-(1 / t) : ℝ) : ℂ)) d :=
    cor34_final_analyticAt_ofReal hminusR
  have hfactor := hminusC.add (hcoefC.mul hsumC)
  have hprod := (Finset.univ.erase l).analyticAt_fun_prod
    (fun j hj => hM j hj)
  have htotal := hfactor.mul hprod
  convert htotal using 1
  ext t
  simp [cor34_normalizedZeroEigenvalue]

end PottsDiscontinuity.SixVertex
