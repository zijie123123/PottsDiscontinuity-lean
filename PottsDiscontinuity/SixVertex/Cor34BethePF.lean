module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34BetheLimits
public import PottsDiscontinuity.SixVertex.Cor34Spectral

/-! # Corollary 3.4: conditional identification with the Perron root

The eigenvector equation is an explicit premise corresponding to the Bethe ansatz theorem.
-/

@[expose] public section

open Filter Topology
open Matrix Set
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

/-- The continuously normalized Bethe coordinate wave on the `n`-particle state block. -/
noncomputable def cor34_normalizedBlockWave {N n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ) : State N n → ℂ :=
  fun x => cor34_normalizedCoordinate ε p (BetheAnsatz.positions x)

private theorem cor34_scalar_mulVec_eq_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Semiring K] (z : K) (v : ι → K) :
    Matrix.scalar ι z *ᵥ v = z • v := by
  ext i
  simp [Matrix.scalar, Matrix.diagonal, Matrix.mulVec, dotProduct]

private theorem cor34_det_eq_zero_of_mulVec_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]
    {M : Matrix ι ι K} {v : ι → K} (hv : v ≠ 0) (hMv : M *ᵥ v = 0) : M.det = 0 := by
  have hsmul : M.det • v = 0 := by
    calc
      M.det • v = (M.adjugate * M) *ᵥ v := by
        rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = M.adjugate *ᵥ (M *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hMv, Matrix.mulVec_zero]
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  have hcoord := congrFun hsmul i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_right hi

/-- One-sided form of the simple-top-root argument. The eigenvector equation is needed only
on the physical side `ε<0`, matching the finite-parameter Bethe identity. -/
private theorem cor34_local_eigenvalue_uniqueness_left
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : ℝ → Matrix ι ι ℝ} {μ : ℝ → ℂ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) 0)
    (hHerm : ∀ t, (A t).IsHermitian)
    (hsimple : (A 0).charpoly.rootMultiplicity (sSup (spectrum ℝ (A 0))) = 1)
    (hμ : Tendsto μ (𝓝 0) (𝓝 ((sSup (spectrum ℝ (A 0)) : ℝ) : ℂ)))
    (hEig : ∀ᶠ t in 𝓝[<] 0, ∃ ψ : ι → ℂ, ψ ≠ 0 ∧
      (A t).map (algebraMap ℝ ℂ) *ᵥ ψ = μ t • ψ) :
    ∀ᶠ t in 𝓝[<] 0, μ t = ((sSup (spectrum ℝ (A t)) : ℝ) : ℂ) := by
  let ρ : ℝ := sSup (spectrum ℝ (A 0))
  have hroot0 : (A 0).charpoly.eval ρ = 0 := by
    have hmem := (AnalyticTools.largestSpectrum_isGreatest (hHerm 0)).1
    have hchar : Polynomial.IsRoot (A 0).charpoly ρ :=
      (Matrix.mem_spectrum_iff_isRoot_charpoly).1 hmem
    exact hchar.eq_zero
  have hbranch := AnalyticTools.exists_analytic_charpolyRootBranch_of_simple_with_local_uniqueness
    (A := A) (t₀ := 0) (μ₀ := ρ) hA hroot0 hsimple
  obtain ⟨branch, hbranch0, hbranchAnalytic, W, V, hWopen, hVopen, hWbase, hVbase,
      hbranch, hunique⟩ := hbranch
  have hpfCont : ContinuousAt (fun t => sSup (spectrum ℝ (A t))) 0 :=
    AnalyticTools.continuousAt_pfRoot_of_entrywise_analytic hA (hHerm 0)
      (Filter.Eventually.of_forall hHerm)
  have hμre : Tendsto (fun t => (μ t).re) (𝓝 0) (𝓝 ρ) := by
    change Tendsto (Complex.re ∘ μ) (𝓝 0) (𝓝 ρ)
    have h := Complex.continuous_re.continuousAt.tendsto.comp hμ
    simpa [ρ] using h
  have hbranch_pf : ∀ᶠ t in 𝓝 0,
      sSup (spectrum ℝ (A t)) = branch t := by
    have hpair : Tendsto (fun t => (t, sSup (spectrum ℝ (A t))))
        (𝓝 0) (𝓝 (0, ρ)) := by
      have hc : ContinuousAt (fun t => (t, sSup (spectrum ℝ (A t)))) 0 :=
        continuousAt_id.prodMk hpfCont
      simpa [ρ] using hc.tendsto
    filter_upwards [hpair.eventually (hWopen.mem_nhds hWbase),
      Filter.Eventually.of_forall hHerm] with t hW hHt
    have hroot : (A t).charpoly.eval (sSup (spectrum ℝ (A t))) = 0 := by
      have hmem := (AnalyticTools.largestSpectrum_isGreatest hHt).1
      have hchar : Polynomial.IsRoot (A t).charpoly (sSup (spectrum ℝ (A t))) :=
        (Matrix.mem_spectrum_iff_isRoot_charpoly).1 hmem
      exact hchar.eq_zero
    exact hunique t (sSup (spectrum ℝ (A t))) hW hroot
  have hbranch_pf_left := hbranch_pf.filter_mono
    (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ)))
  have hμ_real_eventually : ∀ᶠ t in 𝓝[<] 0, μ t = (μ t).re := by
    filter_upwards [hEig] with t ht
    obtain ⟨ψ, hψne, hψ⟩ := ht
    let AC : Matrix ι ι ℂ := (A t).map (algebraMap ℝ ℂ)
    have hAC : AC.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      simp only [AC, Matrix.map_apply, Complex.star_def]
      have hs := (hHerm t).apply i j
      simpa using congrArg (algebraMap ℝ ℂ) hs
    have hμreal : μ t = (μ t).re := by
      let q : ℂ := star ψ ⬝ᵥ ψ
      have hself := hAC.star_dotProduct_mulVec_comm ψ ψ
      rw [hψ] at hself
      have hqstar : star q = q := by
        dsimp [q]
        exact (star_dotProduct ψ ψ).symm
      have hμq : star (μ t) * q = μ t * q := by
        calc
          star (μ t) * q = star (μ t * q) := by
            calc
              star (μ t) * q = star (μ t) * star q := by rw [hqstar]
              _ = star (μ t * q) := (map_mul (starRingEnd ℂ) (μ t) q).symm
          _ = star (star ψ ⬝ᵥ (μ t • ψ)) := by
            congr 1
            rw [dotProduct_smul, smul_eq_mul]
          _ = star ψ ⬝ᵥ (μ t • ψ) := hself
          _ = μ t * q := by rw [dotProduct_smul, smul_eq_mul]
      have hq : q ≠ 0 := by
        have hsum : (star ψ ⬝ᵥ ψ) =
            (∑ i, (Complex.normSq (ψ i) : ℝ) : ℂ) := by
          simp [dotProduct, Complex.normSq_eq_conj_mul_self]
        have hpos : 0 < ∑ i, Complex.normSq (ψ i) := by
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hψne
          refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
          exact Complex.normSq_pos.mpr hi
        change star ψ ⬝ᵥ ψ ≠ 0
        rw [hsum]
        exact_mod_cast (ne_of_gt hpos)
      have hstar : star (μ t) = μ t := mul_right_cancel₀ hq hμq
      have him' : -(μ t).im = (μ t).im := by
        have := congrArg Complex.im hstar
        simpa [Complex.star_def] using this
      have him : (μ t).im = 0 := by linarith
      apply Complex.ext
      · rfl
      · exact him
    exact hμreal
  have hμ_root_eventually : ∀ᶠ t in 𝓝[<] 0,
      (A t).charpoly.eval (μ t).re = 0 := by
    filter_upwards [hμ_real_eventually, hEig] with t hreal hEig_t
    obtain ⟨ψ, hψne, hψ⟩ := hEig_t
    let m := (μ t).re
    let AC : Matrix ι ι ℂ := (A t).map (algebraMap ℝ ℂ)
    have hzero : (Matrix.scalar ι (m : ℂ) - AC) *ᵥ ψ = 0 := by
      rw [Matrix.sub_mulVec, cor34_scalar_mulVec_eq_smul, hψ, hreal, sub_self]
    have hdetC : (Matrix.scalar ι (m : ℂ) - AC).det = 0 :=
      cor34_det_eq_zero_of_mulVec_eq_zero hψne hzero
    have hmap : (algebraMap ℝ ℂ).mapMatrix (Matrix.scalar ι m - A t) =
        Matrix.scalar ι (m : ℂ) - AC := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [AC, Matrix.scalar]
      · simp [AC, Matrix.scalar, hij]
    have hdetR : (Matrix.scalar ι m - A t).det = 0 := by
      apply (algebraMap ℝ ℂ).injective
      rw [RingHom.map_det, hmap, hdetC]
      simp
    rw [Matrix.eval_charpoly]
    exact hdetR
  have hmCurve : Tendsto (fun t => (t, (μ t).re)) (𝓝 0) (𝓝 (0, ρ)) := by
    have hprod : Tendsto (fun t => (t, (μ t).re)) (𝓝 0) (𝓝 0 ×ˢ 𝓝 ρ) :=
      Filter.Tendsto.prodMk continuousAt_id.tendsto hμre
    simpa only [nhds_prod_eq] using hprod
  have hmCurve_left := hmCurve.mono_left
    (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ)))
  have hbranch_mu : ∀ᶠ t in 𝓝[<] 0, (μ t).re = branch t := by
    filter_upwards [hmCurve_left.eventually (hWopen.mem_nhds hWbase),
      hμ_root_eventually] with t hW hroot
    exact hunique t (μ t).re hW hroot
  filter_upwards [hμ_real_eventually, hbranch_mu, hbranch_pf_left]
    with t hreal hμb hpfb
  rw [hreal, hμb, hpfb]

/-- A normalized Bethe eigenvalue branch converging to the infinity PF root is the PF root
near zero if its normalized wave is eventually a nonzero eigenvector of the normalized block. -/
theorem cor34_bethe_eigenbranch_eventually_pfRoot {N n : ℕ}
    (hn : 0 < n) (hbound : 2 * n ≤ N)
    {μ : ℝ → ℂ} {ψ : ℝ → State N n → ℂ}
    (hμ : Tendsto μ (𝓝 0) (𝓝 (pfRoot (infinityBlock N n) : ℂ)))
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      ψ ε ≠ 0 ∧
        Matrix.mulVec ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ))
          (ψ ε) =
          μ ε • ψ ε) :
    ∀ᶠ ε in 𝓝[<] 0,
      μ ε = (pfRoot (cor34_normalizedTransferBlock N n ε) : ℂ) := by
  have : Nonempty (State N n) := ⟨packed (by omega)⟩
  let A : ℝ → Matrix (State N n) (State N n) ℝ :=
    cor34_normalizedTransferBlock N n
  have hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) 0 := by
    intro i j
    exact cor34_normalizedTransferBlock_entry_analyticAt i j 0
  have hHerm : ∀ t, (A t).IsHermitian := by
    intro t
    exact cor34_normalizedTransferBlock_isHermitian t
  have hsimple : (A 0).charpoly.rootMultiplicity
      (sSup (spectrum ℝ (A 0))) = 1 := by
    simpa [A, cor34_normalizedTransferBlock_zero, pfRoot] using
      rootMultiplicity_infinityBlock_pfRoot hn hbound
  have hμ' : Tendsto μ (𝓝 0)
      (𝓝 ((sSup (spectrum ℝ (A 0)) : ℝ) : ℂ)) := by
    simpa [A, cor34_normalizedTransferBlock_zero, pfRoot] using hμ
  have hEig' : ∀ᶠ t in 𝓝[<] 0, ∃ v : State N n → ℂ, v ≠ 0 ∧
      Matrix.mulVec ((A t).map (algebraMap ℝ ℂ)) v = μ t • v := by
    filter_upwards [hEig] with t ht
    exact ⟨ψ t, ht.1, by simpa [A] using ht.2⟩
  have hnear := cor34_local_eigenvalue_uniqueness_left
    (fun i j => hA i j) hHerm hsimple hμ' hEig'
  simpa [A, pfRoot] using hnear

/-- The even normalized eigenvalue is the physical Bethe eigenvalue multiplied by
`(-ε/2)^n = (-2/ε)^(-n)`. -/
private theorem cor34_normalizedRegularEigenvalue_scale {n : ℕ} (ε : ℝ)
    (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedRegularEigenvalue ε p =
      (((-ε / 2 : ℝ) : ℂ) ^ n) *
        BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) p := by
  let q : ℂ := ((-ε / 2 : ℝ) : ℂ)
  let c : ℝ := Real.sqrt (2 - 2 / ε)
  have hroot : c ^ 2 = 2 - 2 / ε := by
    dsimp [c]
    have hrec : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hε
    exact Real.sq_sqrt (by linarith)
  have hcoeffR : (-ε / 2) * (2 - 2 / ε) = 1 - ε := by
    field_simp [ne_of_lt hε]
    ring
  have hcoeff : q * (c : ℂ) ^ 2 = ((1 - ε : ℝ) : ℂ) := by
    dsimp [q, c]
    rw [show ((Real.sqrt (2 - 2 / ε) : ℝ) : ℂ) ^ 2 =
      ((2 - 2 / ε : ℝ) : ℂ) by exact_mod_cast hroot]
    exact_mod_cast hcoeffR
  have hL (j : Fin n) :
      cor34_normalizedL ε (p j) = q * BetheAnsatz.L c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedL BetheAnsatz.L
    rw [← hcoeff]
    ring
  have hM (j : Fin n) :
      cor34_normalizedM ε (p j) = q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedM BetheAnsatz.M
    rw [← hcoeff]
    ring
  have hprodL :
      (∏ j : Fin n, cor34_normalizedL ε (p j)) =
        q ^ n * ∏ j : Fin n, BetheAnsatz.L c (BetheAnsatz.z (p j)) := by
    calc
      _ = ∏ j : Fin n, q * BetheAnsatz.L c (BetheAnsatz.z (p j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hL j
      _ = (∏ j : Fin n, q) * ∏ j : Fin n, BetheAnsatz.L c (BetheAnsatz.z (p j)) :=
        Finset.prod_mul_distrib
      _ = _ := by simp [Finset.prod_const, Fintype.card_fin]
  have hprodM :
      (∏ j : Fin n, cor34_normalizedM ε (p j)) =
        q ^ n * ∏ j : Fin n, BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    calc
      _ = ∏ j : Fin n, q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hM j
      _ = (∏ j : Fin n, q) * ∏ j : Fin n, BetheAnsatz.M c (BetheAnsatz.z (p j)) :=
        Finset.prod_mul_distrib
      _ = _ := by simp [Finset.prod_const, Fintype.card_fin]
  unfold cor34_normalizedRegularEigenvalue BetheAnsatz.eigenvalueRegular
  rw [hprodL, hprodM]
  simp only [q]
  ring

private theorem cor34_derivativeCorrection_eq_rational {ε y : ℝ} (hε : ε < 0) :
    cor34_derivativeCorrection ε y =
      2 * (1 + Real.cos y - 2 / ε) /
        ((1 + Real.cos y - 2 / ε) ^ 2 + (Real.sin y) ^ 2) := by
  have hdiv : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hε
  have hd : 0 < 1 + Real.cos y - 2 / ε := by
    have hcos := Real.neg_one_le_cos y
    linarith
  have hden :
      (ε * (1 + Real.cos y) - 2) ^ 2 + ε ^ 2 * (Real.sin y) ^ 2 =
        ε ^ 2 * ((1 + Real.cos y - 2 / ε) ^ 2 + (Real.sin y) ^ 2) := by
    field_simp [ne_of_lt hε]
  have hnum :
      2 * ε * (ε * (1 + Real.cos y) - 2) =
        ε ^ 2 * (2 * (1 + Real.cos y - 2 / ε)) := by
    field_simp [ne_of_lt hε]
  have hdenne :
      (ε * (1 + Real.cos y) - 2) ^ 2 + ε ^ 2 * (Real.sin y) ^ 2 ≠ 0 := by
    rw [hden]
    exact mul_ne_zero (pow_ne_zero _ (ne_of_lt hε)) (ne_of_gt (by positivity))
  unfold cor34_derivativeCorrection
  rw [hnum, hden]
  field_simp [ne_of_lt hε, ne_of_gt (by positivity :
    0 < (1 + Real.cos y - 2 / ε) ^ 2 + (Real.sin y) ^ 2)]

/-- The odd normalized zero-root eigenvalue is the physical expression multiplied by
`(-ε/2)^n` on the negative side where the phase derivative formula applies. -/
private theorem cor34_normalizedZeroEigenvalue_scale {N n : ℕ} (l : Fin n)
    (ε : ℝ) (hεlo : -1 < ε) (hεhi : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedZeroEigenvalue (N := N) ε p l =
      (((-ε / 2 : ℝ) : ℂ) ^ n) *
        BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) p l := by
  let q : ℂ := ((-ε / 2 : ℝ) : ℂ)
  let c : ℝ := Real.sqrt (2 - 2 / ε)
  have hroot : c ^ 2 = 2 - 2 / ε := by
    dsimp [c]
    have hdiv : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hεhi
    exact Real.sq_sqrt (by linarith)
  have hcoeffR : (-ε / 2) * (2 - 2 / ε) = 1 - ε := by
    field_simp [ne_of_lt hεhi]
    ring
  have hcoeff : q * (c : ℂ) ^ 2 = ((1 - ε : ℝ) : ℂ) := by
    dsimp [q, c]
    rw [show ((Real.sqrt (2 - 2 / ε) : ℝ) : ℂ) ^ 2 =
      ((2 - 2 / ε : ℝ) : ℂ) by exact_mod_cast hroot]
    exact_mod_cast hcoeffR
  have hbaseInv : 1 / ε < -1 := by
    have hinv : 1 / ε < 0 := div_neg_of_pos_of_neg one_pos hεhi
    have hmul : ε * (1 / ε) = 1 := by field_simp [ne_of_lt hεhi]
    have hprod : (ε + 1) * (1 / ε) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hinv
    have hprodEq : (ε + 1) * (1 / ε) = 1 + 1 / ε := by
      calc
        (ε + 1) * (1 / ε) = ε * (1 / ε) + 1 * (1 / ε) := by ring
        _ = 1 + 1 / ε := by rw [hmul]; ring
    rw [hprodEq] at hprod
    linarith
  have hanisotropy : BetheAnsatz.anisotropy c = 1 / ε := by
    unfold BetheAnsatz.anisotropy
    rw [hroot]
    ring
  have hderiv (j : Fin n) :
      (deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 : ℝ) =
        -1 + cor34_derivativeCorrection ε (p j) := by
    rw [hanisotropy, cor34_deriv_theta_at_zero hbaseInv]
    rw [show 2 * (1 / ε) = 2 / ε by ring]
    rw [cor34_derivativeCorrection_eq_rational hεhi]
  have hderivC (j : Fin n) :
      deriv (fun t : ℝ => (Bethe.theta (BetheAnsatz.anisotropy c) t (p j) : ℂ)) 0 =
        ((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ) := by
    have hdiff : DifferentiableAt ℝ
        (fun t : ℝ => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 := by
      simpa [hanisotropy] using
        (Bethe.analyticAt_theta_left hbaseInv 0 (p j)).differentiableAt
    have hcast := hdiff.hasDerivAt.ofReal_comp
    rw [hcast.deriv, hderiv j]
  have hsum :
      (∑ j ∈ Finset.univ.erase l,
          (deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 : ℂ)) =
        ∑ j ∈ Finset.univ.erase l,
          (((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hderivC j
  have htwo : q * (2 : ℂ) = ((-ε : ℝ) : ℂ) := by
    dsimp [q]
    push_cast
    ring
  have hcoef :
      q * (2 + (c : ℂ) ^ 2 * ((N : ℂ) - 1) + (c : ℂ) ^ 2 *
        ∑ j ∈ Finset.univ.erase l,
          (deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 : ℂ)) =
        ((-ε : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) *
          (((N : ℂ) - 1) + ∑ j ∈ Finset.univ.erase l,
            (((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ))) := by
    rw [hsum]
    calc
      _ = q * 2 + (q * (c : ℂ) ^ 2) * ((N : ℂ) - 1) +
          (q * (c : ℂ) ^ 2) *
            ∑ j ∈ Finset.univ.erase l,
              (((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ)) := by ring
      _ = ((-ε : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) * ((N : ℂ) - 1) +
          ((1 - ε : ℝ) : ℂ) *
            ∑ j ∈ Finset.univ.erase l,
              (((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ)) := by
            rw [htwo, hcoeff]
      _ = _ := by ring
  have hM (j : Fin n) :
      cor34_normalizedM ε (p j) = q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedM BetheAnsatz.M
    rw [← hcoeff]
    ring
  have hprodM :
      (∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j)) =
        q ^ (n - 1) * ∏ j ∈ Finset.univ.erase l,
          BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    calc
      _ = ∏ j ∈ Finset.univ.erase l,
          q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hM j
      _ = (∏ j ∈ Finset.univ.erase l, q) *
          ∏ j ∈ Finset.univ.erase l, BetheAnsatz.M c (BetheAnsatz.z (p j)) :=
        Finset.prod_mul_distrib
      _ = _ := by simp [Finset.prod_const, Finset.card_erase_of_mem]
  have hnpos : 0 < n := Nat.zero_lt_of_lt l.isLt
  have hpow : q * q ^ (n - 1) = q ^ n := by
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    calc
      q * q ^ (n - 1) = q ^ (n - 1) * q := by ring
      _ = q ^ (n - 1 + 1) := (pow_succ q (n - 1)).symm
      _ = q ^ n := by rw [hsub]
  have hcoef' := hcoef
  have hprodM' := hprodM
  have hmain :
      (((-ε : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) *
          (((N : ℂ) - 1) + ∑ j ∈ Finset.univ.erase l,
            (((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ)))) *
        ∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j) =
      q ^ n *
        ((2 + (c : ℂ) ^ 2 * ((N : ℂ) - 1) + (c : ℂ) ^ 2 *
            ∑ j ∈ Finset.univ.erase l,
              (deriv (fun t : ℝ =>
                (Bethe.theta (BetheAnsatz.anisotropy c) t (p j) : ℂ)) 0 : ℂ)) *
          ∏ j ∈ Finset.univ.erase l,
            BetheAnsatz.M c (BetheAnsatz.z (p j))) := by
    calc
      _ = (q * (2 + (c : ℂ) ^ 2 * ((N : ℂ) - 1) + (c : ℂ) ^ 2 *
            ∑ j ∈ Finset.univ.erase l,
              (deriv (fun t : ℝ =>
                (Bethe.theta (BetheAnsatz.anisotropy c) t (p j) : ℂ)) 0 : ℂ))) *
          ∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j) := by
        rw [← hcoef']
      _ = _ := by
        rw [hprodM']
        rw [← hpow]
        ring_nf
  simpa [cor34_normalizedZeroEigenvalue, BetheAnsatz.eigenvalueZero, c, q] using hmain

/-- Even-parity conditional Corollary 3.4 for a continuous family based at the discrete
solution. -/
theorem cor34_even_bethe_branch_eventually_pfRoot {N n r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 ≤ r)
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedBlockWave (N := N) (n := n) ε (p ε) ≠ 0 ∧
        Matrix.mulVec
          ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ))
            (cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) =
          cor34_normalizedRegularEigenvalue ε (p ε) •
            cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) :
    ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedRegularEigenvalue ε (p ε) =
        (pfRoot (cor34_normalizedTransferBlock N n ε) : ℂ) := by
  apply cor34_bethe_eigenbranch_eventually_pfRoot hnpos hbound
  · exact cor34_normalizedRegularEigenvalue_tendsto_pfRoot
      hp hp0 hNpos hbound hnpos hn hN hr
  · exact hEig

/-- The even conditional conclusion in physical eigenvalue units. -/
theorem cor34_even_bethe_branch_eventually_physical_pfRoot {N n r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 ≤ r)
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedBlockWave (N := N) (n := n) ε (p ε) ≠ 0 ∧
        Matrix.mulVec
          ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ))
            (cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) =
          cor34_normalizedRegularEigenvalue ε (p ε) •
            cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) :
    ∀ᶠ ε in 𝓝[<] 0,
      BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) (p ε) =
        (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
  have hnear := cor34_even_bethe_branch_eventually_pfRoot
    hp hp0 hNpos hbound hnpos hn hN hr hEig
  filter_upwards [hnear, self_mem_nhdsWithin] with ε hnear hεmem
  have hε : ε < 0 := hεmem
  have hscale := cor34_normalizedRegularEigenvalue_scale ε hε (p ε)
  have hroot := cor34_pfRoot_normalizedTransferBlock_eq
    (N := N) (n := n) (by omega) hε
  rw [hscale, hroot] at hnear
  let q : ℂ := ((-ε / 2 : ℝ) : ℂ)
  have hbaseInv : ((-2 / ε : ℝ)⁻¹) = (-ε / 2 : ℝ) := by
    field_simp [ne_of_lt hε]
  have hfactorR :
      (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n) =
        (-ε / 2 : ℝ) ^ n *
          pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) := by
    rw [div_eq_mul_inv, ← inv_pow, hbaseInv]
    ring
  have hfactor :
      ((pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n : ℝ) : ℂ) =
        q ^ n * (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
    dsimp [q]
    exact_mod_cast hfactorR
  rw [hfactor] at hnear
  have hqne : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast (div_ne_zero (neg_ne_zero.mpr (ne_of_lt hε)) (by norm_num))
  apply mul_left_cancel₀ (pow_ne_zero n hqne)
  simpa [q] using hnear

/-- Odd-parity conditional Corollary 3.4 for the centered zero-root branch. -/
theorem cor34_odd_bethe_branch_eventually_pfRoot {N n q r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 ≤ r)
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedBlockWave (N := N) (n := n) ε (p ε) ≠ 0 ∧
        Matrix.mulVec
          ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ))
            (cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) =
          cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
              (⟨q - 1, by omega⟩ : Fin n) •
            cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) :
    ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
          (⟨q - 1, by omega⟩ : Fin n) =
        (pfRoot (cor34_normalizedTransferBlock N n ε) : ℂ) := by
  apply cor34_bethe_eigenbranch_eventually_pfRoot hnpos hbound
  · exact cor34_normalizedZeroEigenvalue_tendsto_pfRoot
      hp hp0 hNpos hbound hnpos hnq hN hr
  · exact hEig

/-- The odd conditional conclusion in physical eigenvalue units. -/
theorem cor34_odd_bethe_branch_eventually_physical_pfRoot {N n q r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 ≤ r)
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedBlockWave (N := N) (n := n) ε (p ε) ≠ 0 ∧
        Matrix.mulVec
          ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ))
            (cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) =
          cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
              (⟨q - 1, by omega⟩ : Fin n) •
            cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) :
    ∀ᶠ ε in 𝓝[<] 0,
      BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) (p ε)
          (⟨q - 1, by omega⟩ : Fin n) =
        (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
  have hnear := cor34_odd_bethe_branch_eventually_pfRoot
    hp hp0 hNpos hbound hnpos hnq hN hr hEig
  have hgt : ∀ᶠ ε : ℝ in 𝓝[<] (0 : ℝ), (-1 : ℝ) < ε := by
    have hbase : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε ∈ Set.Ioi (-1 : ℝ) :=
      Ioi_mem_nhds (by norm_num)
    exact hbase.filter_mono (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ)))
  filter_upwards [hnear, hgt, self_mem_nhdsWithin] with ε hnear hεlo hεmem
  have hεhi : ε < 0 := hεmem
  let l : Fin n := ⟨q - 1, by omega⟩
  have hscale := cor34_normalizedZeroEigenvalue_scale (N := N) l ε hεlo hεhi (p ε)
  have hroot := cor34_pfRoot_normalizedTransferBlock_eq
    (N := N) (n := n) (by omega) hεhi
  rw [hscale, hroot] at hnear
  let qscale : ℂ := ((-ε / 2 : ℝ) : ℂ)
  have hbaseInv : ((-2 / ε : ℝ)⁻¹) = (-ε / 2 : ℝ) := by
    field_simp [ne_of_lt hεhi]
  have hfactorR :
      (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n) =
        (-ε / 2 : ℝ) ^ n *
          pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) := by
    rw [div_eq_mul_inv, ← inv_pow, hbaseInv]
    ring
  have hfactor :
      ((pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n : ℝ) : ℂ) =
        qscale ^ n * (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
    dsimp [qscale]
    exact_mod_cast hfactorR
  rw [hfactor] at hnear
  have hqne : qscale ≠ 0 := by
    dsimp [qscale]
    exact_mod_cast (div_ne_zero (neg_ne_zero.mpr (ne_of_lt hεhi)) (by norm_num))
  apply mul_left_cancel₀ (pow_ne_zero n hqne)
  simpa [qscale, l] using hnear

end PottsDiscontinuity.SixVertex
