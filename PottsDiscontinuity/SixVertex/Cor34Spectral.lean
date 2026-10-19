module

public import Mathlib
public import PottsDiscontinuity.AnalyticTools.Continuity
public import PottsDiscontinuity.SixVertex.BlockPerronFrobenius
public import PottsDiscontinuity.SixVertex.InfinityLimit

/-!
# Corollary 3.4: analytic spectral family

This file proves the analyticity of the concrete Perron root on the finite-anisotropy range and
records the normalized matrix family at infinite anisotropy.
-/

@[expose] public section

open Filter Matrix Set
open scoped Topology
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

private theorem cor34_transferBlock_sqrt_entry {N n : ℕ} (x y : State N n) {Δ : ℝ}
    (hΔ : Δ < 1) :
    transferBlock N (Real.sqrt (2 - 2 * Δ)) n x y =
      if x = y then 2 else
        if Interlaced x.1 y.1 then (2 - 2 * Δ) ^ (x.1 \ y.1).card else 0 := by
  classical
  rw [transferBlock_apply, transferMatrix_apply]
  by_cases hxy : x = y
  · simp [hxy]
  · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    simp [hxy, hval]
    by_cases hi : Interlaced x.1 y.1
    · simp [hi]
      have hcard : (Finset.univ.filter fun i => Psi x.1 i ≠ Psi y.1 i).card =
          2 * (x.1 \ y.1).card := by
        simpa [arrowDistance] using arrowDistance_state x y
      rw [hcard, pow_mul, Real.sq_sqrt]
      · linarith
    · simp [hi]

private theorem cor34_transferBlock_entry_analyticAt {N n : ℕ} (x y : State N n)
    {Δ : ℝ} (hΔ : Δ < -1) :
    AnalyticAt ℝ (fun d => transferBlock N (Real.sqrt (2 - 2 * d)) n x y) Δ := by
  classical
  let P : ℝ → ℝ := fun d =>
    if x = y then 2 else
      if Interlaced x.1 y.1 then (2 - 2 * d) ^ (x.1 \ y.1).card else 0
  have hP : AnalyticAt ℝ P Δ := by
    by_cases hxy : x = y
    · simpa [P, hxy] using
        (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (2 : ℝ)) Δ)
    · by_cases hi : Interlaced x.1 y.1
      · have hlin : AnalyticAt ℝ (fun d : ℝ => 2 - 2 * d) Δ := by fun_prop
        have hpow : AnalyticAt ℝ
            (fun d : ℝ => (2 - 2 * d) ^ (x.1 \ y.1).card) Δ := by
          convert hlin.pow (x.1 \ y.1).card using 1
        simpa [P, hxy, hi] using hpow
      · simpa [P, hxy, hi] using
          (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) Δ)
  have hEq :
      (fun d => transferBlock N (Real.sqrt (2 - 2 * d)) n x y) =ᶠ[𝓝 Δ] P := by
    filter_upwards [Iio_mem_nhds (show Δ < 1 by linarith)] with d hd
    exact cor34_transferBlock_sqrt_entry x y hd
  exact hP.congr hEq.symm

/-- For every `n ≤ N` and `Δ < -1`, the Perron root of the transfer block is a simple
characteristic root. The proof uses primitivity of the block at `c = √(2 - 2Δ)`. -/
theorem cor34_transferBlock_pfRoot_simple {N n : ℕ} (hn : n ≤ N) {Δ : ℝ}
    (hΔ : Δ < -1) :
    (transferBlock N (Real.sqrt (2 - 2 * Δ)) n).charpoly.rootMultiplicity
      (pfRoot (transferBlock N (Real.sqrt (2 - 2 * Δ)) n)) = 1 := by
  have hc : 0 < Real.sqrt (2 - 2 * Δ) := Real.sqrt_pos.2 (by linarith)
  obtain ⟨_, _, _, _, hsimple, _⟩ := transferBlock_perronFrobenius hc hn
  exact hsimple

/-- The transfer-block Perron root is real-analytic at every `Δ < -1`, hence real-analytic on
the whole source interval `(-∞,-1)`. -/
theorem cor34_analyticAt_pfRoot_transferBlock {N n : ℕ} (hn : n ≤ N) {Δ : ℝ}
    (hΔ : Δ < -1) :
    AnalyticAt ℝ (fun d => pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n)) Δ := by
  classical
  have : Nonempty (State N n) := ⟨packed hn⟩
  let A : ℝ → Matrix (State N n) (State N n) ℝ := fun d =>
    transferBlock N (Real.sqrt (2 - 2 * d)) n
  have hA : ∀ i j, AnalyticAt ℝ (fun d => A d i j) Δ := by
    intro i j
    exact cor34_transferBlock_entry_analyticAt i j hΔ
  have hHerm : ∀ d, (A d).IsHermitian := fun d => transferBlock_isHermitian n
  have hsimple : (A Δ).charpoly.rootMultiplicity (sSup (spectrum ℝ (A Δ))) = 1 := by
    simpa [A, pfRoot] using cor34_transferBlock_pfRoot_simple hn hΔ
  have hanalytic := AnalyticTools.analyticAt_pfRoot_of_simple hA (hHerm Δ)
    (Filter.Eventually.of_forall hHerm) hsimple
  simpa [A, pfRoot] using hanalytic

/-- Polynomial extension in ε = 1/Δ of the normalized transfer block. -/
noncomputable def cor34_normalizedTransferBlock (N n : ℕ) (ε : ℝ) :
    Matrix (State N n) (State N n) ℝ :=
  fun x y =>
    if x = y then 2 * (-ε / 2) ^ n
    else if Interlaced x.1 y.1 then
      (-ε / 2) ^ (n - (x.1 \ y.1).card) * (1 - ε) ^ (x.1 \ y.1).card
    else 0

private theorem cor34_state_sdiff_le {N n : ℕ} (x y : State N n) :
    (x.1 \ y.1).card ≤ n :=
  (Finset.card_le_card Finset.sdiff_subset).trans_eq x.2

/-- The polynomial family has the infinity block as its value at zero. -/
theorem cor34_normalizedTransferBlock_zero (N n : ℕ) :
    cor34_normalizedTransferBlock N n 0 = infinityBlock N n := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    by_cases hn0 : n = 0
    · simp [cor34_normalizedTransferBlock, infinityBlock, hn0]
    · simp [cor34_normalizedTransferBlock, infinityBlock, hn0]
  · by_cases hi : Interlaced x.1 y.1
    · let m := (x.1 \ y.1).card
      have hmle : m ≤ n := cor34_state_sdiff_le x y
      have hdis : m = n ↔ Disjoint x.1 y.1 := by
        constructor
        · intro hm
          apply (arrowDistance_eq_two_mul_iff x y).1
          have hmc : (x.1 \ y.1).card = n := by simpa [m] using hm
          rw [arrowDistance_state, hmc]
        · intro hd
          have h := (arrowDistance_eq_two_mul_iff x y).2 hd
          rw [arrowDistance_state] at h
          omega
      by_cases hd : Disjoint x.1 y.1
      · have hm : m = n := hdis.mpr hd
        simp [cor34_normalizedTransferBlock, infinityBlock, hxy, hi, hd, m, hm]
      · have hm : m ≠ n := fun h => hd (hdis.mp h)
        have hmn : m < n := lt_of_le_of_ne hmle hm
        have hexp : n - m ≠ 0 := Nat.sub_ne_zero_of_lt hmn
        simp [cor34_normalizedTransferBlock, infinityBlock, hxy, hi, hd, m, hexp]
    · simp [cor34_normalizedTransferBlock, infinityBlock, hxy, hi]

/-- Every matrix entry of the normalized family is analytic at every real ε. -/
theorem cor34_normalizedTransferBlock_entry_analyticAt {N n : ℕ} (x y : State N n)
    (ε : ℝ) :
    AnalyticAt ℝ (fun t => cor34_normalizedTransferBlock N n t x y) ε := by
  classical
  by_cases hxy : x = y
  · simp [cor34_normalizedTransferBlock, hxy]
    fun_prop
  · by_cases hi : Interlaced x.1 y.1
    · simp [cor34_normalizedTransferBlock, hxy, hi]
      fun_prop
    · simpa [cor34_normalizedTransferBlock, hxy, hi] using
        (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) ε)

/-- The normalized family is symmetric for every ε. -/
theorem cor34_normalizedTransferBlock_symm {N n : ℕ} (ε : ℝ)
    (x y : State N n) :
    cor34_normalizedTransferBlock N n ε x y =
      cor34_normalizedTransferBlock N n ε y x := by
  classical
  by_cases hxy : x = y
  · subst y
    rfl
  · have hcard : (x.1 \ y.1).card = (y.1 \ x.1).card :=
      Finset.card_sdiff_comm (x.2.trans y.2.symm)
    simp [cor34_normalizedTransferBlock, hxy, eq_comm, interlaced_comm, hcard]

/-- The normalized family is Hermitian for every ε. -/
theorem cor34_normalizedTransferBlock_isHermitian {N n : ℕ} (ε : ℝ) :
    (cor34_normalizedTransferBlock N n ε).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext x y
  exact cor34_normalizedTransferBlock_symm ε y x

/-- The power identity for a normalized off diagonal transfer entry. -/
private theorem cor34_normalized_power_identity {n m : ℕ} (hm : m ≤ n)
    {ε : ℝ} (hε : ε < 0) :
    (-ε / 2) ^ (n - m) * (1 - ε) ^ m =
      ((-2 / ε : ℝ) ^ n)⁻¹ * (2 - 2 / ε) ^ m := by
  let q : ℝ := -2 / ε
  have hεne : ε ≠ 0 := ne_of_lt hε
  have hq : q ≠ 0 := by
    dsimp [q]
    exact div_ne_zero (by norm_num) hεne
  have hqinv : q⁻¹ = -ε / 2 := by
    dsimp [q]
    field_simp [hεne]
  have hbase : 2 - 2 / ε = q * (1 - ε) := by
    dsimp [q]
    field_simp [hεne]
    ring
  have hn : n = m + (n - m) := by omega
  have hqpow : q ^ n = q ^ m * q ^ (n - m) := by
    calc
      q ^ n = q ^ (m + (n - m)) := by
        conv_lhs => rw [hn]
      _ = q ^ m * q ^ (n - m) := pow_add q m (n - m)
  calc
    (-ε / 2) ^ (n - m) * (1 - ε) ^ m =
        (q⁻¹) ^ (n - m) * (1 - ε) ^ m := by rw [hqinv]
    _ = (q ^ (n - m))⁻¹ * (1 - ε) ^ m := by rw [← inv_pow]
    _ = (q ^ n)⁻¹ * (q ^ m * (1 - ε) ^ m) := by
      rw [hqpow]
      field_simp [hq]
    _ = (q ^ n)⁻¹ * (2 - 2 / ε) ^ m := by rw [← mul_pow, hbase]
    _ = ((-2 / ε : ℝ) ^ n)⁻¹ * (2 - 2 / ε) ^ m := by rfl

/-- For ε < 0, the polynomial matrix is exactly the transfer block divided by
(-2/ε)^n, that is, by (-2Δ)^n with Δ = 1/ε. -/
theorem cor34_normalizedTransferBlock_eq_scaled_transferBlock {N n : ℕ} (ε : ℝ)
    (hε : ε < 0) :
    cor34_normalizedTransferBlock N n ε =
      ((-2 / ε : ℝ) ^ n)⁻¹ •
        transferBlock N (Real.sqrt (2 - 2 / ε)) n := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    have hqinv : ((-2 / ε : ℝ)⁻¹) = -ε / 2 := by
      field_simp [ne_of_lt hε]
    have hqpow : ((-2 / ε : ℝ) ^ n)⁻¹ = (-ε / 2) ^ n := by
      rw [← inv_pow, hqinv]
    simp [cor34_normalizedTransferBlock, Matrix.smul_apply, smul_eq_mul,
      transferBlock_apply_self, hqpow]
    ring
  · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    by_cases hi : Interlaced x.1 y.1
    · let m := (x.1 \ y.1).card
      have hmle : m ≤ n := cor34_state_sdiff_le x y
      have hdelta : 1 / ε < 1 := by
        have hinv : 1 / ε < 0 := one_div_neg.mpr hε
        have hone : (1 : ℝ) / ε = ε⁻¹ := by simp
        rw [hone]
        linarith
      have hraw :
          transferBlock N (Real.sqrt (2 - 2 / ε)) n x y =
            (2 - 2 / ε) ^ m := by
        simpa [m, div_eq_mul_inv, hxy, hval, hi] using
          cor34_transferBlock_sqrt_entry x y hdelta
      simp only [cor34_normalizedTransferBlock, hxy, hi, Matrix.smul_apply,
        smul_eq_mul]
      rw [hraw]
      exact cor34_normalized_power_identity hmle hε
    · simp [cor34_normalizedTransferBlock, hxy, hval, hi, Matrix.smul_apply,
        transferBlock_apply, transferMatrix_apply]

/-- Multiplication of a Hermitian matrix by a nonnegative real scales its largest spectral
value by the same factor. -/
private theorem cor34_pfRoot_smul_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (A : Matrix ι ι ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hA : A.IsHermitian) :
    pfRoot (q • A) = q * pfRoot A := by
  have hspec : (spectrum ℝ A).Nonempty := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact Set.range_nonempty _
  change sSup (spectrum ℝ (q • A)) = q * sSup (spectrum ℝ A)
  rw [spectrum.smul_eq_smul q A hspec, Real.sSup_smul_of_nonneg hq]
  rfl

/-- The normalized Perron root agrees exactly with the polynomial-family Perron root for
ε < 0. -/
theorem cor34_pfRoot_normalizedTransferBlock_eq {N n : ℕ} (hn : n ≤ N)
    {ε : ℝ} (hε : ε < 0) :
    pfRoot (cor34_normalizedTransferBlock N n ε) =
      pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n := by
  classical
  have : Nonempty (State N n) := ⟨packed hn⟩
  have hbase : 0 < (-2 / ε : ℝ) := by
    rw [show (-2 : ℝ) / ε = 2 / (-ε) by field_simp [ne_of_lt hε]]
    exact div_pos (by norm_num) (neg_pos.mpr hε)
  have hq : 0 ≤ ((-2 / ε : ℝ) ^ n)⁻¹ :=
    (inv_pos.mpr (pow_pos hbase n)).le
  calc
    pfRoot (cor34_normalizedTransferBlock N n ε) =
        pfRoot (((-2 / ε : ℝ) ^ n)⁻¹ •
          transferBlock N (Real.sqrt (2 - 2 / ε)) n) :=
      congrArg pfRoot (cor34_normalizedTransferBlock_eq_scaled_transferBlock ε hε)
    _ = ((-2 / ε : ℝ) ^ n)⁻¹ *
        pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) :=
      cor34_pfRoot_smul_nonneg _ _ hq (transferBlock_isHermitian n)
    _ = pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n := by
      simp [div_eq_mul_inv, mul_comm]

end PottsDiscontinuity.SixVertex
