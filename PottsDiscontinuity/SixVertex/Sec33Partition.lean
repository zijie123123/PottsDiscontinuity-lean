module

public import PottsDiscontinuity.SixVertex.BlockPerronFrobenius

/-!
# Six-vertex sector maxima and trace bounds

This file packages the finite-sector maximum of the block Perron roots and the trace estimates
used in §3.3.  The full partition function is a sum of the fixed-arrow-number sectors.
-/

@[expose] public section

open Finset Matrix Filter Topology PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N M : ℕ} {c : ℝ}

/-- The largest Perron root among the arrow-number blocks `V^[n]`, `0 ≤ n ≤ N`. -/
noncomputable def LambdaMax (c : ℝ) (N : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin (N + 1))).sup' Finset.univ_nonempty
    (fun n => pfRoot (transferBlock N c n.val))

/-- Every block Perron root is bounded by `LambdaMax`. -/
theorem pfRoot_transferBlock_le_LambdaMax {n : ℕ} (hn : n ≤ N) :
    pfRoot (transferBlock N c n) ≤ LambdaMax c N := by
  unfold LambdaMax
  exact Finset.le_sup' (fun i : Fin (N + 1) => pfRoot (transferBlock N c i.val))
    (Finset.mem_univ (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (N + 1)))

/-- `LambdaMax` is attained by one of the arrow-number blocks. -/
theorem exists_pfRoot_eq_LambdaMax :
    ∃ n ≤ N, pfRoot (transferBlock N c n) = LambdaMax c N := by
  have hself : LambdaMax c N ≤ LambdaMax c N := le_rfl
  unfold LambdaMax at hself
  obtain ⟨i, hi, hle⟩ := (Finset.le_sup'_iff (s := Finset.univ)
    (H := Finset.univ_nonempty) (f := fun n : Fin (N + 1) =>
      pfRoot (transferBlock N c n.val))).mp hself
  have hlow : pfRoot (transferBlock N c i.val) ≤ LambdaMax c N :=
    pfRoot_transferBlock_le_LambdaMax (N := N) (c := c)
      (Nat.lt_succ_iff.mp i.isLt)
  exact ⟨i.val, Nat.lt_succ_iff.mp i.isLt, le_antisymm hlow hle⟩

/-- Positivity of the maximal block Perron root. -/
theorem LambdaMax_pos (hc : 0 < c) : 0 < LambdaMax c N := by
  obtain ⟨n, hn, hmax⟩ := exists_pfRoot_eq_LambdaMax (c := c) (N := N)
  rw [← hmax]
  exact (transferBlock_perronFrobenius (N := N) hc hn).1

/-- The dimension of all fixed-cardinality state spaces sums to the dimension of the full state
space `Finset (Fin N)`, namely `2^N`. -/
noncomputable def stateCardEquiv (N : ℕ) :
    Finset (Fin N) ≃ Σ n : Fin (N + 1), State N n.val where
  toFun x := ⟨⟨x.card, by
      have hx := Finset.card_le_univ x
      rw [Fintype.card_fin] at hx
      exact Nat.lt_succ_of_le hx⟩, ⟨x, rfl⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨n, hn⟩, ⟨s, hs⟩⟩
    change s.card = n at hs
    subst n
    rfl

theorem sum_state_card_eq_two_pow (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), Fintype.card (State N n)) = 2 ^ N := by
  have hcard := Fintype.card_congr (stateCardEquiv N)
  rw [Fintype.card_finset, Fintype.card_sigma] at hcard
  have hsum : (∑ i : Fin (N + 1), Fintype.card (State N i.val)) =
      ∑ n ∈ Finset.range (N + 1), Fintype.card (State N n) := by
    exact Fin.sum_univ_eq_sum_range (fun n => Fintype.card (State N n)) (N + 1)
  rw [Fintype.card_fin] at hcard
  calc
    (∑ n ∈ Finset.range (N + 1), Fintype.card (State N n)) =
        ∑ i : Fin (N + 1), Fintype.card (State N i.val) := hsum.symm
    _ = 2 ^ N := hcard.symm

/-- For a symmetric nonnegative matrix, every trace power is bounded by its dimension times the
`M`-th power of its largest eigenvalue. -/
theorem trace_pow_le_card_mul_pfRoot_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hnn : ∀ i j, 0 ≤ A i j) (_hρ : 0 < pfRoot A) (M : ℕ) :
    (A ^ M).trace ≤ (Fintype.card ι : ℝ) * pfRoot A ^ M := by
  rw [trace_pow_eq_sum hA]
  calc
    (∑ i, hA.eigenvalues i ^ M) ≤ ∑ _i : ι, pfRoot A ^ M := by
      apply Finset.sum_le_sum
      intro i _
      have hμ := abs_le_pfRoot_of_mem_spectrum hA hnn (hA.eigenvalues_mem_spectrum_real i)
      calc
        hA.eigenvalues i ^ M ≤ |hA.eigenvalues i| ^ M := by
          have := le_abs_self (hA.eigenvalues i ^ M)
          simpa only [abs_pow] using this
        _ ≤ pfRoot A ^ M := pow_le_pow_left₀ (abs_nonneg _) hμ M
    _ = (Fintype.card ι : ℝ) * pfRoot A ^ M := by simp

/-- For even `M`, the trace of a symmetric nonnegative matrix is at least the `M`-th power of its
largest eigenvalue. -/
theorem trace_pow_ge_pfRoot_pow_even {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {M : ℕ}
    (hM : Even M) : pfRoot A ^ M ≤ (A ^ M).trace := by
  rw [trace_pow_eq_sum hA]
  obtain ⟨i₀, hi₀⟩ := exists_eigenvalues_eq_pfRoot hA
  have hsingle := Finset.single_le_sum
    (s := Finset.univ) (f := fun i : ι => hA.eigenvalues i ^ M)
    (fun i _ => by
      rcases hM with ⟨k, rfl⟩
      rw [pow_add]
      exact mul_self_nonneg _)
    (Finset.mem_univ i₀)
  rw [hi₀] at hsingle
  exact hsingle

/-- Powers of a matrix with nonnegative entries still have nonnegative entries. -/
theorem matrix_pow_entry_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    ∀ k i j, 0 ≤ (A ^ k) i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      by_cases h : i = j <;> simp [h]
  | succ k ih =>
      intro i j
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

/-- Positive diagonal entries persist under every matrix power when all entries are
nonnegative. -/
theorem matrix_pow_diag_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) (hdiag : ∀ i, 0 < A i i) :
    ∀ k i, 0 < (A ^ k) i i := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih =>
      intro i
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      exact Finset.sum_pos' (fun j _ =>
        mul_nonneg (matrix_pow_entry_nonneg hA k i j) (hA j i))
        ⟨i, Finset.mem_univ i, mul_pos (ih i) (hdiag i)⟩

/-- A symmetric or nonsymmetric matrix with nonnegative entries and positive diagonal has
positive trace in every power. -/
theorem trace_pow_pos_of_nonneg_pos_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hdiag : ∀ i, 0 < A i i) (M : ℕ) : 0 < (A ^ M).trace := by
  rw [Matrix.trace]
  exact Finset.sum_pos (fun i _ => matrix_pow_diag_pos hA hdiag M i) Finset.univ_nonempty

/-- Every fixed-arrow-number sector is nonnegative when `c ≥ 0`. -/
theorem Z6Vn_nonneg (hc : 0 ≤ c) (M n : ℕ) : 0 ≤ Z6Vn c N M n := by
  unfold Z6Vn
  exact Finset.sum_nonneg fun ω _ => by
    unfold w6V1 w6V
    split_ifs <;> positivity

/-- A fixed-arrow-number sector is bounded above by its state-space dimension times the block
Perron root to the `M`-th power. -/
theorem Z6Vn_le_card_mul_pfRoot_pow (hc : 0 < c) (hN : 0 < N) (hM : 0 < M)
    {n : ℕ} (hn : n ≤ N) :
    Z6Vn c N M n ≤ (Fintype.card (State N n) : ℝ) *
      pfRoot (transferBlock N c n) ^ M := by
  rw [Z6Vn_eq_trace_block hN hM c n]
  let : Nonempty (State N n) := ⟨packed hn⟩
  have hρ := (transferBlock_perronFrobenius (N := N) hc hn).1
  exact trace_pow_le_card_mul_pfRoot_pow (transferBlock_isHermitian (N := N) (c := c) n)
    (transferBlock_nonneg hc.le n) hρ M

/-- Every fixed-arrow-number sector with an admissible cardinality is strictly positive for
positive height. -/
theorem Z6Vn_pos (hc : 0 < c) (hN : 0 < N) (hM : 0 < M) {n : ℕ}
    (hn : n ≤ N) : 0 < Z6Vn c N M n := by
  rw [Z6Vn_eq_trace_block hN hM c n]
  let : Nonempty (State N n) := ⟨packed hn⟩
  exact trace_pow_pos_of_nonneg_pos_diag (transferBlock_nonneg hc.le n)
    (fun x => by rw [transferBlock_apply_self]; norm_num) M

/-- The full partition function dominates each fixed-arrow-number sector. -/
theorem Z6Vn_le_Z6V (hc : 0 ≤ c) (hM : 0 < M) {n : ℕ} (hn : n ≤ N) :
    Z6Vn c N M n ≤ Z6V c N M := by
  rw [Z6V_eq_sum_Z6Vn hM c]
  exact Finset.single_le_sum (fun k _ => Z6Vn_nonneg (N := N) hc M k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/-- The `r`-sector trace dominates its Perron root on positive even heights. -/
theorem Lambda_pow_le_Z6Vr_even (_hc : 0 < c) (hN : 0 < N) (hM : 0 < M)
    {r : ℕ} (hr : r ≤ N / 2) (heven : Even M) :
    Lambda c N r ^ M ≤ Z6Vr c N M r := by
  rw [Z6Vr_eq_trace_block hN hM c hr]
  unfold Lambda
  let : Nonempty (State N (N / 2 - r)) := ⟨packed (by omega)⟩
  have hA := transferBlock_isHermitian (N := N) (c := c) (N / 2 - r)
  exact trace_pow_ge_pfRoot_pow_even hA heven

/-- At zero height the centered sector for `N = 2` is empty, because `absUp` is defined as zero
when there are no rows. -/
theorem Z6Vr_zero_height_eq_zero (c : ℝ) : Z6Vr c 2 0 0 = 0 := by
  unfold Z6Vr
  simp [ArrowConfig.absUp]

/-- The lower trace bound cannot include zero height: at `N = 2`, `r = 0`, the left side is one
and the sector partition function is zero. -/
theorem not_Lambda_pow_le_Z6Vr_zero_height (c : ℝ) :
    ¬ Lambda c 2 0 ^ 0 ≤ Z6Vr c 2 0 0 := by
  rw [Z6Vr_zero_height_eq_zero, pow_zero]
  norm_num

/-- The full six-vertex partition function has the uniform trace upper bound from the largest
block root. -/
theorem Z6V_le_two_pow_mul_LambdaMax_pow (hc : 0 < c) (hN : 0 < N) (hM : 0 < M) :
    Z6V c N M ≤ (2 ^ N : ℝ) * LambdaMax c N ^ M := by
  rw [Z6V_eq_sum_Z6Vn hM c]
  calc
    (∑ n ∈ Finset.range (N + 1), Z6Vn c N M n) ≤
        ∑ n ∈ Finset.range (N + 1),
          (Fintype.card (State N n) : ℝ) * LambdaMax c N ^ M := by
      apply Finset.sum_le_sum
      intro n hn
      have hnle : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      have hbound := Z6Vn_le_card_mul_pfRoot_pow hc hN hM hnle
      have hroot := pfRoot_transferBlock_le_LambdaMax (N := N) (c := c) hnle
      have hρ := (transferBlock_perronFrobenius (N := N) hc hnle).1
      calc
        Z6Vn c N M n ≤ (Fintype.card (State N n) : ℝ) * pfRoot (transferBlock N c n) ^ M := hbound
        _ ≤ (Fintype.card (State N n) : ℝ) * LambdaMax c N ^ M := by
          gcongr
    _ = (∑ n ∈ Finset.range (N + 1), (Fintype.card (State N n) : ℝ)) *
        LambdaMax c N ^ M := by rw [Finset.sum_mul]
    _ = (2 ^ N : ℝ) * LambdaMax c N ^ M := by
      have hcard : (∑ n ∈ Finset.range (N + 1),
          (Fintype.card (State N n) : ℝ)) = (2 ^ N : ℝ) := by
        norm_cast
        exact sum_state_card_eq_two_pow N
      rw [hcard]

/-- The sector growth rate at a maximizing block gives the full six-vertex free-energy rate. -/
theorem tendsto_log_Z6V (hc : 0 < c) (hN : 0 < N) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6V c N M)) atTop
      (𝓝 (Real.log (LambdaMax c N))) := by
  obtain ⟨n, hn, hmax⟩ := exists_pfRoot_eq_LambdaMax (c := c) (N := N)
  have hsector := tendsto_log_Z6Vn (N := N) hc hN hn
  have hsector' : Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6Vn c N M n))
      atTop (𝓝 (Real.log (LambdaMax c N))) := by
    simpa [hmax] using hsector
  have hlam := LambdaMax_pos (c := c) (N := N) hc
  have hconst : 0 < (2 ^ N : ℝ) := by positivity
  have hinv : Tendsto (fun M : ℕ => 1 / (M : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsmall : Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (2 ^ N : ℝ))
      atTop (𝓝 0) := by simpa using hinv.mul_const (Real.log (2 ^ N : ℝ))
  have hupper' : Tendsto (fun M : ℕ => Real.log (LambdaMax c N) +
      (1 / (M : ℝ)) * Real.log (2 ^ N : ℝ)) atTop
      (𝓝 (Real.log (LambdaMax c N))) := by
    simpa using (tendsto_const_nhds (x := Real.log (LambdaMax c N))).add hsmall
  have hupper : Tendsto (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log ((2 ^ N : ℝ) * LambdaMax c N ^ M)) atTop
      (𝓝 (Real.log (LambdaMax c N))) := by
    refine hupper'.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M hM
    have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have hpow : LambdaMax c N ^ M ≠ 0 := pow_ne_zero _ hlam.ne'
    rw [Real.log_mul hconst.ne' hpow]
    simp only [Real.log_pow]
    field_simp
    ring_nf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6V c N M))
    (g := fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6Vn c N M n))
    (h := fun M : ℕ => (1 / (M : ℝ)) *
      Real.log ((2 ^ N : ℝ) * LambdaMax c N ^ M))
    hsector' hupper
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hsectorpos := Z6Vn_pos (N := N) hc hN hM hn
    have hfullpos : 0 < Z6V c N M := lt_of_lt_of_le hsectorpos
      (Z6Vn_le_Z6V (N := N) hc.le hM hn)
    have hlog := Real.log_le_log hsectorpos (Z6Vn_le_Z6V (N := N) hc.le hM hn)
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hsectorpos := Z6Vn_pos (N := N) hc hN hM hn
    have hfullpos : 0 < Z6V c N M := lt_of_lt_of_le hsectorpos
      (Z6Vn_le_Z6V (N := N) hc.le hM hn)
    have hup := Z6V_le_two_pow_mul_LambdaMax_pow (N := N) hc hN hM
    have hlog := Real.log_le_log hfullpos hup
    exact mul_le_mul_of_nonneg_left hlog (by positivity)

end PottsDiscontinuity.SixVertex
