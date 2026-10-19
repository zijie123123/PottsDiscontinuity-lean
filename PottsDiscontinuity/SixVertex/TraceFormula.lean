module

public import PottsDiscontinuity.SixVertex.RowTransfer
public import PottsDiscontinuity.SixVertex.PathSum

/-!
# The trace formulas `Z_6V(N,M) = tr (V^M)` and `Z^{(r)}_{6V}(N,M) = tr ((V^{[N/2-r]})^M)`

Companion paper [8], arXiv:1611.09909v1, Proposition 2.1 (proof in §4), and the main
paper arXiv:1611.09877v2, §3.3 (the trace formula for the sector partition functions
`Z^{(r)}_{6V}` used in the proof of Theorem 1.2).

An arrow configuration of the torus is the same thing as the family of its rows: the up arrows
`x_j = {i : vert (i, j)}` between rows `j` and `j + 1` and the horizontal arrows of each row.
By the multiplicative structure of the weight, `Z_6V = ∑_x ∏_j Ṽ(x_{j-1}, x_j)`, and `Ṽ = V`
(`rowSum_eq_transferMatrix`).  Throughout `N, M ≥ 1`.

The block statements are proved exactly in the form `Z6Vn c N M n = tr ((V^{[n]})^M)` (the sum over
arrow configurations with `n` up arrows per row) and `Z6Vr c N M r = tr ((V^{[N/2-r]})^M)` for
`r ≤ N/2`.  They hold for every `N ≥ 1`, not only even `N` (for odd `N` the exponent `N/2` is
integer division); `Z6Vr c N M r = 0` for `r > N/2`.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N M : ℕ}

/-! ### Rows of vertical arrows -/

/-- The up arrows between row `j` and row `j + 1`, as a subset of `Fin N`. -/
def stateRows (V : Fin N × Fin M → Bool) : Fin M → Finset (Fin N) :=
  fun j => univ.filter fun i => V (i, j) = true

/-- Vertical edge fields correspond to families of states, one per row. -/
def stateRowsEquiv (N M : ℕ) : (Fin N × Fin M → Bool) ≃ (Fin M → Finset (Fin N)) where
  toFun := stateRows
  invFun x p := decide (p.1 ∈ x p.2)
  left_inv V := by funext p; simp [stateRows]
  right_inv x := by funext j; ext i; simp [stateRows]

theorem decide_mem_stateRows (V : Fin N × Fin M → Bool) (i : Fin N) (j : Fin M) :
    decide (i ∈ stateRows V j) = V (i, j) := by
  simp [stateRows]

/-- `∑ H ∏_j G j (row j of H) = ∏_j ∑_h G j h`. -/
theorem sum_prod_rows (G : Fin M → (Fin N → Bool) → ℝ) :
    ∑ H : Fin N × Fin M → Bool, ∏ j, G j (fun i => H (i, j)) = ∏ j, ∑ h : Fin N → Bool, G j h := by
  let e : (Fin N × Fin M → Bool) ≃ (Fin M → Fin N → Bool) :=
    (Equiv.curry _ _ _).trans (Equiv.piComm _)
  calc ∑ H : Fin N × Fin M → Bool, ∏ j, G j (fun i => H (i, j))
      = ∑ x : Fin M → Fin N → Bool, ∏ j, G j (x j) :=
        Fintype.sum_equiv e _ _ (fun H => rfl)
    _ = ∏ j, ∑ h : Fin N → Bool, G j h := by
        have := Finset.sum_prod_piFinset (univ : Finset (Fin N → Bool)) G
        rwa [Fintype.piFinset_univ] at this

/-- The key decomposition of the sum over arrow configurations into rows. -/
theorem sum_weight_mul (c : ℝ) (Φ : (Fin M → Finset (Fin N)) → ℝ) :
    ∑ ω : ArrowConfig N M, Φ (stateRows ω.vert) * w6V1 c ω =
      ∑ x : Fin M → Finset (Fin N), Φ x * ∏ j, rowSum c (x (prv j)) (x j) := by
  -- the weight as a function of the two fields
  let W : (Fin N × Fin M → Bool) → (Fin N × Fin M → Bool) → ℝ := fun H V =>
    ∏ v : Fin N × Fin M, localWeight 1 1 c (H (prv v.1, v.2)) (H v) (V (v.1, prv v.2)) (V v)
  have h1 : ∀ ω : ArrowConfig N M, Φ (stateRows ω.vert) * w6V1 c ω =
      Φ (stateRows ω.vert) * W ω.horiz ω.vert := fun ω => by
    rw [w6V1_eq_prod]; rfl
  simp_rw [h1]
  refine (Fintype.sum_equiv (ArrowConfig.equivProd N M) _
    (fun p : (Fin N × Fin M → Bool) × (Fin N × Fin M → Bool) => Φ (stateRows p.2) * W p.1 p.2)
    (fun ω => rfl)).trans ?_
  rw [Fintype.sum_prod_type_right]
  -- sum over the horizontal fields for a fixed vertical field
  have h2 : ∀ V : Fin N × Fin M → Bool, ∑ H, W H V =
      ∏ j, rowSum c (stateRows V (prv j)) (stateRows V j) := by
    intro V
    have hW : ∀ H, W H V = ∏ j, (∏ i : Fin N, localWeight 1 1 c (H (prv i, j)) (H (i, j))
        (V (i, prv j)) (V (i, j))) := fun H => Fintype.prod_prod_type_right _
    simp_rw [hW]
    rw [sum_prod_rows (fun j h => ∏ i : Fin N, localWeight 1 1 c (h (prv i)) (h i)
      (V (i, prv j)) (V (i, j)))]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold rowSum rowWeight
    simp_rw [decide_mem_stateRows]
  simp_rw [← Finset.mul_sum, h2]
  exact Fintype.sum_equiv (stateRowsEquiv N M) _ _ (fun V => rfl)

/-- The partition function as a sum over closed chains of states. -/
theorem Z6V_eq_sum_chain (hN : 0 < N) (c : ℝ) :
    Z6V c N M = ∑ x : Fin M → Finset (Fin N), ∏ j, transferMatrix N c (x (prv j)) (x j) := by
  have := sum_weight_mul (N := N) (M := M) c (fun _ => 1)
  simp only [one_mul] at this
  unfold Z6V
  rw [this]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Finset.prod_congr rfl fun j _ => rowSum_eq_transferMatrix hN c _ _

/-- Reindexing a cyclic product: `∏_j A (x (j - 1)) (x j) = ∏_j A (x j) (x (j + 1))`. -/
theorem prod_prv_eq_prod_nxt {S : Type*} (A : S → S → ℝ) (x : Fin M → S) :
    ∏ j : Fin M, A (x (prv j)) (x j) = ∏ j : Fin M, A (x j) (x (finRotate M j)) := by
  calc ∏ j : Fin M, A (x (prv j)) (x j)
      = ∏ j : Fin M, A (x (prv (finRotate M j))) (x (finRotate M j)) :=
        (Equiv.prod_comp (finRotate M) (fun j => A (x (prv j)) (x j))).symm
    _ = ∏ j : Fin M, A (x j) (x (finRotate M j)) :=
        Finset.prod_congr rfl fun j _ => by simp only [prv, Equiv.symm_apply_apply]

/-- **Proposition 2.1 of the companion paper.** `Z_6V(N, M) = tr (V ^ M)` for `N, M ≥ 1`. -/
theorem Z6V_eq_trace (hN : 0 < N) (hM : 0 < M) (c : ℝ) :
    Z6V c N M = Matrix.trace ((transferMatrix N c) ^ M) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  rw [Z6V_eq_sum_chain hN, trace_pow_succ_eq_sum_chain]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact prod_prv_eq_prod_nxt (fun a b => transferMatrix N c a b) x

/-! ### Blocks -/

/-- If a closed chain has nonzero weight, all its states have the same number of entries. -/
theorem card_const_of_prod_ne_zero (hM : 0 < M) (c : ℝ) (x : Fin M → Finset (Fin N))
    (h : ∏ j, transferMatrix N c (x (prv j)) (x j) ≠ 0) :
    ∀ j, (x j).card = (x ⟨0, hM⟩).card := by
  have hstep : ∀ j, (x (prv j)).card = (x j).card := by
    intro j
    by_contra hne
    exact h (Finset.prod_eq_zero (mem_univ j) (transferMatrix_apply_eq_zero_of_card_ne hne))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  intro j
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
    rw [← hstep (Fin.succ j), prv_succ]
    exact ih

theorem absUp_eq_card (hM : 0 < M) (ω : ArrowConfig N M) :
    ω.absUp = (stateRows ω.vert ⟨0, hM⟩).card := by
  simp [ArrowConfig.absUp, ArrowConfig.rowUp, stateRows, hM]

/-- The part of `Z_6V` with `n` up arrows per row, as a sum over closed chains. -/
theorem Z6Vn_eq_sum_chain (hN : 0 < N) (hM : 0 < M) (c : ℝ) (n : ℕ) :
    Z6Vn c N M n = ∑ x : Fin M → Finset (Fin N),
      if (x ⟨0, hM⟩).card = n then ∏ j, transferMatrix N c (x (prv j)) (x j) else 0 := by
  have := sum_weight_mul (N := N) (M := M) c (fun x => if (x ⟨0, hM⟩).card = n then 1 else 0)
  unfold Z6Vn
  rw [Finset.sum_filter]
  have h1 : ∀ ω : ArrowConfig N M, (if ω.absUp = n then w6V1 c ω else 0) =
      (if (stateRows ω.vert ⟨0, hM⟩).card = n then 1 else 0) * w6V1 c ω := by
    intro ω
    rw [absUp_eq_card hM]
    split_ifs <;> simp
  simp_rw [h1]
  rw [this]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp_rw [rowSum_eq_transferMatrix hN]
  split_ifs <;> simp

/-- The closed-chain expression of the trace of the `M`-th power of a block `V^{[n]}`. -/
theorem trace_block_pow_eq_sum_chain (hM : 0 < M) (c : ℝ) (n : ℕ) :
    Matrix.trace ((transferBlock N c n) ^ M) = ∑ x : Fin M → Finset (Fin N),
      if (∀ j, (x j).card = n) then ∏ j, transferMatrix N c (x (prv j)) (x j) else 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  rw [trace_pow_succ_eq_sum_chain]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (Finset.univ.filter fun x : Fin (m + 1) → Finset (Fin N) =>
    ∀ j, (x j).card = n) (p := fun x : Fin (m + 1) → Finset (Fin N) => ∀ j, (x j).card = n)
    (by intro x; simp)]
  rw [← (Equiv.subtypePiEquivPi (β := fun _ : Fin (m + 1) => Finset (Fin N))
    (p := fun _ s => s.card = n)).sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (Finset.prod_congr rfl fun j _ => rfl).trans
    (prod_prv_eq_prod_nxt (fun a b => transferMatrix N c a b) x.1).symm

/-- **Block trace formula.** The part of the partition function with `n` up arrows per row is
`tr ((V^{[n]})^M)`. -/
theorem Z6Vn_eq_trace_block (hN : 0 < N) (hM : 0 < M) (c : ℝ) (n : ℕ) :
    Z6Vn c N M n = Matrix.trace ((transferBlock N c n) ^ M) := by
  rw [Z6Vn_eq_sum_chain hN hM, trace_block_pow_eq_sum_chain hM]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hp : ∏ j, transferMatrix N c (x (prv j)) (x j) = 0
  · rw [hp]
    simp only [ite_self]
  · have hc := card_const_of_prod_ne_zero hM c x hp
    by_cases h0 : (x ⟨0, hM⟩).card = n
    · have : ∀ j, (x j).card = n := fun j => (hc j).trans h0
      simp [h0, this]
    · have : ¬ ∀ j, (x j).card = n := fun h => h0 (h _)
      simp [h0, this]

/-- **Trace formula for `Z^{(r)}_{6V}`.** For `0 ≤ r ≤ N/2`,
`Z^{(r)}_{6V}(N, M) = tr ((V^{[N/2-r]})^M)`. -/
theorem Z6Vr_eq_trace_block (hN : 0 < N) (hM : 0 < M) (c : ℝ) {r : ℕ} (hr : r ≤ N / 2) :
    Z6Vr c N M r = Matrix.trace ((transferBlock N c (N / 2 - r)) ^ M) := by
  rw [← Z6Vn_eq_trace_block hN hM]
  unfold Z6Vr Z6Vn
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ω
  simp only [mem_filter, mem_univ, true_and]
  omega

theorem absUp_le (hM : 0 < M) (ω : ArrowConfig N M) : ω.absUp ≤ N := by
  rw [absUp_eq_card hM]
  simpa using Finset.card_le_univ (stateRows ω.vert ⟨0, hM⟩)

/-- `Z_6V(N, M) = ∑_{n=0}^N Z_n`: the partition function is the sum of the block partition
functions (`tr (V^M) = ∑_n tr ((V^{[n]})^M)`). -/
theorem Z6V_eq_sum_Z6Vn (hM : 0 < M) (c : ℝ) :
    Z6V c N M = ∑ n ∈ range (N + 1), Z6Vn c N M n := by
  unfold Z6V Z6Vn
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range (N + 1))
    (g := fun ω : ArrowConfig N M => ω.absUp)]
  intro ω _
  simp only [mem_range]
  exact Nat.lt_succ_of_le (absUp_le hM ω)

/-- `tr (V^M) = ∑_{n=0}^N tr ((V^{[n]})^M)`. -/
theorem trace_pow_eq_sum_trace_block (hN : 0 < N) (hM : 0 < M) (c : ℝ) :
    Matrix.trace ((transferMatrix N c) ^ M) =
      ∑ n ∈ range (N + 1), Matrix.trace ((transferBlock N c n) ^ M) := by
  rw [← Z6V_eq_trace hN hM, Z6V_eq_sum_Z6Vn hM]
  exact Finset.sum_congr rfl fun n _ => Z6Vn_eq_trace_block hN hM c n

/-! ### Conservation of the number of up arrows -/

/-- The ice rule on row `j` is the flux equation between the states below and above the row. -/
theorem flux_of_iceRule {ω : ArrowConfig N M} (h : ω.IceRule) (j : Fin M) :
    Flux (stateRows ω.vert (prv j)) (stateRows ω.vert j) (fun i => ω.horiz (i, j)) := by
  intro i
  have := (inDegree_eq_two_iff _ _ _ _).1 (h (i, j))
  simpa [ArrowConfig.left, ArrowConfig.right, ArrowConfig.below, ArrowConfig.above,
    decide_mem_stateRows] using this

/-- For configurations obeying the ice rule the number of up arrows is the same on every row
(as recalled in Section 3.3.1 of arXiv:1611.09877v2), so `|ω|` is well defined. -/
theorem rowUp_eq_absUp {ω : ArrowConfig N M} (h : ω.IceRule) (j : Fin M) :
    ω.rowUp j = ω.absUp := by
  have hM : 0 < M := Fin.pos j
  rw [absUp_eq_card hM]
  have hstep : ∀ j : Fin M, (stateRows ω.vert (prv j)).card = (stateRows ω.vert j).card := by
    intro j
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      rw [Finset.eq_empty_of_isEmpty (stateRows ω.vert (prv j)),
        Finset.eq_empty_of_isEmpty (stateRows ω.vert j)]
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      exact (flux_of_iceRule h j).card_eq
  have key : ∀ j : Fin M, (stateRows ω.vert j).card = (stateRows ω.vert ⟨0, hM⟩).card := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
    intro j
    induction j using Fin.induction with
    | zero => rfl
    | succ j ih =>
      rw [← hstep (Fin.succ j), prv_succ]
      exact ih
  exact key j

end PottsDiscontinuity.SixVertex
