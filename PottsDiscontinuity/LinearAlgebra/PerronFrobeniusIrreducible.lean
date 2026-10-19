module

public import Mathlib
public import PottsDiscontinuity.LinearAlgebra.SymmetricSpectral

/-!
# Perron-Frobenius for symmetric nonnegative matrices: the irreducible case

Let `A : Matrix ι ι ℝ` be symmetric (`Matrix.IsHermitian`) with nonnegative entries over a finite
nonempty index type, and write `ρ = pfRoot A` for its largest eigenvalue.  The only Perron-Frobenius
inputs are the spectral theorem for symmetric matrices (via `SymmetricSpectral`), the Rayleigh bound
`x ⬝ᵥ A x ≤ ρ * (x ⬝ᵥ x)`, and the inequality `|x ⬝ᵥ A x| ≤ |x| ⬝ᵥ A |x|` for `A ≥ 0`.

* `abs_le_pfRoot_of_mem_spectrum` (no irreducibility needed): `|μ| ≤ ρ` for every `μ ∈ spectrum`.
* `abs_mulVec_eq`: if `A v = μ v` with `|μ| ≥ ρ` then `|v|` is an eigenvector for `ρ`.
* Under irreducibility (`∀ i j, ∃ k > 0, 0 < (A ^ k) i j`): `ρ > 0`, a strictly positive
  eigenvector exists, the `ρ`-eigenspace is a line, and `ρ` is a simple root of the characteristic
  polynomial (`rootMultiplicity_charpoly_pfRoot`).  The eigenvalue `-ρ`, if present, is also simple.
* Under primitivity: `|μ| < ρ` for all other eigenvalues (`abs_lt_pfRoot_of_primitive`).
-/

@[expose] public section

open Matrix

namespace PottsDiscontinuity.PerronFrobenius

variable {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ}

theorem dotProduct_self_nonneg' (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem abs_dotProduct_self (v : ι → ℝ) : (fun i => |v i|) ⬝ᵥ (fun i => |v i|) = v ⬝ᵥ v :=
  Finset.sum_congr rfl fun i _ => abs_mul_abs_self (v i)

/-- For a nonnegative matrix, `|vᵀ A v| ≤ |v|ᵀ A |v|`. -/
theorem abs_dotProduct_mulVec_le (hnn : ∀ i j, 0 ≤ A i j) (v : ι → ℝ) :
    |v ⬝ᵥ (A *ᵥ v)| ≤ (fun i => |v i|) ⬝ᵥ (A *ᵥ fun i => |v i|) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (hnn i j)]

variable [DecidableEq ι] [Nonempty ι]

/-- If `A v = μ v` with `|μ| ≥ ρ` (`ρ` the largest eigenvalue) then `|v|` is an eigenvector of `A`
for `ρ`. -/
theorem abs_mulVec_eq (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j) {μ : ℝ} {v : ι → ℝ}
    (hv : A *ᵥ v = μ • v) (hμ : pfRoot A ≤ |μ|) :
    A *ᵥ (fun i => |v i|) = pfRoot A • (fun i => |v i|) := by
  apply mulVec_eq_pfRoot_smul_of_dotProduct_mulVec_eq hA
  have hvv := dotProduct_self_nonneg' v
  have h1 : |v ⬝ᵥ (A *ᵥ v)| = |μ| * (v ⬝ᵥ v) := by
    rw [hv, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_nonneg hvv]
  have h2 := abs_dotProduct_mulVec_le hnn v
  have h3 := dotProduct_mulVec_le_pfRoot hA (fun i => |v i|)
  rw [abs_dotProduct_self] at h3 ⊢
  apply le_antisymm h3
  calc pfRoot A * (v ⬝ᵥ v) ≤ |μ| * (v ⬝ᵥ v) := mul_le_mul_of_nonneg_right hμ hvv
    _ = |v ⬝ᵥ (A *ᵥ v)| := h1.symm
    _ ≤ _ := h2

/-- All eigenvalues of a symmetric nonnegative matrix are bounded in absolute value by the
largest one. -/
theorem abs_eigenvalues_le_pfRoot (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j) (i : ι) :
    |hA.eigenvalues i| ≤ pfRoot A := by
  have hb := mulVec_eigvec hA i
  have hbb : eigvec hA i ⬝ᵥ eigvec hA i = 1 := by simpa using eigvec_dot hA i i
  have h1 : |eigvec hA i ⬝ᵥ (A *ᵥ eigvec hA i)| = |hA.eigenvalues i| := by
    rw [hb, dotProduct_smul, smul_eq_mul, hbb, mul_one]
  have h2 := abs_dotProduct_mulVec_le hnn (eigvec hA i)
  have h3 := dotProduct_mulVec_le_pfRoot hA (fun j => |eigvec hA i j|)
  rw [abs_dotProduct_self, hbb] at h3
  rw [h1] at h2
  linarith

theorem abs_le_pfRoot_of_mem_spectrum (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ A) : |μ| ≤ pfRoot A := by
  rw [hA.spectrum_real_eq_range_eigenvalues] at hμ
  obtain ⟨i, rfl⟩ := hμ
  exact abs_eigenvalues_le_pfRoot hA hnn i

theorem pfRoot_nonneg (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j) : 0 ≤ pfRoot A :=
  (abs_nonneg _).trans (abs_le_pfRoot_of_mem_spectrum hA hnn (isGreatest_pfRoot hA).1)

/-- A nonnegative symmetric matrix with a positive entry has positive largest eigenvalue. -/
theorem pfRoot_pos (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j) (hne : ∃ i j, 0 < A i j) :
    0 < pfRoot A := by
  obtain ⟨i, j, hij⟩ := hne
  have h := dotProduct_mulVec_le_pfRoot hA (fun _ : ι => (1 : ℝ))
  have hs : 0 < (fun _ : ι => (1 : ℝ)) ⬝ᵥ (A *ᵥ fun _ : ι => (1 : ℝ)) := by
    simp only [dotProduct, mulVec, one_mul, mul_one]
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)
      ⟨i, Finset.mem_univ i, Finset.sum_pos' (fun j _ => hnn i j) ⟨j, Finset.mem_univ j, hij⟩⟩
  have hcard : (0 : ℝ) < (fun _ : ι => (1 : ℝ)) ⬝ᵥ (fun _ : ι => (1 : ℝ)) := by
    simp [dotProduct, Fintype.card_pos]
  by_contra hρ
  push Not at hρ
  nlinarith

omit [Nonempty ι] in
theorem pow_mulVec_eq_of_mulVec_eq {c : ℝ} {w : ι → ℝ} (h : A *ᵥ w = c • w) (M : ℕ) :
    (A ^ M) *ᵥ w = c ^ M • w := by
  induction M with
  | zero => simp
  | succ M ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, h, smul_smul, ← pow_succ]

omit [Nonempty ι] in
theorem rootMultiplicity_charpoly_eq_card (hA : A.IsHermitian) (a : ℝ) :
    A.charpoly.rootMultiplicity a =
      (Finset.univ.filter fun i => hA.eigenvalues i = a).card := by
  rw [← Polynomial.count_roots, hA.roots_charpoly_eq_eigenvalues]
  simp only [Function.comp_def, Multiset.count_map, RCLike.ofReal_real_eq_id, id_eq]
  rw [Finset.card_def, Finset.filter_val]
  simp only [eq_comm]

/-! ### Irreducible matrices -/

section Irreducible

variable (hnn : ∀ i j, 0 ≤ A i j) (hirr : ∀ i j, ∃ k > 0, 0 < (A ^ k) i j)

include hnn hirr in
theorem exists_pos_entry_of_irreducible : ∃ i j, 0 < A i j := by
  by_contra h
  push Not at h
  obtain ⟨k, hk, hpos⟩ := hirr (Classical.arbitrary ι) (Classical.arbitrary ι)
  have hA0 : A = 0 := by
    ext i j
    exact le_antisymm (h i j) (hnn i j)
  rw [hA0, zero_pow hk.ne'] at hpos
  simp at hpos

omit [Nonempty ι] in
include hnn hirr in
/-- A nonnegative eigenvector (for a positive eigenvalue) of an irreducible matrix is strictly
positive. -/
theorem pos_of_nonneg_eigenvector {ρ : ℝ} (hρ : 0 < ρ) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hwne : w ≠ 0) (hw : A *ᵥ w = ρ • w) : ∀ i, 0 < w i := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hwne (funext hcon)
  have hjpos : 0 < w j := lt_of_le_of_ne (hw0 j) (Ne.symm hj)
  intro i
  obtain ⟨k, hk, hkpos⟩ := hirr i j
  have h1 := congrFun (pow_mulVec_eq_of_mulVec_eq hw k) i
  have h2 : (A ^ k) i j * w j ≤ ((A ^ k) *ᵥ w) i := by
    simp only [mulVec, dotProduct]
    exact Finset.single_le_sum (f := fun l => (A ^ k) i l * w l)
      (fun l _ => mul_nonneg (pow_apply_nonneg hnn k i l) (hw0 l)) (Finset.mem_univ j)
  have h3 : 0 < ρ ^ k * w i := by
    have : 0 < (A ^ k) i j * w j := mul_pos hkpos hjpos
    have h4 := lt_of_lt_of_le this h2
    rw [h1] at h4
    simpa using h4
  by_contra hcon
  push Not at hcon
  nlinarith [pow_pos hρ k]

variable (hA : A.IsHermitian)

include hA hnn hirr in
theorem pfRoot_pos_of_irreducible : 0 < pfRoot A :=
  pfRoot_pos hA hnn (exists_pos_entry_of_irreducible hnn hirr)

include hA hnn hirr in
/-- An irreducible symmetric nonnegative matrix has a strictly positive eigenvector for `pfRoot A`. -/
theorem exists_pos_eigenvector :
    ∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ A *ᵥ v = pfRoot A • v := by
  have hρ := pfRoot_pos_of_irreducible hnn hirr hA
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_pfRoot hA
  have hb : A *ᵥ eigvec hA i = pfRoot A • eigvec hA i := by rw [mulVec_eigvec, hi]
  have habs := abs_mulVec_eq hA hnn hb (by rw [abs_of_pos hρ])
  have hbb : eigvec hA i ⬝ᵥ eigvec hA i = 1 := by simpa using eigvec_dot hA i i
  refine ⟨fun j => |eigvec hA i j|, ?_, habs⟩
  refine pos_of_nonneg_eigenvector hnn hirr hρ (fun j => abs_nonneg _) ?_ habs
  intro h0
  have h1 : eigvec hA i ⬝ᵥ eigvec hA i = 0 := by
    have : ∀ j, eigvec hA i j = 0 := fun j => abs_eq_zero.1 (congrFun h0 j)
    simp [dotProduct, this]
  rw [hbb] at h1
  exact one_ne_zero h1

include hA hnn hirr in
/-- The `pfRoot A`-eigenspace of an irreducible symmetric nonnegative matrix is a line. -/
theorem eigenspace_pfRoot_eq {u : ι → ℝ} (hu : ∀ i, 0 < u i) (hu' : A *ᵥ u = pfRoot A • u)
    {w : ι → ℝ} (hw : A *ᵥ w = pfRoot A • w) : ∃ c : ℝ, w = c • u := by
  have hρ := pfRoot_pos_of_irreducible hnn hirr hA
  let i0 : ι := Classical.arbitrary ι
  let t : ℝ := w i0 / u i0
  have hz : A *ᵥ (w - t • u) = pfRoot A • (w - t • u) := by
    rw [mulVec_sub, mulVec_smul, hw, hu', smul_sub, smul_comm]
  have hzi : (w - t • u) i0 = 0 := by
    simp [t, (hu i0).ne']
  refine ⟨t, ?_⟩
  by_contra hne
  have hz0 : w - t • u ≠ 0 := fun h => hne (sub_eq_zero.1 h)
  have habs := abs_mulVec_eq hA hnn hz (by rw [abs_of_pos hρ])
  have hne' : (fun j => |(w - t • u) j|) ≠ 0 := by
    intro h
    apply hz0
    funext j
    exact abs_eq_zero.1 (congrFun h j)
  have := pos_of_nonneg_eigenvector hnn hirr hρ (fun j => abs_nonneg _) hne' habs i0
  simp [hzi] at this

include hA hnn hirr in
/-- Exactly one eigenvalue of `hA.eigenvalues` (counted by index) equals `pfRoot A`. -/
theorem existsUnique_eigenvalues_eq_pfRoot : ∃! i, hA.eigenvalues i = pfRoot A := by
  obtain ⟨u, hu, hu'⟩ := exists_pos_eigenvector hnn hirr hA
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_pfRoot hA
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hne
  have hbi : A *ᵥ eigvec hA i = pfRoot A • eigvec hA i := by rw [mulVec_eigvec, hi]
  have hbj : A *ᵥ eigvec hA j = pfRoot A • eigvec hA j := by rw [mulVec_eigvec, hj]
  obtain ⟨c, hc⟩ := eigenspace_pfRoot_eq hnn hirr hA hu hu' hbi
  obtain ⟨d, hd⟩ := eigenspace_pfRoot_eq hnn hirr hA hu hu' hbj
  have horth : eigvec hA i ⬝ᵥ eigvec hA j = 0 := by simpa [Ne.symm hne] using eigvec_dot hA i j
  have hii : eigvec hA i ⬝ᵥ eigvec hA i = 1 := by simpa using eigvec_dot hA i i
  have hjj : eigvec hA j ⬝ᵥ eigvec hA j = 1 := by simpa using eigvec_dot hA j j
  have huu : 0 < u ⬝ᵥ u := Finset.sum_pos (fun k _ => mul_pos (hu k) (hu k)) Finset.univ_nonempty
  rw [hc, hd, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at horth
  rw [hc, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hii
  rw [hd, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hjj
  have hcd : c * d = 0 := by
    have : c * (d * (u ⬝ᵥ u)) = 0 := by linarith [horth]
    rcases mul_eq_zero.1 this with h | h
    · exact mul_eq_zero.2 (Or.inl h)
    · rcases mul_eq_zero.1 h with h | h
      · exact mul_eq_zero.2 (Or.inr h)
      · exact absurd h huu.ne'
  rcases mul_eq_zero.1 hcd with h | h
  · rw [h] at hii; simp at hii
  · rw [h] at hjj; simp at hjj

include hA hnn hirr in
/-- The characteristic polynomial has `pfRoot A` as a simple root. -/
theorem rootMultiplicity_charpoly_pfRoot :
    A.charpoly.rootMultiplicity (pfRoot A) = 1 := by
  rw [rootMultiplicity_charpoly_eq_card hA, Finset.card_eq_one]
  obtain ⟨i, hi, huniq⟩ := existsUnique_eigenvalues_eq_pfRoot hnn hirr hA
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hj => huniq j hj, fun hj => hj ▸ hi⟩

include hA hnn hirr in
/-- The eigenspace of `-pfRoot A` (if nonzero) is a line. -/
theorem eigenspace_neg_pfRoot_eq {w' : ι → ℝ} (hw' : A *ᵥ w' = (-pfRoot A) • w') (hne : w' ≠ 0)
    {w : ι → ℝ} (hw : A *ᵥ w = (-pfRoot A) • w) : ∃ c : ℝ, w = c • w' := by
  have hρ := pfRoot_pos_of_irreducible hnn hirr hA
  have hμ : pfRoot A ≤ |-pfRoot A| := by rw [abs_neg, abs_of_pos hρ]
  let i0 : ι := Classical.arbitrary ι
  have habs' := abs_mulVec_eq hA hnn hw' hμ
  have hne' : (fun j => |w' j|) ≠ 0 := by
    intro h
    apply hne
    funext j
    exact abs_eq_zero.1 (congrFun h j)
  have hpos := pos_of_nonneg_eigenvector hnn hirr hρ (fun j => abs_nonneg _) hne' habs' i0
  have hw'i : w' i0 ≠ 0 := fun h => by simp [h] at hpos
  let t : ℝ := w i0 / w' i0
  have hz : A *ᵥ (w - t • w') = (-pfRoot A) • (w - t • w') := by
    rw [mulVec_sub, mulVec_smul, hw, hw', smul_sub, smul_comm]
  have hzi : (w - t • w') i0 = 0 := by
    simp [t, hw'i]
  refine ⟨t, ?_⟩
  by_contra hne2
  have hz0 : w - t • w' ≠ 0 := fun h => hne2 (sub_eq_zero.1 h)
  have habs := abs_mulVec_eq hA hnn hz hμ
  have hne'' : (fun j => |(w - t • w') j|) ≠ 0 := by
    intro h
    apply hz0
    funext j
    exact abs_eq_zero.1 (congrFun h j)
  have := pos_of_nonneg_eigenvector hnn hirr hρ (fun j => abs_nonneg _) hne'' habs i0
  simp [hzi] at this

include hA hnn hirr in
/-- At most one eigenvalue index equals `-pfRoot A`. -/
theorem eigenvalues_eq_neg_pfRoot_subsingleton {i j : ι} (hi : hA.eigenvalues i = -pfRoot A)
    (hj : hA.eigenvalues j = -pfRoot A) : i = j := by
  by_contra hne
  have hbi : A *ᵥ eigvec hA i = (-pfRoot A) • eigvec hA i := by rw [mulVec_eigvec, hi]
  have hbj : A *ᵥ eigvec hA j = (-pfRoot A) • eigvec hA j := by rw [mulVec_eigvec, hj]
  have hii : eigvec hA i ⬝ᵥ eigvec hA i = 1 := by simpa using eigvec_dot hA i i
  have hjj : eigvec hA j ⬝ᵥ eigvec hA j = 1 := by simpa using eigvec_dot hA j j
  have horth : eigvec hA i ⬝ᵥ eigvec hA j = 0 := by simpa [hne] using eigvec_dot hA i j
  have hj0 : eigvec hA j ≠ 0 := by
    intro h
    rw [h] at hjj
    simp at hjj
  obtain ⟨c, hc⟩ := eigenspace_neg_pfRoot_eq hnn hirr hA hbj hj0 hbi
  rw [hc, smul_dotProduct, smul_eq_mul, hjj, mul_one] at horth
  rw [hc, horth] at hii
  simp at hii

include hA hnn hirr in
/-- The characteristic polynomial has `-pfRoot A` as a root of multiplicity at most one. -/
theorem rootMultiplicity_charpoly_neg_pfRoot_le_one :
    A.charpoly.rootMultiplicity (-pfRoot A) ≤ 1 := by
  rw [rootMultiplicity_charpoly_eq_card hA, Finset.card_le_one]
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact eigenvalues_eq_neg_pfRoot_subsingleton hnn hirr hA hi hj

end Irreducible

/-! ### Primitive matrices -/

section Primitive

omit [DecidableEq ι] [Nonempty ι] in
/-- Strict triangle inequality for positive weights and a sign-changing vector. -/
theorem abs_sum_lt_sum_abs_of_mixed {c v : ι → ℝ} (hc : ∀ j, 0 < c j) {a b : ι} (ha : 0 < v a)
    (hb : v b < 0) : |∑ j, c j * v j| < ∑ j, c j * |v j| := by
  rw [abs_lt]
  constructor
  · have h : 0 < ∑ j, (c j * |v j| + c j * v j) := by
      refine Finset.sum_pos' (fun j _ => ?_) ⟨a, Finset.mem_univ a, ?_⟩
      · have := neg_abs_le (v j)
        have := hc j
        nlinarith
      · rw [abs_of_pos ha]; have := hc a; nlinarith
    rw [Finset.sum_add_distrib] at h
    linarith
  · have h : 0 < ∑ j, (c j * |v j| - c j * v j) := by
      refine Finset.sum_pos' (fun j _ => ?_) ⟨b, Finset.mem_univ b, ?_⟩
      · have := le_abs_self (v j)
        have := hc j
        nlinarith
      · rw [abs_of_neg hb]; have := hc b; nlinarith
    rw [Finset.sum_sub_distrib] at h
    linarith

omit [DecidableEq ι] [Nonempty ι] in
theorem eq_zero_of_mulVec_eq_pos_neg {ρ : ℝ} (hρ : 0 < ρ) {v : ι → ℝ} (h1 : A *ᵥ v = ρ • v)
    (h2 : A *ᵥ v = (-ρ) • v) : v = 0 := by
  funext j
  have a := congrFun h1 j
  have b := congrFun h2 j
  simp only [Pi.smul_apply, smul_eq_mul] at a b
  have : ρ * v j = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hρ.ne'
  · simpa using h

variable (hnn : ∀ i j, 0 ≤ A i j) {k : ℕ} (hk0 : 0 < k) (hk : ∀ i j, 0 < (A ^ k) i j)
  (hA : A.IsHermitian)

include hA hnn hk0 hk in
/-- For a primitive symmetric nonnegative matrix, `-pfRoot A` is not an eigenvalue. -/
theorem neg_pfRoot_not_mem_spectrum_of_primitive : -pfRoot A ∉ spectrum ℝ A := by
  intro hmem
  have hirr : ∀ i j, ∃ k > 0, 0 < (A ^ k) i j := fun i j => ⟨k, hk0, hk i j⟩
  have hρ := pfRoot_pos_of_irreducible hnn hirr hA
  rw [hA.spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨i, hi⟩ := hmem
  have hv : A *ᵥ eigvec hA i = (-pfRoot A) • eigvec hA i := by rw [mulVec_eigvec, hi]
  have hvv : eigvec hA i ⬝ᵥ eigvec hA i = 1 := by simpa using eigvec_dot hA i i
  have hμ : pfRoot A ≤ |-pfRoot A| := by rw [abs_neg, abs_of_pos hρ]
  have habs := abs_mulVec_eq hA hnn hv hμ
  have hno : ¬ (∃ a b, 0 < eigvec hA i a ∧ eigvec hA i b < 0) := by
    rintro ⟨a, b, ha, hb⟩
    let i0 : ι := Classical.arbitrary ι
    have h1 := congrFun (pow_mulVec_eq_of_mulVec_eq hv k) i0
    have h2 := congrFun (pow_mulVec_eq_of_mulVec_eq habs k) i0
    have hlt := abs_sum_lt_sum_abs_of_mixed (c := fun j => (A ^ k) i0 j) (v := eigvec hA i)
      (fun j => hk i0 j) ha hb
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [h1, h2, abs_mul, abs_pow, abs_neg, abs_of_pos hρ] at hlt
    exact lt_irrefl _ hlt
  have hsign : (∀ j, 0 ≤ eigvec hA i j) ∨ (∀ j, eigvec hA i j ≤ 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨b, hb⟩, ⟨a, ha⟩⟩ := hcon
    exact hno ⟨a, b, ha, hb⟩
  have hzero : eigvec hA i = 0 := by
    rcases hsign with h | h
    · have e : (fun j => |eigvec hA i j|) = eigvec hA i := funext fun j => abs_of_nonneg (h j)
      rw [e] at habs
      exact eq_zero_of_mulVec_eq_pos_neg hρ habs hv
    · have e : (fun j => |eigvec hA i j|) = -eigvec hA i :=
        funext fun j => abs_of_nonpos (h j)
      rw [e, mulVec_neg, smul_neg, neg_inj] at habs
      exact eq_zero_of_mulVec_eq_pos_neg hρ habs hv
  rw [hzero] at hvv
  simp at hvv

include hA hnn hk0 hk in
/-- Strict spectral gap for primitive symmetric nonnegative matrices: every eigenvalue other than
`pfRoot A` has absolute value `< pfRoot A`. -/
theorem abs_lt_pfRoot_of_primitive {μ : ℝ} (hμ : μ ∈ spectrum ℝ A) (hne : μ ≠ pfRoot A) :
    |μ| < pfRoot A := by
  have hirr : ∀ i j, ∃ k > 0, 0 < (A ^ k) i j := fun i j => ⟨k, hk0, hk i j⟩
  have hρ := pfRoot_pos_of_irreducible hnn hirr hA
  refine lt_of_le_of_ne (abs_le_pfRoot_of_mem_spectrum hA hnn hμ) fun habs => ?_
  rcases (abs_eq hρ.le).1 habs with h | h
  · exact hne h
  · exact neg_pfRoot_not_mem_spectrum_of_primitive hnn hk0 hk hA (h ▸ hμ)

end Primitive

end PottsDiscontinuity.PerronFrobenius
