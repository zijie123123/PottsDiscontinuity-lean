module

public import Mathlib
public import PottsDiscontinuity.LinearAlgebra.PerronFrobeniusGrowth

/-!
# Perron-Frobenius theorems for real symmetric nonnegative matrices

Public statements, for a finite nonempty index type `ι` and a real symmetric matrix
`A : Matrix ι ι ℝ` (`hA : A.IsHermitian`, equivalent to `Aᵀ = A` by `Matrix.isHermitian_iff_isSymm`)
with `A.IsIrreducible` / `A.IsPrimitive` in the sense of Mathlib
(`Mathlib/LinearAlgebra/Matrix/Irreducible/Defs.lean`; both include nonnegativity of the entries).
Here `pfRoot A = sSup (spectrum ℝ A)` is the largest eigenvalue.

* `perronFrobenius_irreducible`: `pfRoot A > 0`, it is the maximum of the spectrum and of
  `|spectrum|`, it has a strictly positive eigenvector, its eigenspace is a line
  (`finrank = 1`), and it is a simple root of the characteristic polynomial.
  The eigenvalue `-pfRoot A` has algebraic multiplicity at most one (the periodic case); this is
  the statement used for possibly periodic irreducible blocks.
* `perronFrobenius_primitive`: in addition every eigenvalue `μ ≠ pfRoot A` satisfies
  `|μ| < pfRoot A`.
* `tendsto_log_trace_pow`, `tendsto_log_dotProduct_pow_mulVec`, `tendsto_log_sum_entries_pow`:
  `(1/M) log tr (A ^ M) → log (pfRoot A)` and the analogues for the pairing with nonzero
  nonnegative vectors / the sum of all entries.
-/

@[expose] public section

open Matrix Filter Topology

namespace PottsDiscontinuity.PerronFrobenius

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℝ}

omit [Nonempty ι] in
/-- Entries of an irreducible matrix are nonnegative and some power of it connects any two indices
(Mathlib's `Matrix.isIrreducible_iff_exists_pow_pos`). -/
theorem nonneg_and_exists_pow_pos_of_isIrreducible (hirr : A.IsIrreducible) :
    (∀ i j, 0 ≤ A i j) ∧ ∀ i j, ∃ k > 0, 0 < (A ^ k) i j :=
  ⟨hirr.nonneg, (Matrix.isIrreducible_iff_exists_pow_pos hirr.nonneg).1 hirr⟩

theorem finrank_eigenspace_pfRoot_eq_one (hA : A.IsHermitian) (hirr : A.IsIrreducible) :
    Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' A) (pfRoot A)) = 1 := by
  obtain ⟨hnn, hirr'⟩ := nonneg_and_exists_pow_pos_of_isIrreducible hirr
  obtain ⟨v, hv, hv'⟩ := exists_pos_eigenvector hnn hirr' hA
  have hmem : v ∈ Module.End.eigenspace (Matrix.toLin' A) (pfRoot A) := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hv'
  have hne : (⟨v, hmem⟩ : Module.End.eigenspace (Matrix.toLin' A) (pfRoot A)) ≠ 0 := by
    intro h
    have := congrArg (fun z : Module.End.eigenspace (Matrix.toLin' A) (pfRoot A) => (z : ι → ℝ)) h
    have h0 : v (Classical.arbitrary ι) = 0 := congrFun this (Classical.arbitrary ι)
    exact (hv _).ne' h0
  rw [finrank_eq_one_iff_of_nonzero' _ hne]
  intro w
  have hw : A *ᵥ (w : ι → ℝ) = pfRoot A • (w : ι → ℝ) := by
    have := w.2
    rwa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this
  obtain ⟨c, hc⟩ := eigenspace_pfRoot_eq hnn hirr' hA hv hv' hw
  exact ⟨c, Subtype.ext hc.symm⟩

/-- **Perron-Frobenius for irreducible symmetric nonnegative matrices** (periodic case allowed).

The largest eigenvalue `ρ = pfRoot A` is positive, is the maximum of the spectrum and also the
maximum of the absolute values of the eigenvalues, has a strictly positive eigenvector, its
eigenspace is a line, it is a simple root of the characteristic polynomial and the eigenvalue
`-ρ` has algebraic multiplicity at most one. -/
theorem perronFrobenius_irreducible (hA : A.IsHermitian) (hirr : A.IsIrreducible) :
    0 < pfRoot A ∧
    IsGreatest (spectrum ℝ A) (pfRoot A) ∧
    IsGreatest ((fun μ : ℝ => |μ|) '' spectrum ℝ A) (pfRoot A) ∧
    (∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ A *ᵥ v = pfRoot A • v) ∧
    (∀ v w : ι → ℝ, (∀ i, 0 < v i) → A *ᵥ v = pfRoot A • v → A *ᵥ w = pfRoot A • w →
      ∃ c : ℝ, w = c • v) ∧
    Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' A) (pfRoot A)) = 1 ∧
    A.charpoly.rootMultiplicity (pfRoot A) = 1 ∧
    (∃! i, hA.eigenvalues i = pfRoot A) ∧
    A.charpoly.rootMultiplicity (-pfRoot A) ≤ 1 := by
  obtain ⟨hnn, hirr'⟩ := nonneg_and_exists_pow_pos_of_isIrreducible hirr
  have hmem := (isGreatest_pfRoot hA).1
  refine ⟨pfRoot_pos_of_irreducible hnn hirr' hA, isGreatest_pfRoot hA, ?_,
    exists_pos_eigenvector hnn hirr' hA, ?_, finrank_eigenspace_pfRoot_eq_one hA hirr,
    rootMultiplicity_charpoly_pfRoot hnn hirr' hA, existsUnique_eigenvalues_eq_pfRoot hnn hirr' hA,
    rootMultiplicity_charpoly_neg_pfRoot_le_one hnn hirr' hA⟩
  · refine ⟨⟨pfRoot A, hmem, abs_of_nonneg (pfRoot_nonneg hA hnn)⟩, ?_⟩
    rintro _ ⟨μ, hμ, rfl⟩
    exact abs_le_pfRoot_of_mem_spectrum hA hnn hμ
  · intro v w hv hv' hw
    exact eigenspace_pfRoot_eq hnn hirr' hA hv hv' hw

/-- **Perron-Frobenius for primitive symmetric nonnegative matrices**: besides the conclusions of
`perronFrobenius_irreducible`, every eigenvalue other than `pfRoot A` has strictly smaller absolute
value (`-pfRoot A` is not an eigenvalue). -/
theorem perronFrobenius_primitive (hA : A.IsHermitian) (hprim : A.IsPrimitive) :
    (0 < pfRoot A ∧
      IsGreatest (spectrum ℝ A) (pfRoot A) ∧
      (∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ A *ᵥ v = pfRoot A • v) ∧
      Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' A) (pfRoot A)) = 1 ∧
      A.charpoly.rootMultiplicity (pfRoot A) = 1) ∧
    (∀ μ ∈ spectrum ℝ A, μ ≠ pfRoot A → |μ| < pfRoot A) ∧
    (∀ i, hA.eigenvalues i = pfRoot A ∨ |hA.eigenvalues i| < pfRoot A) := by
  have hirr := hprim.isIrreducible
  obtain ⟨h1, h2, -, h4, -, h6, h7, -, -⟩ := perronFrobenius_irreducible hA hirr
  obtain ⟨k, hk0, hk⟩ := hprim.exists_pos_pow
  have hgap : ∀ μ ∈ spectrum ℝ A, μ ≠ pfRoot A → |μ| < pfRoot A :=
    fun μ hμ hne => abs_lt_pfRoot_of_primitive hprim.nonneg hk0 hk hA hμ hne
  refine ⟨⟨h1, h2, h4, h6, h7⟩, hgap, fun i => ?_⟩
  by_cases h : hA.eigenvalues i = pfRoot A
  · exact Or.inl h
  · exact Or.inr (hgap _ (hA.eigenvalues_mem_spectrum_real i) h)

/-- `(1/M) log tr (A ^ M) → log (pfRoot A)` for a primitive symmetric nonnegative matrix. -/
theorem tendsto_log_trace_pow (hA : A.IsHermitian) (hprim : A.IsPrimitive) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Matrix.trace (A ^ M))) atTop
      (𝓝 (Real.log (pfRoot A))) :=
  tendsto_log_trace_pow_primitive hA hprim

/-- `(1/M) log (x ⬝ᵥ Aᴹ y) → log (pfRoot A)` for nonzero nonnegative vectors `x`, `y` and a
primitive symmetric nonnegative matrix `A`. -/
theorem tendsto_log_dotProduct_pow_mulVec (hA : A.IsHermitian) (hprim : A.IsPrimitive)
    {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hx0 : x ≠ 0) (hy : ∀ i, 0 ≤ y i) (hy0 : y ≠ 0) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (x ⬝ᵥ ((A ^ M) *ᵥ y))) atTop
      (𝓝 (Real.log (pfRoot A))) :=
  tendsto_log_dotProduct_pow_mulVec_primitive hA hprim hx hx0 hy hy0

/-- `(1/M) log (∑ i j, (Aᴹ) i j) → log (pfRoot A)` for a primitive symmetric nonnegative
matrix `A`. -/
theorem tendsto_log_sum_entries_pow (hA : A.IsHermitian) (hprim : A.IsPrimitive) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (∑ i, ∑ j, (A ^ M) i j)) atTop
      (𝓝 (Real.log (pfRoot A))) :=
  tendsto_log_sum_entries_pow_primitive hA hprim

end PottsDiscontinuity.PerronFrobenius
