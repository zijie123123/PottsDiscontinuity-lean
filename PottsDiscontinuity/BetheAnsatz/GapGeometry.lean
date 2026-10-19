module

public import PottsDiscontinuity.BetheAnsatz.Toroidal

/-!
# Finite cyclic gap configurations

Companion paper, `cor:expressionRsi` and the domain of the sum `R_σ`.
The lower coordinates are the actual predecessor coordinates on the integer cover.
Residue distinctness is retained in the definition, including the wraparound endpoints.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- All integer choices in the closed predecessor gaps. -/
def gapTuples {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ) : Finset (Fin (n + 1) → ℤ) :=
  Fintype.piFinset (fun k => Icc (cyclicPredecessorPositions N x k) (x k))

/-- Gap choices whose positions are distinct modulo the circumference. -/
def distinctGapTuples {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ) :
    Finset (Fin (n + 1) → ℤ) :=
  (gapTuples N x).filter (fun y => Function.Injective (fun k => y k % (N : ℤ)))

/-- The extended weight in the companion paper's gap sum. -/
noncomputable def gapWeight {n : ℕ} (c : ℝ) (N : ℕ)
    (x y : Fin (n + 1) → ℤ) : ℂ :=
  ∏ k, if y k = cyclicPredecessorPositions N x k ∨ y k = x k then 1 else (c : ℂ) ^ 2

/-- The finite cyclic gap sum `R_σ`; no Bethe equation is part of its definition. -/
noncomputable def cyclicGapSum {n : ℕ} (c : ℝ) (N : ℕ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) : ℂ :=
  ∑ y ∈ distinctGapTuples N x, gapWeight c N x y * planeWave p σ y

/-- A collision of consecutive gap choices at their common endpoint, including the seam. -/
def gapCollision {n : ℕ} (N : ℕ) (x y : Fin (n + 1) → ℤ) (k : Fin (n + 1)) : Prop :=
  y k = x k ∧ y (finRotate (n + 1) k) =
    cyclicPredecessorPositions N x (finRotate (n + 1) k)

@[simp] theorem mem_gapTuples {n : ℕ} {N : ℕ} {x y : Fin (n + 1) → ℤ} :
    y ∈ gapTuples N x ↔ ∀ k, cyclicPredecessorPositions N x k ≤ y k ∧ y k ≤ x k := by
  simp only [gapTuples, Fintype.mem_piFinset, mem_Icc]

@[simp] theorem cyclicPredecessorPositions_zero {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ) :
    cyclicPredecessorPositions N x 0 = x (Fin.last n) - N := by
  have h : (finRotate (n + 1)).symm 0 = Fin.last n :=
    (Equiv.symm_apply_eq _).mpr finRotate_last.symm
  simp only [cyclicPredecessorPositions, h, ↓reduceIte]

@[simp] theorem cyclicPredecessorPositions_succ {n : ℕ} (N : ℕ)
    (x : Fin (n + 1) → ℤ) (k : Fin n) :
    cyclicPredecessorPositions N x k.succ = x k.castSucc := by
  have h : (finRotate (n + 1)).symm k.succ = k.castSucc :=
    (Equiv.symm_apply_eq _).mpr (finRotate_of_lt k.isLt).symm
  simp only [cyclicPredecessorPositions, h, Fin.succ_ne_zero, ↓reduceIte, sub_zero]

theorem positions_strictMono {N n : ℕ} (x : SixVertex.State N n) : StrictMono (positions x) := by
  intro i j hij
  have h : (x.1.orderEmbOfFin x.2 i).val < (x.1.orderEmbOfFin x.2 j).val :=
    (x.1.orderEmbOfFin x.2).strictMono hij
  unfold positions
  exact_mod_cast h

theorem positions_span_lt {N n : ℕ} (x : SixVertex.State N (n + 1)) :
    positions x (Fin.last n) - positions x 0 < (N : ℤ) := by
  have h := (x.1.orderEmbOfFin x.2 (Fin.last n)).isLt
  unfold positions
  omega

/-- Gap choices are weakly increasing, before imposing residue distinctness. -/
theorem gapTuples_monotone {N n : ℕ} {x y : Fin (n + 1) → ℤ}
    (hy : y ∈ gapTuples N x) : Monotone y := by
  apply Fin.monotone_iff_le_succ.mpr
  intro k
  have h1 := (mem_gapTuples.mp hy) k.castSucc
  have h2 := (mem_gapTuples.mp hy) k.succ
  rw [cyclicPredecessorPositions_succ] at h2
  exact h1.2.trans h2.1

/-- Every coordinate belongs to the same closed interval of length N. -/
theorem gapTuples_global_bounds {N n : ℕ} {x y : Fin (n + 1) → ℤ}
    (hx : StrictMono x) (hy : y ∈ gapTuples N x) (k : Fin (n + 1)) :
    x (Fin.last n) - N ≤ y k ∧ y k ≤ x (Fin.last n) := by
  have hm := gapTuples_monotone hy
  have h0 := (mem_gapTuples.mp hy) 0
  rw [cyclicPredecessorPositions_zero] at h0
  exact ⟨h0.1.trans (hm (Fin.zero_le k)), ((mem_gapTuples.mp hy) k).2.trans
    (hx.monotone (Fin.le_last k))⟩

/-- Two ordered coordinates in a gap tuple with the same residue differ by 0 or N. -/
theorem gapTuples_equal_residue {N n : ℕ} {x y : Fin (n + 1) → ℤ}
    (hx : StrictMono x) (hy : y ∈ gapTuples N x)
    {i j : Fin (n + 1)} (hij : i < j) (he : y i % (N : ℤ) = y j % (N : ℤ)) :
    y j = y i ∨ y j - y i = N := by
  have hb1 := gapTuples_global_bounds hx hy i
  have hb2 := gapTuples_global_bounds hx hy j
  have hm := gapTuples_monotone hy hij.le
  have hd : (N : ℤ) ∣ y j - y i := Int.modEq_iff_dvd.mp he
  by_cases h : y j - y i = N
  · exact Or.inr h
  · left
    have hlt : |y j - y i| < (N : ℤ) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hm)]
      omega
    have hz := Int.eq_zero_of_abs_lt_dvd hd hlt
    omega

/-- Equal ordered gap coordinates can only be a common endpoint of neighboring gaps. -/
theorem gapTuples_equal_coordinates {N n : ℕ} {x y : Fin (n + 1) → ℤ}
    (hx : StrictMono x) (hy : y ∈ gapTuples N x)
    {i j : Fin (n + 1)} (hij : i < j) (he : y i = y j) :
    ∃ k : Fin n, i = k.castSucc ∧ j = k.succ ∧ y i = x i ∧ y j = x i := by
  have hj : j ≠ 0 := by intro hj; subst j; exact (not_lt_of_ge (Fin.zero_le i)) hij
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj
  have hl := ((mem_gapTuples.mp hy) k.succ).1
  rw [cyclicPredecessorPositions_succ] at hl
  have hu := ((mem_gapTuples.mp hy) i).2
  have hik : i ≤ k.castSucc := by
    change i.val ≤ k.val
    have hval : i.val < k.val + 1 := hij
    omega
  have hi : i = k.castSucc := by
    by_contra hne
    have hstrict := hx (lt_of_le_of_ne hik hne)
    omega
  subst i
  refine ⟨k, rfl, rfl, ?_, ?_⟩ <;> omega

/-- A gap-coordinate difference N occurs only at the two endpoints of the period. -/
theorem gapTuples_period_difference {N n : ℕ} {x y : Fin (n + 1) → ℤ}
    (hx : StrictMono x) (hspan : x (Fin.last n) - x 0 < (N : ℤ))
    (hy : y ∈ gapTuples N x) {i j : Fin (n + 1)}
    (he : y j - y i = N) :
    i = 0 ∧ j = Fin.last n ∧ y i = x (Fin.last n) - N ∧ y j = x (Fin.last n) := by
  have hbi := gapTuples_global_bounds hx hy i
  have hbj := gapTuples_global_bounds hx hy j
  have hei : y i = x (Fin.last n) - N := by omega
  have hej : y j = x (Fin.last n) := by omega
  have hi : i = 0 := by
    by_contra hi
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hi
    have hl := ((mem_gapTuples.mp hy) k.succ).1
    rw [cyclicPredecessorPositions_succ] at hl
    have hx0 := hx.monotone (Fin.zero_le k.castSucc)
    omega
  have hj : j = Fin.last n := by
    by_contra hj
    have hstrict := hx (lt_of_le_of_ne (Fin.le_last j) hj)
    have hu := ((mem_gapTuples.mp hy) j).2
    omega
  exact ⟨hi, hj, hei, hej⟩

theorem gapCollision_equal_residue {N n : ℕ} {x y : Fin (n + 1) → ℤ}
    {k : Fin (n + 1)} (hk : gapCollision N x y k) :
    y k % (N : ℤ) = y (finRotate (n + 1) k) % (N : ℤ) := by
  rw [hk.1, hk.2]
  simp only [cyclicPredecessorPositions, Equiv.symm_apply_apply]
  split_ifs <;> simp

/-- Residue distinctness is exactly exclusion of the local endpoint collisions.
At least two gaps are present, so each successor is a different coordinate. -/
theorem distinct_residues_iff_no_gapCollision {N n : ℕ} {x y : Fin (n + 2) → ℤ}
    (hx : StrictMono x) (hspan : x (Fin.last (n + 1)) - x 0 < (N : ℤ))
    (hy : y ∈ gapTuples N x) :
    Function.Injective (fun k => y k % (N : ℤ)) ↔ ∀ k, ¬ gapCollision N x y k := by
  constructor
  · intro hinj k hk
    have he := hinj (gapCollision_equal_residue hk)
    have hs : k ∈ (finRotate (n + 2)).support := by rw [support_finRotate]; exact mem_univ k
    exact (Equiv.Perm.mem_support.mp hs) he.symm
  · intro hn
    have hord : ∀ i j : Fin (n + 2), i < j → y i % (N : ℤ) ≠ y j % (N : ℤ) := by
      intro i j hij he
      rcases gapTuples_equal_residue hx hy hij he with heq | hperiod
      · obtain ⟨k, hi, hj, hu, hl⟩ := gapTuples_equal_coordinates hx hy hij heq.symm
        apply hn i
        refine ⟨hu, ?_⟩
        rw [hi, show finRotate (n + 2) k.castSucc = k.succ from finRotate_of_lt k.isLt,
          cyclicPredecessorPositions_succ]
        simpa only [hi, hj] using hl
      · obtain ⟨hi, hj, hl, hu⟩ := gapTuples_period_difference hx hspan hy hperiod
        apply hn j
        refine ⟨?_, ?_⟩
        · simpa only [hj] using hu
        · rw [hj, finRotate_last, cyclicPredecessorPositions_zero]
          simpa only [hi] using hl
    intro i j he
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (hord i j hij he).elim
    · exact hij
    · exact (hord j i hij he.symm).elim

end PottsDiscontinuity.BetheAnsatz
