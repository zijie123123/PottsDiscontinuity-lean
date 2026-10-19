module

public import PottsDiscontinuity.BetheAnsatz.GapGeometric
public import PottsDiscontinuity.BetheAnsatz.GapInclusionExclusion

/-!
# Restricted cyclic gap sums

The constraints on a collision set separate coordinate by coordinate. Unlike the
printed `eq:ArbitrarySetCalc`, the formula below includes adjacent collisions:
the corresponding local factor is zero, since every gap has positive length.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Collision constraints expressed at each individual coordinate. -/
theorem gapCollision_constraints_iff {N n : ℕ} (x y : Fin (n + 1) → ℤ)
    (S : Finset (Fin (n + 1))) :
    (∀ k ∈ S, gapCollision N x y k) ↔
      ∀ k, (k ∈ S → y k = x k) ∧
        ((finRotate (n + 1)).symm k ∈ S → y k = cyclicPredecessorPositions N x k) := by
  constructor
  · intro h k
    refine ⟨fun hk => (h k hk).1, ?_⟩
    intro hk
    simpa only [gapCollision, Equiv.apply_symm_apply] using (h _ hk).2
  · intro h k hk
    exact ⟨(h k).1 hk, (h _).2 (by simpa only [Equiv.symm_apply_apply] using hk)⟩

/-- Product domain for a collision set, including the empty domain when constraints conflict. -/
theorem restricted_gapTuples_eq_pi {N n : ℕ} (x : Fin (n + 1) → ℤ)
    (S : Finset (Fin (n + 1))) :
    (gapTuples N x).filter (fun y => ∀ k ∈ S, gapCollision N x y k) =
      Fintype.piFinset (fun k => (Icc (cyclicPredecessorPositions N x k) (x k)).filter
        (fun u => (k ∈ S → u = x k) ∧
          ((finRotate (n + 1)).symm k ∈ S → u = cyclicPredecessorPositions N x k))) := by
  ext y
  simp only [mem_filter, mem_gapTuples, gapCollision_constraints_iff,
    Fintype.mem_piFinset, mem_Icc]
  constructor
  · rintro ⟨hg, hc⟩ k
    exact ⟨hg k, hc k⟩
  · intro h
    exact ⟨fun k => (h k).1, fun k => (h k).2⟩

/-- Evaluate one gap with either, both, or neither endpoint forced. -/
theorem sum_constrained_gap_geometric (c p : ℝ) {a b : ℤ} (hab : a < b)
    (hp : z p ≠ 1) (A B : Prop) :
    (∑ u ∈ (Icc a b).filter (fun u => (A → u = b) ∧ (B → u = a)),
      (if u = a ∨ u = b then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase p u) =
      if A then (if B then 0 else positionPhase p b)
      else (if B then positionPhase p a
        else L c (z p) * positionPhase p a + M c (z p) * positionPhase p b) := by
  by_cases hA : A <;> by_cases hB : B
  · have he : (Icc a b).filter (fun u => (A → u = b) ∧ (B → u = a)) = ∅ := by
      ext u
      constructor
      · intro hu
        have hu' := (mem_filter.mp hu).2
        have h1 := hu'.1 hA
        have h2 := hu'.2 hB
        omega
      · intro hu
        exact False.elim (Finset.notMem_empty u hu)
    rw [he]
    simp only [Finset.sum_empty, hA, hB, ↓reduceIte]
  · have he : (Icc a b).filter (fun u => (A → u = b) ∧ (B → u = a)) = {b} := by
      ext u
      simp only [mem_filter, mem_Icc, hA, hB, true_implies, false_implies,
        and_true, mem_singleton]
      omega
    rw [he]
    simp only [sum_singleton, hA, hB, ↓reduceIte, or_true, one_mul]
  · have he : (Icc a b).filter (fun u => (A → u = b) ∧ (B → u = a)) = {a} := by
      ext u
      simp only [mem_filter, mem_Icc, hA, hB, true_implies, false_implies,
        true_and, mem_singleton]
      omega
    rw [he]
    simp only [sum_singleton, hA, hB, ↓reduceIte, true_or, one_mul]
  · simpa only [hA, hB, false_implies, and_self, filter_true, ↓reduceIte] using
      sum_gap_geometric c p hab hp

/-- Strictly positive lengths of the predecessor gaps. -/
theorem cyclicPredecessorPositions_lt {N n : ℕ} {x : Fin (n + 1) → ℤ}
    (hx : StrictMono x) (hspan : x (Fin.last n) - x 0 < (N : ℤ)) (k : Fin (n + 1)) :
    cyclicPredecessorPositions N x k < x k := by
  induction k using Fin.cases with
  | zero => rw [cyclicPredecessorPositions_zero]; omega
  | succ k =>
    rw [cyclicPredecessorPositions_succ]
    exact hx (by change k.val < k.val + 1; omega)

/-- Equation `eq:ArbitrarySetCalc`, extended to every collision set by zero factors. -/
theorem restrictedGapSum_eq_product {N n : ℕ} (c : ℝ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (hx : StrictMono x)
    (hspan : x (Fin.last n) - x 0 < (N : ℤ)) (hp : ∀ j, z (p j) ≠ 1) :
    restrictedGapSum (N := N) c x p σ S =
      ∏ k, if k ∈ S then
        (if (finRotate (n + 1)).symm k ∈ S then 0 else positionPhase (p (σ k)) (x k))
      else (if (finRotate (n + 1)).symm k ∈ S then
        positionPhase (p (σ k)) (cyclicPredecessorPositions N x k)
      else L c (z (p (σ k))) * positionPhase (p (σ k)) (cyclicPredecessorPositions N x k) +
        M c (z (p (σ k))) * positionPhase (p (σ k)) (x k)) := by
  unfold restrictedGapSum
  rw [restricted_gapTuples_eq_pi]
  unfold gapWeight planeWave
  simp_rw [← Finset.prod_mul_distrib]
  change (∑ y ∈ Fintype.piFinset _, ∏ k,
    (if y k = cyclicPredecessorPositions N x k ∨ y k = x k then (1 : ℂ) else (c : ℂ) ^ 2) *
      positionPhase (p (σ k)) (y k)) = _
  rw [← Finset.prod_univ_sum
    (fun k => (Icc (cyclicPredecessorPositions N x k) (x k)).filter
      (fun u => (k ∈ S → u = x k) ∧
        ((finRotate (n + 1)).symm k ∈ S → u = cyclicPredecessorPositions N x k)))
    (fun k (u : ℤ) => (if u = cyclicPredecessorPositions N x k ∨ u = x k
      then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase (p (σ k)) u)]
  apply Finset.prod_congr rfl
  intro k _
  have hlocal := sum_constrained_gap_geometric c (p (σ k))
    (cyclicPredecessorPositions_lt hx hspan k) (hp (σ k))
    (k ∈ S) ((finRotate (n + 1)).symm k ∈ S)
  by_cases hk : k ∈ S <;> by_cases hl : (finRotate (n + 1)).symm k ∈ S <;>
    simpa only [hk, hl, true_implies, false_implies, true_and, and_true, ↓reduceIte] using hlocal

end PottsDiscontinuity.BetheAnsatz
