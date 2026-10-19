module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1FinitePairs

/-!
# The unique LM edge of a T₁ word

A cyclic binary word has equally many ML and LM edges. Thus the unique ML edge
in a `T1PairIndex` determines one unique LM edge, which is the end of its L-run.
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.BetheAnsatz

/-- Cyclic edges whose letters are `ML` (false, then true). -/
def t1MLBoundarySet {n : ℕ} (w : Fin (n + 1) → Bool) :
    Finset (Fin (n + 1)) :=
  univ.filter (fun k => w k = false ∧ w (finRotate (n + 1) k) = true)

/-- Cyclic edges whose letters are `LM` (true, then false). -/
def t1LMBoundarySet {n : ℕ} (w : Fin (n + 1) → Bool) :
    Finset (Fin (n + 1)) :=
  univ.filter (fun k => w k = true ∧ w (finRotate (n + 1) k) = false)

/-- Around a cyclic word, the number of transitions from M to L equals the
number of transitions from L to M. -/
theorem t1TransitionCounts_eq {n : ℕ} (w : Fin (n + 1) → Bool) :
    (t1MLBoundarySet w).card = (t1LMBoundarySet w).card := by
  let b (k : Fin (n + 1)) : ℤ := if w k then 1 else 0
  have hcycle : (∑ k, b (finRotate (n + 1) k)) = ∑ k, b k :=
    Equiv.sum_comp (finRotate (n + 1)) b
  have hzero : (∑ k, (b (finRotate (n + 1) k) - b k)) = 0 := by
    rw [Finset.sum_sub_distrib, hcycle]
    simp
  have hpoint (k : Fin (n + 1)) :
      b (finRotate (n + 1) k) - b k =
        (if w k = false ∧ w (finRotate (n + 1) k) = true then (1 : ℤ) else 0) -
        (if w k = true ∧ w (finRotate (n + 1) k) = false then (1 : ℤ) else 0) := by
    rw [finRotate_apply]
    cases hw : w k <;> cases hn : w (k + 1) <;> simp [b, hw, hn]
  have hsum : (∑ k, (b (finRotate (n + 1) k) - b k)) =
      ((t1MLBoundarySet w).card : ℤ) - (t1LMBoundarySet w).card := by
    calc
      _ = ∑ k, ((if w k = false ∧ w (finRotate (n + 1) k) = true
            then (1 : ℤ) else 0) -
          (if w k = true ∧ w (finRotate (n + 1) k) = false
            then (1 : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        exact hpoint k
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp [t1MLBoundarySet, t1LMBoundarySet, Finset.sum_boole]
  have hcardCast : ((t1MLBoundarySet w).card : ℤ) = (t1LMBoundarySet w).card := by
    have := hsum.symm.trans hzero
    exact sub_eq_zero.mp this
  exact_mod_cast hcardCast

/-- A canonical T₁ word has a unique LM edge. -/
theorem t1PairIndex_existsUnique_LM {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) :
    ∃! e, i.w e = true ∧ i.w (finRotate (n + 1) e) = false := by
  have hrot : finRotate (n + 1) (t1EdgeLeft i.edge) = t1EdgeRight i.edge := by
    cases i.edge with
    | none => exact finRotate_last
    | some a => exact finRotate_of_lt a.isLt
  have hML : t1MLBoundarySet i.w = {t1EdgeLeft i.edge} := by
    ext k
    simp only [t1MLBoundarySet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hk₀, hk₁⟩
      exact i.hunique k hk₀ hk₁
    · intro hk
      subst k
      exact ⟨i.hleft, hrot ▸ i.hright⟩
  have hMLcard : (t1MLBoundarySet i.w).card = 1 := by rw [hML]; simp
  have hLMcard : (t1LMBoundarySet i.w).card = 1 := by
    rw [← t1TransitionCounts_eq i.w, hMLcard]
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hLMcard
  refine ⟨e, ?_, ?_⟩
  · have hemem : e ∈ t1LMBoundarySet i.w := by rw [he]; simp
    exact (Finset.mem_filter.mp hemem).2
  · intro j hj
    have hjmem : j ∈ t1LMBoundarySet i.w :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    rw [he] at hjmem
    simpa using hjmem

/-- The end of the unique L-run, selected from its unique LM edge. -/
noncomputable def t1PairRunEnd {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : Fin (n + 1) :=
  Classical.choose (t1PairIndex_existsUnique_LM i)

/-- The selected run endpoint is the unique LM edge. -/
theorem t1PairRunEnd_spec {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) :
    i.w (t1PairRunEnd i) = true ∧
      i.w (finRotate (n + 1) (t1PairRunEnd i)) = false :=
  (Classical.choose_spec (t1PairIndex_existsUnique_LM i)).1

end PottsDiscontinuity.BetheAnsatz
