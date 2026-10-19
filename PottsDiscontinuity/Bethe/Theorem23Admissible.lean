module

public import PottsDiscontinuity.Bethe.AsymptoticPartition
public import PottsDiscontinuity.Bethe.Theorem23Coordinates

/-! # Compact regions of separated symmetric configurations -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- A symmetric configuration with strictly positive cyclic gaps lies in S_n.
This includes the physical endpoint inequalities, not just absence of root
collisions. -/
theorem mem_S_n_of_positive_cyclic_gaps {k : ℕ} (p : Fin (k + 1) → ℝ)
    (hsym : p ∈ R_n_sym (k + 1))
    (hgaps : ∀ j : Fin (k + 2), 0 < rootPartitionPoint (k + 1) p (by omega) j.succ -
      rootPartitionPoint (k + 1) p (by omega) j.castSucc) : p ∈ S_n (k + 1) := by
  have hmono : StrictMono p := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    let cell : Fin (k + 2) := ⟨j.val + 1, by omega⟩
    have ha : rootPartitionPoint (k + 1) p (by omega) cell.castSucc = p j.castSucc := by
      convert rootPartitionPoint_root p (by omega) j.castSucc using 1
      congr 1
    have hb : rootPartitionPoint (k + 1) p (by omega) cell.succ = p j.succ := by
      convert rootPartitionPoint_root p (by omega) j.succ using 1
      congr 1
    have h := hgaps cell
    rw [ha, hb] at h
    exact sub_pos.mp h
  have hfirst := hgaps 0
  have ha : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).castSucc =
      p (Fin.last k) - 2 * Real.pi := by
    convert rootPartitionPoint_zero p (by omega) using 1 <;> congr 1
  have hb : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).succ = p 0 := by
    convert rootPartitionPoint_root p (by omega) (0 : Fin (k + 1)) using 1
    congr 1
  rw [ha, hb] at hfirst
  have hsym0 : p (Fin.last k) = -p 0 := by simpa using hsym 0
  have hlo : -Real.pi < p 0 := by linarith
  have hhi : p (Fin.last k) < Real.pi := by linarith
  refine ⟨fun j => ⟨?_, ?_⟩, hmono, hsym⟩
  · exact hlo.trans_le (hmono.monotone (Fin.zero_le j))
  · exact (hmono.monotone (Fin.le_last j)).trans_lt hhi

/-- The admissible coordinates have every cyclic gap between two fixed bounds.
Both bounds are literal finite inequalities in the roots. -/
def betheGapRegion (k : ℕ) (ell u : ℝ) : Set (Fin ((k + 1) / 2) → ℝ) :=
  {q | ∀ j : Fin (k + 2), rootPartitionPoint (k + 1) (discreteSymLift (k + 1) q)
      (by omega) j.succ - rootPartitionPoint (k + 1) (discreteSymLift (k + 1) q)
      (by omega) j.castSucc ∈ Icc ell u}

theorem continuous_rootPartitionPoint (k : ℕ) (j : Fin (k + 3)) :
    Continuous (fun p : Fin (k + 1) → ℝ => rootPartitionPoint (k + 1) p (by omega) j) := by
  unfold rootPartitionPoint
  split_ifs <;> fun_prop

theorem isClosed_betheGapRegion (k : ℕ) (ell u : ℝ) :
    IsClosed (betheGapRegion k ell u) := by
  simp only [betheGapRegion, ofPred_forall]
  apply isClosed_iInter
  intro j
  have hc (i : Fin (k + 3)) : Continuous (fun q : Fin ((k + 1) / 2) → ℝ =>
      rootPartitionPoint (k + 1) (discreteSymLift (k + 1) q) (by omega) i) :=
    (continuous_rootPartitionPoint k i).comp (discreteSymLift (k + 1)).continuous_of_finiteDimensional
  exact isClosed_Icc.preimage ((hc j.succ).sub (hc j.castSucc))

theorem betheGapRegion_mem_S_n {k : ℕ} {ell u : ℝ} (hell : 0 < ell)
    {q : Fin ((k + 1) / 2) → ℝ} (hq : q ∈ betheGapRegion k ell u) :
    discreteSymLift (k + 1) q ∈ S_n (k + 1) :=
  mem_S_n_of_positive_cyclic_gaps _ (discreteSymLift_mem _ _)
    (fun j => hell.trans_le (hq j).1)

/-- Positive lower gaps make the closed gap region compact. -/
theorem isCompact_betheGapRegion (k : ℕ) {ell u : ℝ} (hell : 0 < ell) :
    IsCompact (betheGapRegion k ell u) := by
  have hbox : IsCompact (Set.pi Set.univ (fun _ : Fin ((k + 1) / 2) => Icc (-Real.pi) Real.pi)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_betheGapRegion k ell u)
  intro q hq j _
  have hp := betheGapRegion_mem_S_n hell hq
  have hj := hp.1 (discreteHalfIndex (k + 1) j)
  simpa only [Set.mem_Icc, discreteSymLift_half] using And.intro hj.1.le hj.2.le

end PottsDiscontinuity.Bethe
