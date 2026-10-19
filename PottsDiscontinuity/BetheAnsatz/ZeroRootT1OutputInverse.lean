module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1OutputIndex

/-!
# Reconstructing a canonical T₁ pair from its output index

For an output permutation and a choice of ML-left slot, the original word is
the cyclic interval from the right endpoint through the output zero slot.
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.BetheAnsatz

/-- The cyclic shift whose coordinate zero is the right endpoint of an edge. -/
def t1OutputShift {n : ℕ} (edge : Option (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  finCycle (t1EdgeRight edge)

theorem t1OutputShift_commute {n : ℕ} (edge : Option (Fin n))
    (k : Fin (n + 1)) :
    t1OutputShift edge (finRotate (n + 1) k) =
      finRotate (n + 1) (t1OutputShift edge k) := by
  simp only [t1OutputShift, finCycle_apply, finRotate_apply]
  ac_rfl

theorem t1OutputShift_zero {n : ℕ} (edge : Option (Fin n)) :
    t1OutputShift edge 0 = t1EdgeRight edge := by
  simp [t1OutputShift, finCycle_apply]

theorem t1OutputShift_last {n : ℕ} (edge : Option (Fin n)) :
    t1OutputShift edge (Fin.last n) = t1EdgeLeft edge := by
  apply (finRotate (n + 1)).injective
  calc
    finRotate (n + 1) (t1OutputShift edge (Fin.last n)) =
        t1OutputShift edge (finRotate (n + 1) (Fin.last n)) :=
      (t1OutputShift_commute edge (Fin.last n)).symm
    _ = t1EdgeRight edge := by rw [finRotate_last, t1OutputShift_zero]
    _ = finRotate (n + 1) (t1EdgeLeft edge) :=
      (t1EdgeLeft_rotate edge).symm

/-- The shifted coordinate of a slot. -/
def t1OutputCoordinate {n : ℕ} (edge : Option (Fin n)) (k : Fin (n + 1)) :
    Fin (n + 1) := (t1OutputShift edge).symm k

theorem t1OutputCoordinate_rotate {n : ℕ} (edge : Option (Fin n))
    (k : Fin (n + 1)) :
    t1OutputCoordinate edge (finRotate (n + 1) k) =
      finRotate (n + 1) (t1OutputCoordinate edge k) := by
  have h := congrArg (t1OutputShift edge).symm
    (t1OutputShift_commute edge (t1OutputCoordinate edge k))
  simpa [t1OutputCoordinate] using h.symm

/-- The word of the pair represented by an output index. -/
def t1OutputWord {n : ℕ} {l : Fin (n + 1)} (o : T1OutputIndex n l)
    (k : Fin (n + 1)) : Bool :=
  decide (t1OutputCoordinate o.edge k ≤ t1OutputCoordinate o.edge (o.σ.symm l))

/-- Enumerate the cyclic interval of true letters from the edge's right slot to
the output zero slot. -/
def t1OutputPath {n : ℕ} {l : Fin (n + 1)} (o : T1OutputIndex n l) :
    List (Fin (n + 1)) :=
  let e := t1OutputCoordinate o.edge (o.σ.symm l)
  List.ofFn (fun q : Fin (e.val + 1) =>
    t1OutputShift o.edge (t1RunPathIndex e q))

theorem t1OutputEndCoordinate_ne_last {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) :
    t1OutputCoordinate o.edge (o.σ.symm l) ≠ Fin.last n := by
  intro he
  have hshift := (t1OutputShift o.edge).apply_symm_apply (o.σ.symm l)
  change (t1OutputShift o.edge).symm (o.σ.symm l) = Fin.last n at he
  rw [he, t1OutputShift_last] at hshift
  exact o.hleft hshift

theorem t1OutputWord_right {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) : t1OutputWord o (t1EdgeRight o.edge) = true := by
  simp only [t1OutputWord, t1OutputCoordinate]
  rw [← t1OutputShift_zero o.edge]
  simp

theorem t1OutputWord_left {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) : t1OutputWord o (t1EdgeLeft o.edge) = false := by
  have he := t1OutputEndCoordinate_ne_last o
  have hlt : t1OutputCoordinate o.edge (o.σ.symm l) < Fin.last n :=
    Fin.lt_last_iff_ne_last.mpr he
  have hleft : t1OutputCoordinate o.edge (t1EdgeLeft o.edge) = Fin.last n := by
    unfold t1OutputCoordinate
    rw [← t1OutputShift_last o.edge]
    simp
  simpa [t1OutputWord, hleft] using he

theorem t1OutputWord_end {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) : t1OutputWord o (o.σ.symm l) = true := by
  simp [t1OutputWord]

theorem t1OutputWord_end_rotate {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) :
    t1OutputWord o (finRotate (n + 1) (o.σ.symm l)) = false := by
  let e := t1OutputCoordinate o.edge (o.σ.symm l)
  have he : e ≠ Fin.last n := t1OutputEndCoordinate_ne_last o
  obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last he
  have hrot : finRotate (n + 1) e = j.succ := by
    rw [← hj]
    exact finRotate_of_lt j.isLt
  have hcoord :
      t1OutputCoordinate o.edge (finRotate (n + 1) (o.σ.symm l)) = j.succ := by
    calc
      _ = finRotate (n + 1) e := by
        rw [t1OutputCoordinate_rotate]
      _ = j.succ := hrot
  have hnot : ¬ j.succ ≤ e := by
    have hlt : e < j.succ := by
      rw [← hj]
      exact Fin.castSucc_lt_succ
    exact not_le_of_gt hlt
  change decide (t1OutputCoordinate o.edge (finRotate (n + 1) (o.σ.symm l)) ≤ e) = false
  rw [hcoord]
  simp [hnot]

theorem t1OutputWord_uniqueML {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) (k : Fin (n + 1))
    (hfalse : t1OutputWord o k = false)
    (htrue : t1OutputWord o (finRotate (n + 1) k) = true) :
    k = t1EdgeLeft o.edge := by
  let q := t1OutputCoordinate o.edge k
  let e := t1OutputCoordinate o.edge (o.σ.symm l)
  have hqnot : ¬ q ≤ e := by
    exact of_decide_eq_false (by simpa [t1OutputWord, q, e] using hfalse)
  have hnext : t1OutputCoordinate o.edge (finRotate (n + 1) k) ≤ e := by
    exact of_decide_eq_true (by simpa [t1OutputWord, q, e] using htrue)
  have hcoord : t1OutputCoordinate o.edge (finRotate (n + 1) k) =
      finRotate (n + 1) q := by
    exact t1OutputCoordinate_rotate o.edge k
  by_cases hlast : q = Fin.last n
  · calc
      k = t1OutputShift o.edge q :=
        (t1OutputShift o.edge).apply_symm_apply k |>.symm
      _ = t1OutputShift o.edge (Fin.last n) := congrArg _ hlast
      _ = t1EdgeLeft o.edge := t1OutputShift_last o.edge
  · obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hlast
    have hrot : finRotate (n + 1) q = j.succ := by
      rw [← hj]
      exact finRotate_of_lt j.isLt
    have hstrict : e < q := lt_of_not_ge hqnot
    rw [hcoord, hrot] at hnext
    have hqsucc : q < j.succ := by
      rw [← hj]
      exact Fin.castSucc_lt_succ
    exact False.elim ((not_le_of_gt (hstrict.trans hqsucc)) hnext)

theorem t1OutputPath_nonempty {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) : t1OutputPath o ≠ [] := by
  intro h
  let e := t1OutputCoordinate o.edge (o.σ.symm l)
  have hmem : t1OutputShift o.edge (t1RunPathIndex e 0) ∈ t1OutputPath o := by
    unfold t1OutputPath
    rw [List.mem_ofFn']
    exact Set.mem_range.mpr ⟨0, rfl⟩
  rw [h] at hmem
  exact List.not_mem_nil hmem

theorem t1OutputPath_head {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) :
    (t1OutputPath o).headD 0 = t1EdgeRight o.edge := by
  let e := t1OutputCoordinate o.edge (o.σ.symm l)
  unfold t1OutputPath
  rw [List.ofFn_succ]
  simp [t1RunPathIndex, t1OutputShift_zero]

theorem t1OutputPath_last {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) :
    (t1OutputPath o).getLast (t1OutputPath_nonempty o) = o.σ.symm l := by
  let e := t1OutputCoordinate o.edge (o.σ.symm l)
  have hlast := List.getLast_ofFn_succ
    (fun q : Fin (e.val + 1) => t1OutputShift o.edge (t1RunPathIndex e q))
  have hindex : t1RunPathIndex e (Fin.last e.val) = e := by
    apply Fin.ext
    rfl
  unfold t1OutputPath
  rw [hlast, hindex]
  exact (t1OutputShift o.edge).apply_symm_apply (o.σ.symm l)

/-- The input permutation recovered by undoing all swaps of the output path. -/
noncomputable def t1OutputInputPerm {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) : Equiv.Perm (Fin (n + 1)) :=
  o.σ * (zeroRootZipperPerm (t1OutputPath o))⁻¹

/-- Reconstruct the canonical input word, permutation, and unique ML edge. -/
noncomputable def t1OutputInput {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) : T1PairIndex n l where
  σ := t1OutputInputPerm o
  w := t1OutputWord o
  edge := o.edge
  hσ := by
    let path := t1OutputPath o
    let ρ := zeroRootZipperPerm path
    have hρend : ρ (o.σ.symm l) = t1EdgeRight o.edge := by
      have h := zeroRootZipperPerm_getLast_eq_headD path (t1OutputPath_nonempty o)
      rw [t1OutputPath_last] at h
      rw [t1OutputPath_head] at h
      exact h
    have hρsymm : ρ.symm (t1EdgeRight o.edge) = o.σ.symm l := by
      apply ρ.injective
      calc
        ρ (ρ.symm (t1EdgeRight o.edge)) = t1EdgeRight o.edge := ρ.apply_symm_apply _
        _ = ρ (o.σ.symm l) := hρend.symm
    change (o.σ * ρ⁻¹) (t1EdgeRight o.edge) = l
    calc
      _ = o.σ (ρ.symm (t1EdgeRight o.edge)) := by simp [Equiv.Perm.mul_apply]
      _ = o.σ (o.σ.symm l) := by rw [hρsymm]
      _ = l := o.σ.apply_symm_apply l
  hleft := t1OutputWord_left o
  hright := t1OutputWord_right o
  hunique := t1OutputWord_uniqueML o

theorem t1OutputInput_runEnd {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) : t1PairRunEnd (t1OutputInput o) = o.σ.symm l := by
  let i := t1OutputInput o
  have hEnd : i.w (o.σ.symm l) = true ∧
      i.w (finRotate (n + 1) (o.σ.symm l)) = false := by
    exact ⟨t1OutputWord_end o, t1OutputWord_end_rotate o⟩
  have huniq := (Classical.choose_spec (t1PairIndex_existsUnique_LM i)).2
  have h := huniq (o.σ.symm l) hEnd
  exact h.symm

theorem t1OutputPath_eq_inputPath {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) :
    t1OutputPath o = t1PairZipperPath (t1OutputInput o) := by
  unfold t1OutputPath t1PairZipperPath t1ShiftedRunEnd t1RunShift
    t1OutputCoordinate t1OutputShift
  rw [t1OutputInput_runEnd]
  rfl

theorem t1OutputInput_outputPerm {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) :
    (zeroRootZipperRun (t1PairZipperPath (t1OutputInput o))
      ((t1OutputInput o).σ, (t1OutputInput o).w)).1 = o.σ := by
  rw [zeroRootZipperRun_perm]
  rw [← t1OutputPath_eq_inputPath]
  simp only [t1OutputInput, t1OutputInputPerm]
  group

end PottsDiscontinuity.BetheAnsatz
