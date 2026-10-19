module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RunShape
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1ZipperRun

/-!
# A concrete zipper path for a canonical T₁ word

In the cyclicly shifted coordinates, the L slots are the initial interval
through the unique LM edge. Enumerating that interval gives a zipper path in
the original cyclic coordinates.
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.BetheAnsatz

/-- The unique LM endpoint expressed in the shifted coordinates. -/
noncomputable def t1ShiftedRunEnd {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : Fin (n + 1) :=
  (t1RunShift i).symm (t1PairRunEnd i)

/-- View an initial interval index as a slot of the full cyclic word. -/
def t1RunPathIndex {n : ℕ} (e : Fin (n + 1))
    (q : Fin (e.val + 1)) : Fin (n + 1) :=
  ⟨q.val, by omega⟩

/-- The L-run beginning at the zero-root slot, in cyclic order. -/
noncomputable def t1PairZipperPath {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : List (Fin (n + 1)) :=
  List.ofFn (fun q : Fin ((t1ShiftedRunEnd i).val + 1) =>
    t1RunShift i (t1RunPathIndex (t1ShiftedRunEnd i) q))

private theorem zipperPathAdjacent_ofFn {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1))
    (hstep : ∀ j : Fin m, f j.succ = finRotate (n + 1) (f j.castSucc)) :
    zipperPathAdjacent (List.ofFn f) := by
  induction m with
  | zero => simp [List.ofFn_succ, zipperPathAdjacent]
  | succ m ih =>
      simp only [List.ofFn_succ, zipperPathAdjacent]
      constructor
      · simpa using hstep 0
      · have htail : zipperPathAdjacent
            (List.ofFn (fun j : Fin (m + 1) => f j.succ)) := by
          apply ih
          intro j
          simpa using hstep j.succ
        simpa only [List.ofFn_succ, zipperPathAdjacent] using htail

theorem t1PairZipperPath_nodup {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : (t1PairZipperPath i).Nodup := by
  apply List.nodup_ofFn.mpr
  intro a b hab
  have h := (t1RunShift i).injective hab
  apply Fin.ext
  simpa [t1RunPathIndex] using congrArg Fin.val h

theorem t1PairZipperPath_adjacent {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : zipperPathAdjacent (t1PairZipperPath i) := by
  let e := t1ShiftedRunEnd i
  let f : Fin (e.val + 1) → Fin (n + 1) := fun j =>
    t1RunShift i (t1RunPathIndex e j)
  change zipperPathAdjacent (List.ofFn f)
  apply zipperPathAdjacent_ofFn f
  intro q
  have hidx : t1RunPathIndex e q.succ =
      finRotate (n + 1) (t1RunPathIndex e q.castSucc) := by
    have hlt : (t1RunPathIndex e q.castSucc).val < n := by
      simp [t1RunPathIndex]
      have hq := q.isLt
      have he := e.isLt
      omega
    have hstep := finRotate_of_lt hlt
    have hval : t1RunPathIndex e q.succ =
        (⟨q.val + 1, by have hq := q.isLt; have he := e.isLt; omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [t1RunPathIndex]
    calc
      t1RunPathIndex e q.succ = _ := hval
      _ = finRotate (n + 1) (t1RunPathIndex e q.castSucc) := by
        simpa [t1RunPathIndex] using hstep.symm
  change f q.succ = finRotate (n + 1) (f q.castSucc)
  change t1RunShift i (t1RunPathIndex e q.succ) =
    finRotate (n + 1) (t1RunShift i (t1RunPathIndex e q.castSucc))
  rw [hidx]
  exact t1RunShift_commute i _

theorem t1PairZipperPath_letters {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) (k : Fin (n + 1))
    (hk : k ∈ t1PairZipperPath i) : i.w k = true := by
  change k ∈ List.ofFn (fun q : Fin ((t1ShiftedRunEnd i).val + 1) =>
    t1RunShift i (t1RunPathIndex (t1ShiftedRunEnd i) q)) at hk
  rw [List.mem_ofFn'] at hk
  obtain ⟨q, rfl⟩ := hk
  have hle : t1RunPathIndex (t1ShiftedRunEnd i) q ≤ t1ShiftedRunEnd i := by
    apply Fin.le_iff_val_le_val.mpr
    simp [t1RunPathIndex]
    omega
  have htrue := (t1ShiftedWord_true_iff_le_end i
    (t1RunPathIndex (t1ShiftedRunEnd i) q)).2 hle
  simpa [t1ShiftedWord, t1ShiftedRunEnd] using htrue

theorem t1PairZipperPath_covers {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) :
    ∀ k, i.w k = true → k ∈ t1PairZipperPath i := by
  intro k hk
  let q := (t1RunShift i).symm k
  have htrue : t1ShiftedWord i q = true := by
    change i.w (t1RunShift i q) = true
    simpa [q] using hk
  have hle : q ≤ t1ShiftedRunEnd i :=
    (t1ShiftedWord_true_iff_le_end i q).1 htrue
  let q' : Fin ((t1ShiftedRunEnd i).val + 1) :=
    ⟨q.val, by have := Fin.le_iff_val_le_val.mp hle; omega⟩
  have hindex : t1RunPathIndex (t1ShiftedRunEnd i) q' = q := by
    apply Fin.ext
    rfl
  have hmap : t1RunShift i (t1RunPathIndex (t1ShiftedRunEnd i) q') = k := by
    rw [hindex]
    exact (t1RunShift i).apply_symm_apply k
  exact (List.mem_ofFn' (fun q : Fin ((t1ShiftedRunEnd i).val + 1) =>
    t1RunShift i (t1RunPathIndex (t1ShiftedRunEnd i) q)) k).2
      (Set.mem_range.mpr ⟨q', hmap⟩)

theorem t1PairZipperPath_nonempty {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : t1PairZipperPath i ≠ [] := by
  intro h
  have h0 : t1RunShift i (t1RunPathIndex (t1ShiftedRunEnd i) 0) ∈
      t1PairZipperPath i := by
    change _ ∈ List.ofFn _
    apply (List.mem_ofFn' _ _).2
    exact Set.mem_range.mpr ⟨0, rfl⟩
  rw [h] at h0
  exact List.not_mem_nil h0

theorem t1PairZipperPath_head {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) :
    (t1PairZipperPath i).headD 0 = t1EdgeRight i.edge := by
  change (List.ofFn (fun q : Fin ((t1ShiftedRunEnd i).val + 1) =>
    t1RunShift i (t1RunPathIndex (t1ShiftedRunEnd i) q))).headD 0 = _
  rw [List.ofFn_succ]
  simp [t1RunPathIndex, t1RunShift_zero]

theorem zeroRootZipperRun_root_at_last {n : ℕ}
    (path : List (Fin (n + 1))) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) {l : Fin (n + 1)}
    (hne : path ≠ []) (hroot : σ (path.headD 0) = l) :
    (zeroRootZipperRun path (σ, w)).1 (path.getLast hne) = l := by
  induction path generalizing σ w with
  | nil => contradiction
  | cons a tail ih =>
      cases tail with
      | nil =>
          have hroot' : σ a = l := by simpa using hroot
          simp [zeroRootZipperRun, hroot']
      | cons b rest =>
          have htailNe : (b :: rest) ≠ [] := by simp
          let σ' := σ * Equiv.swap a b
          let w' := Function.update w a false
          have hroot' : σ' ((b :: rest).headD 0) = l := by
            simpa [σ', Equiv.Perm.mul_apply] using hroot
          have hlast : (a :: b :: rest).getLast hne = (b :: rest).getLast htailNe := by
            simp
          change (zeroRootZipperRun (b :: rest) (σ', w')).1
            ((b :: rest).getLast htailNe) = l
          rw [← hlast]
          simpa [σ', w'] using ih σ' w' htailNe hroot'

/-- The last path slot is the unique LM endpoint in the original cyclic
coordinates. -/
noncomputable def t1PairZipperPathLast {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : Fin (n + 1) :=
  (t1PairZipperPath i).getLast (t1PairZipperPath_nonempty i)

theorem t1PairZipperPathLast_eq_runEnd {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : t1PairZipperPathLast i = t1PairRunEnd i := by
  let e := t1ShiftedRunEnd i
  have hlast := List.getLast_ofFn_succ
    (fun q : Fin (e.val + 1) => t1RunShift i (t1RunPathIndex e q))
  have hindex : t1RunPathIndex e (Fin.last e.val) = e := by
    apply Fin.ext
    rfl
  unfold t1PairZipperPathLast t1PairZipperPath
  rw [hlast, hindex]
  exact (t1RunShift i).apply_symm_apply (t1PairRunEnd i)

/-- Zipping the canonical run sends the zero root to its unique LM endpoint. -/
theorem t1PairZipperRun_root {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) :
    (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).1
      (t1PairRunEnd i) = l := by
  have hroot : i.σ ((t1PairZipperPath i).headD 0) = l := by
    rw [t1PairZipperPath_head]
    exact i.hσ
  have hlast := zeroRootZipperRun_root_at_last (t1PairZipperPath i) i.σ i.w
    (t1PairZipperPath_nonempty i) hroot
  rw [← t1PairZipperPathLast_eq_runEnd i]
  exact hlast

/-- The zipper run preserves the regularized zero-root term. -/
theorem t1PairZipperRun_preserves {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) (i : T1PairIndex n l) :
    zeroRootRegularizedWordTerm (N := N) c x p l
      (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).1
      (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).2 =
    zeroRootRegularizedWordTerm (N := N) c x p l i.σ i.w := by
  have hroot : i.σ ((t1PairZipperPath i).headD 0) = l := by
    rw [t1PairZipperPath_head]
    exact i.hσ
  exact zeroRootZipperRun_preserves hc x p hp hinj l hpl hBE
    (t1PairZipperPath i) i.σ i.w (t1PairZipperPath_nodup i)
    (fun k hk => t1PairZipperPath_letters i k hk)
    (t1PairZipperPath_adjacent i) (t1PairZipperPath_nonempty i) hroot

/-- Every letter is M after the full T₁ zipper run. -/
theorem t1PairZipperRun_word_eq_false {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) :
    ∀ k, (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).2 k = false := by
  exact zeroRootZipperRun_word_eq_false (t1PairZipperPath i) i.σ i.w
    (t1PairZipperPath_covers i)

end PottsDiscontinuity.BetheAnsatz
