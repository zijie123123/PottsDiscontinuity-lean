module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RunPath

/-!
# Permutation carried by a zero-root zipper run

The successive adjacent swaps in the zipper run form one explicit permutation.
It moves the root from the first path slot to the last and fixes slots outside
the path.
-/

@[expose] public section

namespace PottsDiscontinuity.BetheAnsatz

/-- The permutation accumulated by the adjacent swaps along a zipper path. -/
def zeroRootZipperPerm {n : ℕ} : List (Fin (n + 1)) → Equiv.Perm (Fin (n + 1))
  | [] => 1
  | [_] => 1
  | a :: b :: rest => Equiv.swap a b * zeroRootZipperPerm (b :: rest)

theorem zeroRootZipperRun_perm {n : ℕ}
    (path : List (Fin (n + 1))) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) :
    (zeroRootZipperRun path (σ, w)).1 = σ * zeroRootZipperPerm path := by
  induction path generalizing σ w with
  | nil => simp [zeroRootZipperPerm, zeroRootZipperRun]
  | cons a tail ih =>
      cases tail with
      | nil => simp [zeroRootZipperPerm, zeroRootZipperRun]
      | cons b rest =>
          simp only [zeroRootZipperRun]
          rw [ih]
          simp only [zeroRootZipperPerm]
          group

theorem zeroRootZipperPerm_apply_of_not_mem {n : ℕ}
    (path : List (Fin (n + 1))) (k : Fin (n + 1))
    (hk : k ∉ path) : zeroRootZipperPerm path k = k := by
  induction path with
  | nil => simp [zeroRootZipperPerm]
  | cons a tail ih =>
      cases tail with
      | nil => simp [zeroRootZipperPerm]
      | cons b rest =>
          have hka : k ≠ a := by
            intro heq
            exact hk (List.mem_cons.mpr (Or.inl heq))
          have hkb : k ≠ b := by
            intro heq
            exact hk (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl heq))))
          have htail : k ∉ b :: rest := by
            intro hmem
            exact hk (List.mem_cons.mpr (Or.inr hmem))
          rw [zeroRootZipperPerm, Equiv.Perm.mul_apply, ih htail]
          exact Equiv.swap_apply_of_ne_of_ne hka hkb

theorem zeroRootZipperPerm_getLast_eq_headD {n : ℕ}
    (path : List (Fin (n + 1))) (hne : path ≠ []) :
    zeroRootZipperPerm path (path.getLast hne) = path.headD 0 := by
  have hroot : (1 : Equiv.Perm (Fin (n + 1))) (path.headD 0) = path.headD 0 := rfl
  have h := zeroRootZipperRun_root_at_last (l := path.headD 0)
    path 1 (fun _ => false) hne hroot
  rw [zeroRootZipperRun_perm] at h
  simpa [zeroRootZipperPerm] using h

theorem t1PairZipperPath_left_not_mem {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : t1EdgeLeft i.edge ∉ t1PairZipperPath i := by
  intro hmem
  have htrue := t1PairZipperPath_letters i (t1EdgeLeft i.edge) hmem
  rw [i.hleft] at htrue
  contradiction

/-- The run changes only the labels on its path. In particular, the original
ML left endpoint keeps its momentum label. -/
theorem t1PairZipperRun_left {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) :
    (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).1
      (t1EdgeLeft i.edge) = i.σ (t1EdgeLeft i.edge) := by
  rw [zeroRootZipperRun_perm]
  rw [Equiv.Perm.mul_apply,
    zeroRootZipperPerm_apply_of_not_mem _ _ (t1PairZipperPath_left_not_mem i)]

end PottsDiscontinuity.BetheAnsatz
