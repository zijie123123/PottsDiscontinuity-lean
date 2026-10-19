module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RunBoundary

/-!
# Linear shape of a canonical T₁ word after a cyclic shift

Shift the unique ML edge to the end-to-start boundary. The resulting word has
no internal ML transition, hence its L letters form an initial interval.
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.BetheAnsatz

/-- Reindex slots cyclically so that the right endpoint of the unique ML edge
is at position zero. -/
noncomputable def t1RunShift {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : Equiv.Perm (Fin (n + 1)) :=
  finCycle (t1EdgeRight i.edge)

/-- The shifted Boolean word, with its unique ML edge at the seam. -/
noncomputable def t1ShiftedWord {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) (k : Fin (n + 1)) : Bool :=
  i.w (t1RunShift i k)

theorem t1EdgeLeft_rotate {n : ℕ} (e : Option (Fin n)) :
    finRotate (n + 1) (t1EdgeLeft e) = t1EdgeRight e := by
  cases e with
  | none => exact finRotate_last
  | some a => exact finRotate_of_lt a.isLt

theorem t1RunShift_commute {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) (k : Fin (n + 1)) :
    t1RunShift i (finRotate (n + 1) k) =
      finRotate (n + 1) (t1RunShift i k) := by
  simp only [t1RunShift, finCycle_apply, finRotate_apply]
  ac_rfl

theorem t1RunShift_zero {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : t1RunShift i 0 = t1EdgeRight i.edge := by
  simp [t1RunShift, finCycle_apply]

theorem t1RunShift_last {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : t1RunShift i (Fin.last n) = t1EdgeLeft i.edge := by
  apply (finRotate (n + 1)).injective
  calc
    finRotate (n + 1) (t1RunShift i (Fin.last n)) =
        t1RunShift i (finRotate (n + 1) (Fin.last n)) :=
      (t1RunShift_commute i (Fin.last n)).symm
    _ = t1EdgeRight i.edge := by rw [finRotate_last, t1RunShift_zero]
    _ = finRotate (n + 1) (t1EdgeLeft i.edge) :=
      (t1EdgeLeft_rotate i.edge).symm

theorem t1ShiftedWord_boundary {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) :
    t1ShiftedWord i 0 = true ∧ t1ShiftedWord i (Fin.last n) = false := by
  constructor
  · change i.w (t1RunShift i 0) = true
    rw [t1RunShift_zero]
    exact i.hright
  · change i.w (t1RunShift i (Fin.last n)) = false
    rw [t1RunShift_last]
    exact i.hleft

/-- The shifted word has no ordinary ML edge. -/
theorem t1ShiftedWord_no_ordinaryML {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) (k : Fin n) :
    ¬ (t1ShiftedWord i k.castSucc = false ∧
      t1ShiftedWord i k.succ = true) := by
  rintro ⟨hfalse, htrue⟩
  have hrot := finRotate_of_lt k.isLt
  have hsucc : finRotate (n + 1) k.castSucc = k.succ := by
    simp
  have hnext : i.w (finRotate (n + 1) (t1RunShift i k.castSucc)) = true := by
    rw [← t1RunShift_commute, hsucc]
    exact htrue
  have hleft := i.hunique (t1RunShift i k.castSucc) hfalse hnext
  have hlast := t1RunShift_last i
  have heq : t1RunShift i k.castSucc = t1RunShift i (Fin.last n) :=
    hleft.trans hlast.symm
  have : k.castSucc = Fin.last n := (t1RunShift i).injective heq
  exact Fin.castSucc_ne_last k this

/-- The true/false indicator of the shifted word is antitone in the ordinary
linear order. -/
theorem t1ShiftedWord_antitone {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) :
    Antitone (fun k => if t1ShiftedWord i k then (1 : ℕ) else 0) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro k
  cases h0 : t1ShiftedWord i k.castSucc <;>
    cases h1 : t1ShiftedWord i k.succ
  · decide
  · exact False.elim (t1ShiftedWord_no_ordinaryML i k ⟨h0, h1⟩)
  · decide
  · decide

/-- The unique LM edge becomes the end of the initial true interval after the
cyclic shift. -/
theorem t1ShiftedWord_true_iff_le_end {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) (k : Fin (n + 1)) :
    t1ShiftedWord i k = true ↔ k ≤ (t1RunShift i).symm (t1PairRunEnd i) := by
  let e := (t1RunShift i).symm (t1PairRunEnd i)
  have hshift : t1RunShift i e = t1PairRunEnd i := by simp [e]
  have he : t1ShiftedWord i e = true ∧
      t1ShiftedWord i (finRotate (n + 1) e) = false := by
    constructor
    · change i.w (t1RunShift i e) = true
      rw [hshift]
      exact (t1PairRunEnd_spec i).1
    · change i.w (t1RunShift i (finRotate (n + 1) e)) = false
      rw [t1RunShift_commute]
      rw [hshift]
      exact (t1PairRunEnd_spec i).2
  have heLast : e ≠ Fin.last n := by
    intro heq
    have hboundary := (t1ShiftedWord_boundary i).2
    rw [heq] at he
    rw [he.1] at hboundary
    contradiction
  obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last heLast
  have hsuccFalse : t1ShiftedWord i j.succ = false := by
    have hrot : finRotate (n + 1) e = j.succ := by
      rw [← hj]
      exact finRotate_of_lt j.isLt
    rw [← hrot]
    exact he.2
  have hmono := t1ShiftedWord_antitone i
  constructor
  · intro hk
    by_contra hle
    have hek : e < k := lt_of_not_ge hle
    have hcast : j.castSucc < k := by rw [hj]; exact hek
    have hsuccle : j.succ ≤ k := (Fin.castSucc_lt_iff_succ_le).mp hcast
    have hleval := hmono hsuccle
    change (if t1ShiftedWord i k = true then (1 : ℕ) else 0) ≤
      (if t1ShiftedWord i j.succ = true then 1 else 0) at hleval
    simp [hsuccFalse] at hleval
    simp [hk] at hleval
  · intro hle
    have hleval := hmono hle
    change (if t1ShiftedWord i e = true then (1 : ℕ) else 0) ≤
      (if t1ShiftedWord i k = true then 1 else 0) at hleval
    simp [he.1] at hleval
    cases hk : t1ShiftedWord i k <;> simp [hk] at hleval ⊢

end PottsDiscontinuity.BetheAnsatz
