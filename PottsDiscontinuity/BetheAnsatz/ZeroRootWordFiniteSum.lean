module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordCancellationSum

/-!
# Reindexing the fixed-amplitude word sum into root-slot fibers

Every permutation occurs in exactly one fiber, determined by the slot carrying
the distinguished label. This is the finite-sum interface used to separate
root-incident T₁ words from terms canceled away from that slot.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- All permutations grouped by the slot which carries the label `l`. -/
abbrev RootSlotFiberIndex (n : ℕ) (l : Fin (n + 1)) :=
  {q : Fin (n + 1) × Equiv.Perm (Fin (n + 1)) // q.2 q.1 = l}

/-- The root-slot fibers partition the permutation group. -/
noncomputable def rootSlotFiberEquiv {n : ℕ} (l : Fin (n + 1)) :
    RootSlotFiberIndex n l ≃ Equiv.Perm (Fin (n + 1)) where
  toFun q := q.1.2
  invFun σ := ⟨(σ.symm l, σ), σ.apply_symm_apply l⟩
  left_inv := by
    intro q
    apply Subtype.ext
    apply Prod.ext
    · apply q.1.2.injective
      calc
        q.1.2 (q.1.2.symm l) = l := q.1.2.apply_symm_apply l
        _ = q.1.2 q.1.1 := q.2.symm
    · rfl
  right_inv := by
    intro σ
    rfl

/-- If a chosen ML edge is disjoint from the root slot, its entire constrained
fixed-amplitude word sum vanishes. -/
theorem sum_rootSlotFiber_fixedAmplitudeWordTerm_eq_zero_of_ML_away
    {N n : ℕ} {c : ℝ} (hc : 2 < c) (hn : 0 < n)
    (p q : Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℤ)
    (l r a : Fin (n + 1)) (w : Fin (n + 1) → Bool)
    (hBE : BetheEquations N (anisotropy c) p)
    (hAgree : ∀ k, k ≠ l → q k = p k)
    (hNotOne : ∀ k, k ≠ l → z (p k) ≠ 1)
    (ha : w a = false) (hb : w (finRotate (n + 1) a) = true)
    (hra : r ≠ a) (hrb : r ≠ finRotate (n + 1) a) :
    (∑ σ : RootSlotPerm l r,
      fixedAmplitudeWordTerm (N := N) c x p q σ.1 w) = 0 :=
  sum_fixedAmplitudeWordTerm_eq_zero_of_ML_away hc hn p q x l r a w
    hBE hAgree hNotOne ha hb hra hrb

end PottsDiscontinuity.BetheAnsatz
