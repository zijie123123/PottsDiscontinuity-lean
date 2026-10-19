module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordGoodFiberSum

/-!
# The fixed-amplitude zero-root word-sum bridge

The word expansion at a punctured perturbation is split into its constant,
root-incident, and canceling fibers. This file first proves that finite identity;
the next step is to pass to its T₀/T₁ limit and identify the transfer action.
-/

@[expose] public section

open Finset Complex Classical Filter Topology

namespace PottsDiscontinuity.BetheAnsatz

/-- Reindex the fixed-amplitude sum over permutations and words by the slot occupied
by the distinguished label, retaining the word coordinate. -/
theorem sum_fixedAmplitudeWordTerm_eq_rootSlotWordFiberTerm {N m : ℕ} {c : ℝ}
    (x : Fin (m + 1) → ℤ) (p q : Fin (m + 1) → ℝ) (l : Fin (m + 1)) :
    (∑ σ : Equiv.Perm (Fin (m + 1)),
      ∑ w : Fin (m + 1) → Bool,
        fixedAmplitudeWordTerm (N := N) c x p q σ w) =
      ∑ i : RootSlotWordFiberIndex m l,
        rootSlotWordFiberTerm (N := N) c x p q i := by
  classical
  let F : Equiv.Perm (Fin (m + 1)) × (Fin (m + 1) → Bool) → ℂ := fun a =>
    fixedAmplitudeWordTerm (N := N) c x p q a.1 a.2
  calc
    _ = ∑ a : Equiv.Perm (Fin (m + 1)) × (Fin (m + 1) → Bool), F a := by
      rw [Fintype.sum_prod_type]
    _ = ∑ i : RootSlotWordFiberIndex m l,
        F (rootSlotWordFiberEquiv l i) :=
      (Equiv.sum_comp (rootSlotWordFiberEquiv l) F).symm
    _ = ∑ i : RootSlotWordFiberIndex m l,
        rootSlotWordFiberTerm (N := N) c x p q i := by
      apply Finset.sum_congr rfl
      intro i hi
      rfl

/-- At a perturbation of one zero root, the complete word sum is precisely the
constant T₀ expression plus the canonical paired T₁ terms. -/
theorem fixedAmplitudeWordSum_eq_constant_plus_t1 {N m : ℕ} {c : ℝ}
    (hc : 2 < c) (hm : 0 < m) (x : Fin (m + 1) → ℤ)
    (p : Fin (m + 1) → ℝ) (hp : ∀ k, p k ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (m + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) (t : ℝ) :
    (∑ σ : Equiv.Perm (Fin (m + 1)),
      ∑ w : Fin (m + 1) → Bool,
        fixedAmplitudeWordTerm (N := N) c x p (perturbedMomenta p l t) σ w) =
      constantWordSumPerturbed (N := N) c x p l t +
        ∑ i : T1PairIndex m l, t1PairTerm (N := N) c x p l t i := by
  classical
  let q := perturbedMomenta p l t
  have hAgree : ∀ k, k ≠ l → q k = p k := by
    intro k hkl
    exact perturbedMomenta_of_ne p l k t hkl
  have hpk0 : ∀ k, k ≠ l → p k ≠ 0 := by
    intro k hkl hzero
    have : k = l := hinj (hzero.trans hpl.symm)
    exact hkl this
  have hNotOne : ∀ k, k ≠ l → z (p k) ≠ 1 := by
    intro k hkl
    exact z_ne_one (hp k) (hpk0 k hkl)
  calc
    _ = ∑ i : RootSlotWordFiberIndex m l,
        rootSlotWordFiberTerm (N := N) c x p q i :=
      sum_fixedAmplitudeWordTerm_eq_rootSlotWordFiberTerm x p q l
    _ = (∑ i : RootSlotWordConstantIndex m l,
          rootSlotWordFiberTerm (N := N) c x p q i.1) +
        (∑ i : RootSlotWordGoodIndex m l,
          rootSlotWordFiberTerm (N := N) c x p q i.1) +
        ∑ i : RootSlotWordBadIndex m l,
          rootSlotWordFiberTerm (N := N) c x p q i.1 :=
      sum_rootSlotWordFiberTerm_eq_constant_good_bad x p q l
    _ = constantWordSumPerturbed (N := N) c x p l t +
        ∑ i : T1PairIndex m l, t1PairTerm (N := N) c x p l t i := by
      rw [sum_rootSlotWordBadFiberTerm_eq_zero hc hm p q x l hBE hAgree hNotOne,
        sum_rootSlotWordConstantFiberTerm_eq_constantWordSumPerturbed,
        sum_rootSlotWordGoodFiberTerm_eq_sum_t1PairTerm x p l t hm]
      ring

end PottsDiscontinuity.BetheAnsatz
