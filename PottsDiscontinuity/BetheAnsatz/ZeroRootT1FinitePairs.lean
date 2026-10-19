module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamResidue

/-!
# Finite sums of corrected T₁ pairs

This module sums the already checked ordinary-edge and seam-pair limits over a
finite type of canonical pair representatives. The combinatorial identification
of that type with the source's W₁ indexing is kept separate.
-/

@[expose] public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The left endpoint of an ordinary or seam edge in the cyclic word. -/
def t1EdgeLeft {n : ℕ} (a : Option (Fin n)) : Fin (n + 1) :=
  a.elim (Fin.last n) Fin.castSucc

/-- The right endpoint of an ordinary or seam edge in the cyclic word. -/
def t1EdgeRight {n : ℕ} (a : Option (Fin n)) : Fin (n + 1) :=
  a.elim 0 Fin.succ

/-- A canonical representative of a paired T₁ contribution. `none` denotes
the seam edge `last → 0`; `some a` denotes the ordinary edge `a.castSucc → a.succ`.
The word is required to have this as its unique cyclic `ML` edge. -/
structure T1PairIndex (n : ℕ) (l : Fin (n + 1)) where
  σ : Equiv.Perm (Fin (n + 1))
  w : Fin (n + 1) → Bool
  edge : Option (Fin n)
  hσ : σ (t1EdgeRight edge) = l
  hleft : w (t1EdgeLeft edge) = false
  hright : w (t1EdgeRight edge) = true
  hunique : ∀ k, w k = false → w (finRotate (n + 1) k) = true →
    k = t1EdgeLeft edge

noncomputable instance t1PairIndexFintype {n : ℕ} {l : Fin (n + 1)} :
    Fintype (T1PairIndex n l) := by
  classical
  apply Fintype.ofInjective (fun i => (i.σ, i.w, i.edge))
  intro i j hij
  cases i with
  | mk σ w edge hσ hleft hright hunique =>
    cases j with
    | mk σ' w' edge' hσ' hleft' hright' hunique' =>
      simp only [Prod.mk.injEq] at hij
      rcases hij with ⟨rfl, rfl, rfl⟩
      rfl

/-- One fixed-amplitude summand together with its paired permutation term. -/
noncomputable def t1PairTerm {N n : ℕ} (c : ℝ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ)
    (i : T1PairIndex n l) : ℂ :=
  perturbedWordTerm (N := N) c x p l t i.σ i.w +
    perturbedWordTerm (N := N) c x p l t
      (i.σ * Equiv.swap (t1EdgeLeft i.edge) (t1EdgeRight i.edge)) i.w

/-- The finite limit of a paired term, with the `N` seam slope included. -/
noncomputable def t1PairLimit {N n : ℕ} (c : ℝ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (i : T1PairIndex n l) : ℂ :=
  match i.edge with
  | some a =>
      ((c : ℂ)^2 * amplitude (anisotropy c) p i.σ *
        M c (z (p (i.σ a.castSucc))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) i.σ i.w a.castSucc *
        wordPhase (N := N) x p i.σ i.w) *
        (zeroRootPhaseDerivative (N := N) (anisotropy c)
          (p (i.σ a.castSucc)) False : ℂ)
  | none =>
      ((c : ℂ)^2 * amplitude (anisotropy c) p i.σ *
        M c (z (p (i.σ (Fin.last n)))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) i.σ i.w (Fin.last n) *
        wordPhase (N := N) x p i.σ i.w) *
        (zeroRootPhaseDerivative (N := N) (anisotropy c)
          (p (i.σ (Fin.last n))) True : ℂ)

/-- Every canonical ordinary or seam pair has the stated finite limit. -/
theorem tendsto_t1PairTerm {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) (i : T1PairIndex n l) :
    Tendsto (fun t : ℝ => t1PairTerm (N := N) c x p l t i)
      (𝓝[≠] (0 : ℝ)) (𝓝 (t1PairLimit (N := N) c x p l i)) := by
  cases hEdge : i.edge with
  | none =>
      have hn : 0 < n := by
        by_cases hn0 : n = 0
        · subst n
          have hfalse : i.w 0 = false := by simpa [hEdge, t1EdgeLeft] using i.hleft
          have htrue : i.w 0 = true := by simpa [hEdge, t1EdgeRight] using i.hright
          rw [hfalse] at htrue
          contradiction
        · omega
      have hlim := tendsto_seamT1_pair (N := N) hc x p hp hinj l hpl hBE
        i.σ i.w hn (by simpa [hEdge, t1EdgeRight] using i.hσ)
        (by simpa [hEdge, t1EdgeLeft] using i.hleft)
        (by simpa [hEdge, t1EdgeRight] using i.hright)
      simpa [t1PairTerm, t1PairLimit, hEdge, t1EdgeLeft, t1EdgeRight] using hlim
  | some a =>
      have hlim := tendsto_ordinaryT1_pair (N := N) hc x p hp hinj l hpl
        i.σ i.w a (by simpa [hEdge, t1EdgeRight] using i.hσ)
        (by simpa [hEdge, t1EdgeLeft] using i.hleft)
        (by simpa [hEdge, t1EdgeRight] using i.hright)
      simpa [t1PairTerm, t1PairLimit, hEdge, t1EdgeLeft, t1EdgeRight] using hlim

/-- The finite sum over canonical T₁ pair representatives commutes with the
punctured limit. -/
theorem tendsto_sum_t1PairTerm {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    Tendsto (fun t : ℝ => ∑ i : T1PairIndex n l, t1PairTerm (N := N) c x p l t i)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∑ i : T1PairIndex n l, t1PairLimit (N := N) c x p l i)) := by
  classical
  have hterm (i : T1PairIndex n l) := tendsto_t1PairTerm hc x p hp hinj l hpl hBE i
  have hsum : ∀ s : Finset (T1PairIndex n l),
      Tendsto (fun t : ℝ => ∑ i ∈ s, t1PairTerm (N := N) c x p l t i)
        (𝓝[≠] (0 : ℝ)) (𝓝 (∑ i ∈ s, t1PairLimit (N := N) c x p l i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simpa [Finset.sum_insert ha] using (hterm a).add ih
  simpa using hsum Finset.univ

end PottsDiscontinuity.BetheAnsatz
