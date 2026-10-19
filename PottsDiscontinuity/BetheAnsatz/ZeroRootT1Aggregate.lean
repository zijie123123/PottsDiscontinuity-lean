module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1OutputEquivalence
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RegularizedResidue

/-!
# The aggregate T₁ contribution after zipper reindexing

The output index is equivalent to an output permutation together with an
allowed ML-left slot. This exposes the derivative sum over all nonzero root
labels and the single seam indicator.
-/

@[expose] public section

open Finset Complex

namespace PottsDiscontinuity.BetheAnsatz

/-- A cyclic edge's left endpoint, including the seam edge at `Fin.last`. -/
def t1EdgeLeftEquiv {n : ℕ} : Option (Fin n) ≃ Fin (n + 1) where
  toFun := t1EdgeLeft
  invFun := fun m => Fin.lastCases none (fun j => some j) m
  left_inv := by
    intro e
    cases e <;> simp [t1EdgeLeft, Fin.lastCases_last, Fin.lastCases_castSucc]
  right_inv := by
    intro m
    refine Fin.lastCases ?_ (fun j => ?_) m
    · simp [t1EdgeLeft, Fin.lastCases_last]
    · simp [t1EdgeLeft, Fin.lastCases_castSucc]

/-- Forget the seam/ordinary presentation and retain the left endpoint slot. -/
noncomputable def t1OutputIndexSigmaEquiv {n : ℕ} {l : Fin (n + 1)} :
    T1OutputIndex n l ≃ Σ σ : Equiv.Perm (Fin (n + 1)),
      {m : Fin (n + 1) // m ≠ σ.symm l} where
  toFun o := ⟨o.σ, ⟨t1EdgeLeftEquiv o.edge, o.hleft⟩⟩
  invFun q := ⟨q.1, t1EdgeLeftEquiv.symm q.2.1, by
    have hm := q.2.2
    change t1EdgeLeftEquiv (t1EdgeLeftEquiv.symm q.2.1) ≠ q.1.symm l
    rw [t1EdgeLeftEquiv.apply_symm_apply]
    exact hm⟩
  left_inv := by
    intro o
    apply T1OutputIndex.ext
    · rfl
    · exact t1EdgeLeftEquiv.symm_apply_apply o.edge
  right_inv := by
    rintro ⟨σ, ⟨m, hm⟩⟩
    cases m using Fin.lastCases with
    | last => simp [t1EdgeLeftEquiv, t1EdgeLeft]
    | cast j => simp [t1EdgeLeftEquiv, t1EdgeLeft]

/-- The corrected phase slope attached to an output permutation and a slot. -/
noncomputable def t1OutputSlope {N n : ℕ} (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (m : Fin (n + 1)) : ℂ :=
  (zeroRootPhaseDerivative (N := N) Δ (p (σ m)) False : ℂ) +
    if m = Fin.last n then (N : ℂ) else 0

/-- The all-M regularized coefficient times the corrected slope. -/
noncomputable def t1OutputLimitTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (o : T1OutputIndex n l) : ℂ :=
  zeroRootRegularizedWordTerm (N := N) c x p l o.σ (fun _ => false) *
    t1OutputSlope (N := N) (anisotropy c) p o.σ (t1EdgeLeft o.edge)

/-- The same limit summand in permutation/left-slot coordinates. -/
noncomputable def t1SigmaLimitTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (q : Σ σ : Equiv.Perm (Fin (n + 1)),
      {m : Fin (n + 1) // m ≠ σ.symm l}) : ℂ :=
  zeroRootRegularizedWordTerm (N := N) c x p l q.1 (fun _ => false) *
    t1OutputSlope (N := N) (anisotropy c) p q.1 q.2.1

theorem t1OutputLimitTerm_sigma {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (q : Σ σ : Equiv.Perm (Fin (n + 1)),
      {m : Fin (n + 1) // m ≠ σ.symm l}) :
    t1OutputLimitTerm (N := N) c x p l (t1OutputIndexSigmaEquiv.symm q) =
      t1SigmaLimitTerm (N := N) c x p l q := by
  unfold t1OutputLimitTerm t1SigmaLimitTerm
  change zeroRootRegularizedWordTerm (N := N) c x p l q.1 (fun _ => false) *
      t1OutputSlope (N := N) (anisotropy c) p q.1
        (t1EdgeLeftEquiv (t1EdgeLeftEquiv.symm q.2.1)) = _
  rw [t1EdgeLeftEquiv.apply_symm_apply]

/-- Output slots other than the zero slot correspond exactly to the nonzero
root labels under an output permutation. -/
noncomputable def t1OutputSlotLabelEquiv {n : ℕ} (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    {m : Fin (n + 1) // m ≠ σ.symm l} ≃ {j : Fin (n + 1) // j ≠ l} where
  toFun m := ⟨σ m.1, by
    intro h
    apply m.2
    apply σ.injective
    calc
      σ m.1 = l := h
      _ = σ (σ.symm l) := (σ.apply_symm_apply l).symm⟩
  invFun j := ⟨σ.symm j.1, by
    intro h
    apply j.2
    have h' := congrArg σ h
    simpa using h'⟩
  left_inv := by
    intro m
    apply Subtype.ext
    simp
  right_inv := by
    intro j
    apply Subtype.ext
    simp

theorem sum_t1OutputDerivative_slots {N n : ℕ} (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      (zeroRootPhaseDerivative (N := N) Δ (p (σ m.1)) False : ℂ)) =
      ∑ j : {j : Fin (n + 1) // j ≠ l},
        (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ) := by
  exact Equiv.sum_comp (t1OutputSlotLabelEquiv l σ)
    (fun j : {j : Fin (n + 1) // j ≠ l} =>
      (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ))

theorem sum_t1OutputSeam_slots {N n : ℕ} (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      if m.1 = Fin.last n then (N : ℂ) else 0) =
      if σ (Fin.last n) = l then 0 else (N : ℂ) := by
  classical
  by_cases hroot : σ.symm l = Fin.last n
  · have hσ : σ (Fin.last n) = l := by
      rw [← hroot]
      exact σ.apply_symm_apply l
    have hzero : ∀ m : {m : Fin (n + 1) // m ≠ σ.symm l},
        (if m.1 = Fin.last n then (N : ℂ) else 0) = 0 := by
      intro m
      have hm : m.1 ≠ Fin.last n := by
        intro heq
        apply m.2
        calc
          m.1 = Fin.last n := heq
          _ = σ.symm l := hroot.symm
      simp [hm]
    have hsum : (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
        (if m.1 = Fin.last n then (N : ℂ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      exact hzero m
    rw [hsum]
    simp [hσ]
  · let m₀ : {m : Fin (n + 1) // m ≠ σ.symm l} :=
      ⟨Fin.last n, fun h => hroot h.symm⟩
    have hzero : ∀ m ∈ (Finset.univ : Finset {m : Fin (n + 1) // m ≠ σ.symm l}),
        m ≠ m₀ → (if m.1 = Fin.last n then (N : ℂ) else 0) = 0 := by
      intro m hm hne
      have hlast : m.1 ≠ Fin.last n := by
        intro heq
        apply hne
        apply Subtype.ext
        exact heq
      simp [hlast]
    have hmem : m₀ ∈ (Finset.univ : Finset {m : Fin (n + 1) // m ≠ σ.symm l}) :=
      Finset.mem_univ _
    have hsum := Finset.sum_eq_single_of_mem m₀ hmem hzero
    have hσne : σ (Fin.last n) ≠ l := by
      intro h
      apply hroot
      apply σ.injective
      calc
        σ (σ.symm l) = l := σ.apply_symm_apply l
        _ = σ (Fin.last n) := h.symm
    simpa [m₀, hσne] using hsum

theorem sum_t1OutputSlope_slots {N n : ℕ} (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      t1OutputSlope (N := N) Δ p σ m.1) =
      (∑ j : {j : Fin (n + 1) // j ≠ l},
        (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ)) +
        if σ (Fin.last n) = l then 0 else (N : ℂ) := by
  simp only [t1OutputSlope, Finset.sum_add_distrib]
  rw [sum_t1OutputDerivative_slots, sum_t1OutputSeam_slots]

theorem t1PairLimit_eq_t1OutputLimitTerm {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) (i : T1PairIndex n l) :
    t1PairLimit (N := N) c x p l i =
      t1OutputLimitTerm (N := N) c x p l (t1PairOutputIndex i) := by
  let o := t1PairOutputIndex i
  have hoedge : o.edge = i.edge := rfl
  have hword : (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).2 =
      (fun _ => false) := by
    funext k
    exact t1PairZipperRun_word_eq_false i k
  have hreg := t1PairZipperRun_preserves hc x p hp hinj l hpl hBE i
  have hσout : o.σ = (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).1 := rfl
  have hreg' : zeroRootRegularizedWordTerm (N := N) c x p l o.σ (fun _ => false) =
      zeroRootRegularizedWordTerm (N := N) c x p l i.σ i.w := by
    rw [hσout]
    simpa [hword] using hreg
  have hlabel : p (o.σ (t1EdgeLeft i.edge)) =
      p (i.σ (t1EdgeLeft i.edge)) := by
    exact congrArg p (t1PairOutputIndex_left i)
  have hlim := t1PairLimit_eq_regularizedWordTerm (N := N) (c := c) x p l i
  change t1PairLimit (N := N) c x p l i =
    zeroRootRegularizedWordTerm (N := N) c x p l o.σ (fun _ => false) *
      t1OutputSlope (N := N) (anisotropy c) p o.σ (t1EdgeLeft o.edge)
  cases hEdge : i.edge with
  | none =>
      have hlabel' : p (o.σ (Fin.last n)) = p (i.σ (Fin.last n)) := by
        simpa [hEdge, t1EdgeLeft] using hlabel
      rw [hlim, ← hreg']
      simp only [hEdge, zeroRootPhaseDerivative]
      rw [← hlabel']
      simp [t1OutputSlope, t1EdgeLeft, hoedge, hEdge, zeroRootPhaseDerivative]
  | some a =>
      have hlabel' : p (o.σ a.castSucc) = p (i.σ a.castSucc) := by
        simpa [hEdge, t1EdgeLeft] using hlabel
      rw [hlim, ← hreg']
      simp only [hEdge, zeroRootPhaseDerivative]
      rw [← hlabel']
      simp [t1OutputSlope, t1EdgeLeft, hoedge, hEdge, zeroRootPhaseDerivative]

theorem tendsto_sum_t1PairLimit_eq_sum_t1SigmaLimitTerm {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    (∑ i : T1PairIndex n l, t1PairLimit (N := N) c x p l i) =
      ∑ q : Σ σ : Equiv.Perm (Fin (n + 1)),
        {m : Fin (n + 1) // m ≠ σ.symm l}, t1SigmaLimitTerm (N := N) c x p l q := by
  calc
    _ = ∑ i : T1PairIndex n l,
          t1OutputLimitTerm (N := N) c x p l (t1PairOutputIndex i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact t1PairLimit_eq_t1OutputLimitTerm hc x p hp hinj l hpl hBE i
    _ = ∑ o : T1OutputIndex n l, t1OutputLimitTerm (N := N) c x p l o :=
      Equiv.sum_comp t1PairOutputEquiv
        (t1OutputLimitTerm (N := N) c x p l)
    _ = ∑ q : Σ σ : Equiv.Perm (Fin (n + 1)),
          {m : Fin (n + 1) // m ≠ σ.symm l},
          t1OutputLimitTerm (N := N) c x p l (t1OutputIndexSigmaEquiv.symm q) :=
      (Equiv.sum_comp t1OutputIndexSigmaEquiv.symm
        (t1OutputLimitTerm (N := N) c x p l)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact t1OutputLimitTerm_sigma c x p l q
end PottsDiscontinuity.BetheAnsatz
