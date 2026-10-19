module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordFiniteSum
public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordGoodFiber

/-!
# Finite indices for the surviving zero-root word terms

The complete word expansion is indexed by a root slot, a word, and a constrained
permutation. This file relates that index to the good root-incident subtype and
to the paired T₁ representatives.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- All words and permutations, grouped by the slot occupied by the root label. -/
abbrev RootSlotWordFiberIndex (n : ℕ) (l : Fin (n + 1)) :=
  RootSlotFiberIndex n l × (Fin (n + 1) → Bool)

/-- Reindex a root-slot/word fiber as a permutation and word. -/
noncomputable def rootSlotWordFiberEquiv {n : ℕ} (l : Fin (n + 1)) :
    RootSlotWordFiberIndex n l ≃
      (Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool)) where
  toFun i := (rootSlotFiberEquiv l i.1, i.2)
  invFun q := ((rootSlotFiberEquiv l).symm q.1, q.2)
  left_inv := by
    intro q
    cases q with
    | mk s w => exact congrArg (fun t => (t, w)) ((rootSlotFiberEquiv l).left_inv s)
  right_inv := by
    intro q
    cases q with
    | mk σ w => exact congrArg (fun t => (t, w)) ((rootSlotFiberEquiv l).right_inv σ)

/-- The word value associated with the root-slot good-fiber condition. -/
def rootSlotWordGood {n : ℕ} (l : Fin (n + 1))
    (i : RootSlotWordFiberIndex n l) : Prop :=
  RootIncidentFiberPredicate l (i.1.val.1, (i.1.val.2, i.2))

/-- The two constant words, retained for the T₀ contribution. -/
def rootSlotWordConstant {n : ℕ} {l : Fin (n + 1)}
    (i : RootSlotWordFiberIndex n l) : Prop :=
  i.2 = (fun _ => true) ∨ i.2 = (fun _ => false)

/-- The surviving root-slot/word indices: the two constant words or a good T₁ fiber. -/
def rootSlotWordSurvivor {n : ℕ} (l : Fin (n + 1))
    (i : RootSlotWordFiberIndex n l) : Prop :=
  rootSlotWordConstant i ∨ rootSlotWordGood l i

abbrev RootSlotWordConstantIndex (n : ℕ) (l : Fin (n + 1)) :=
  {i : RootSlotWordFiberIndex n l // rootSlotWordConstant i}

abbrev RootSlotWordGoodIndex (n : ℕ) (l : Fin (n + 1)) :=
  {i : RootSlotWordFiberIndex n l // rootSlotWordGood l i}

abbrev RootSlotWordBadIndex (n : ℕ) (l : Fin (n + 1)) :=
  {i : RootSlotWordFiberIndex n l //
    ¬ rootSlotWordConstant i ∧ ¬ rootSlotWordGood l i}

abbrev RootSlotWordSurvivorIndex (n : ℕ) (l : Fin (n + 1)) :=
  {i : RootSlotWordFiberIndex n l // rootSlotWordSurvivor l i}

theorem rootSlotWordGood_notConstant {n : ℕ} {l : Fin (n + 1)}
    {i : RootSlotWordFiberIndex n l} (hi : rootSlotWordGood l i) :
    ¬ rootSlotWordConstant i := by
  intro hc
  rcases hi with ⟨_, htrue, hfalse, _⟩
  rcases hc with hc | hc
  · exact htrue hc
  · exact hfalse hc

/-- Within the survivor subtype, the constant part is the original constant subtype. -/
noncomputable def rootSlotWordSurvivorConstantEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordSurvivorIndex n l // rootSlotWordConstant i.1} ≃
      RootSlotWordConstantIndex n l where
  toFun i := ⟨i.1.1, i.2⟩
  invFun i := ⟨⟨i.1, Or.inl i.2⟩, i.2⟩
  left_inv := by intro i; apply Subtype.ext; rfl
  right_inv := by intro i; apply Subtype.ext; rfl

/-- Within the survivor subtype, the nonconstant part is exactly the good subtype. -/
noncomputable def rootSlotWordSurvivorGoodEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordSurvivorIndex n l // ¬ rootSlotWordConstant i.1} ≃
      RootSlotWordGoodIndex n l where
  toFun i := ⟨i.1.1, Or.resolve_left i.1.2 i.2⟩
  invFun i := ⟨⟨i.1, Or.inr i.2⟩, rootSlotWordGood_notConstant i.2⟩
  left_inv := by intro i; apply Subtype.ext; rfl
  right_inv := by intro i; apply Subtype.ext; rfl

/-- A Boolean selecting one of the two constant words. -/
abbrev ConstantWordIndex (n : ℕ) :=
  {w : Fin (n + 1) → Bool //
    w = (fun _ => true) ∨ w = (fun _ => false)}

noncomputable def constantWordEquiv {n : ℕ} : Bool ≃ ConstantWordIndex n where
  toFun b := ⟨fun _ => b, by cases b <;> simp⟩
  invFun w := w.1 0
  left_inv := by intro b; cases b <;> rfl
  right_inv := by
    intro w
    apply Subtype.ext
    change (fun _ : Fin (n + 1) => w.1 0) = w.1
    rcases w.2 with hT | hF
    · rw [hT]
    · rw [hF]

/-- Separate the word and permutation coordinates on constant root fibers. -/
noncomputable def rootSlotWordConstantSubtypeEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordFiberIndex n l // rootSlotWordConstant i} ≃
      RootSlotFiberIndex n l × ConstantWordIndex n where
  toFun i := (i.1.1, ⟨i.1.2, i.2⟩)
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv := by
    intro i
    apply Subtype.ext
    rfl
  right_inv := by
    intro q
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

/-- Reindex constant root-slot terms by the permutation and constant-word bit. -/
noncomputable def rootSlotWordConstantEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordFiberIndex n l // rootSlotWordConstant i} ≃
      Equiv.Perm (Fin (n + 1)) × Bool :=
  rootSlotWordConstantSubtypeEquiv.trans
    (Equiv.prodCongr (rootSlotFiberEquiv l) constantWordEquiv.symm)

/-- The good root-slot/word indices are exactly the root-incident T₁ indices. -/
noncomputable def rootSlotWordGoodEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordFiberIndex n l // rootSlotWordGood l i} ≃
      RootIncidentFiberTermIndex n l where
  toFun i := by
    let d : RootFiberRawData n := (i.1.1.val.1, (i.1.1.val.2, i.1.2))
    exact ⟨d, i.2⟩
  invFun j := by
    rcases j with ⟨d, hd⟩
    rcases d with ⟨r, sw⟩
    rcases sw with ⟨σ, w⟩
    exact ⟨(⟨(r, σ), hd.1⟩, w), hd⟩
  left_inv := by
    rintro ⟨⟨s, w⟩, hi⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  right_inv := by
    intro j
    apply Subtype.ext
    rfl

/-- A nonconstant word with a selected ML edge disjoint from the root slot. -/
def RootSlotBadWord {n : ℕ} (r : Fin (n + 1)) :=
  {w : Fin (n + 1) → Bool //
    w ≠ (fun _ => true) ∧ w ≠ (fun _ => false) ∧
      ¬ ∀ a, w a = false → w (finRotate (n + 1) a) = true →
        r = a ∨ r = finRotate (n + 1) a}

noncomputable instance rootSlotPermFintype {n : ℕ} {l r : Fin (n + 1)} :
    Fintype (RootSlotPerm l r) := by
  classical
  exact Fintype.subtype
    ((Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))).filter (fun σ => σ r = l))
    (by intro σ; simp)

noncomputable instance rootSlotBadWordFintype {n : ℕ} (r : Fin (n + 1)) :
    Fintype (RootSlotBadWord r) := by
  classical
  exact Fintype.subtype
    ((Finset.univ : Finset (Fin (n + 1) → Bool)).filter
      (fun w => w ≠ (fun _ => true) ∧ w ≠ (fun _ => false) ∧
        ¬ ∀ a, w a = false → w (finRotate (n + 1) a) = true →
          r = a ∨ r = finRotate (n + 1) a))
    (by intro w; simp)

/-- The bad root-slot word/permutation fibers, grouped so permutations are summed
last and can be canceled by the selected ML edge. -/
abbrev RootSlotBadFiberIndex {n : ℕ} (l : Fin (n + 1)) :=
  Σ r : Fin (n + 1), RootSlotBadWord r × RootSlotPerm l r

/-- The complement of the constant and good root-slot/word terms is exactly
the set of nonconstant words with an ML edge away from the root slot. -/
noncomputable def rootSlotWordBadEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordFiberIndex n l //
      ¬ rootSlotWordConstant i ∧ ¬ rootSlotWordGood l i} ≃
      RootSlotBadFiberIndex l where
  toFun i := by
    let r := i.1.1.val.1
    let σ := i.1.1.val.2
    let w := i.1.2
    have hL : w ≠ (fun _ => true) := by
      intro h
      exact i.2.1 (Or.inl h)
    have hM : w ≠ (fun _ => false) := by
      intro h
      exact i.2.1 (Or.inr h)
    have hnotall : ¬ ∀ a, w a = false → w (finRotate (n + 1) a) = true →
        r = a ∨ r = finRotate (n + 1) a := by
      intro hAll
      exact i.2.2 ⟨i.1.1.property, hL, hM, hAll⟩
    exact ⟨r, ⟨w, ⟨hL, hM, hnotall⟩⟩,
      ⟨σ, i.1.1.property⟩⟩
  invFun j := by
    rcases j with ⟨r, ⟨w, hw⟩, σ⟩
    let i : RootSlotWordFiberIndex n l :=
      (⟨(r, σ.1), σ.2⟩, w)
    have hconst : ¬ rootSlotWordConstant i := by
      intro h
      rcases h with hT | hF
      · exact hw.1 hT
      · exact hw.2.1 hF
    have hgood : ¬ rootSlotWordGood l i := by
      intro hg
      rcases hg with ⟨_, _, _, hAll⟩
      exact hw.2.2 hAll
    exact ⟨i, hconst, hgood⟩
  left_inv := by
    intro i
    apply Subtype.ext
    rfl
  right_inv := by
    intro j
    cases j with
    | mk r rest =>
      rcases rest with ⟨w, σ⟩
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl

/-- The complement of the survivor indices is exactly the bad subtype. -/
noncomputable def rootSlotWordSurvivorComplementEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordFiberIndex n l // ¬ rootSlotWordSurvivor l i} ≃
      RootSlotWordBadIndex n l where
  toFun i := ⟨i.1, ⟨fun h => i.2 (Or.inl h), fun h => i.2 (Or.inr h)⟩⟩
  invFun i := ⟨i.1, fun h => h.elim i.2.1 i.2.2⟩
  left_inv := by intro i; apply Subtype.ext; rfl
  right_inv := by intro i; apply Subtype.ext; rfl

/-- The fixed-amplitude summand at a root-slot/word index. -/
noncomputable def rootSlotWordFiberTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ) {l : Fin (n + 1)}
    (i : RootSlotWordFiberIndex n l) : ℂ :=
  fixedAmplitudeWordTerm (N := N) c x p q i.1.val.2 i.2

/-- The same fixed-amplitude summand on the bad-word fiber index. -/
noncomputable def rootSlotBadFiberTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ) {l : Fin (n + 1)}
    (i : RootSlotBadFiberIndex l) : ℂ :=
  fixedAmplitudeWordTerm (N := N) c x p q i.2.2.1 i.2.1.1

/-- All nonconstant root-slot fibers outside the good set cancel after grouping
permutations by the selected root slot and word. -/
theorem sum_rootSlotWordBadFiberTerm_eq_zero {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (hn : 0 < n) (p q : Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → ℤ) (l : Fin (n + 1))
    (hBE : BetheEquations N (anisotropy c) p)
    (hAgree : ∀ k, k ≠ l → q k = p k)
    (hNotOne : ∀ k, k ≠ l → z (p k) ≠ 1) :
    (∑ i : {i : RootSlotWordFiberIndex n l //
      ¬ rootSlotWordConstant i ∧ ¬ rootSlotWordGood l i},
      rootSlotWordFiberTerm (N := N) c x p q i.1) = 0 := by
  classical
  let g : RootSlotBadFiberIndex l → ℂ :=
    rootSlotBadFiberTerm (N := N) c x p q
  calc
    _ = ∑ i : {i : RootSlotWordFiberIndex n l //
        ¬ rootSlotWordConstant i ∧ ¬ rootSlotWordGood l i},
        g (rootSlotWordBadEquiv (l := l) i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rfl
    _ = ∑ i : RootSlotBadFiberIndex l, g i := Equiv.sum_comp
      (rootSlotWordBadEquiv (l := l)) g
    _ = ∑ r : Fin (n + 1), ∑ w : RootSlotBadWord r,
        ∑ σ : RootSlotPerm l r,
          fixedAmplitudeWordTerm (N := N) c x p q σ.1 w.1 := by
      simp only [g, rootSlotBadFiberTerm, Fintype.sum_sigma, Fintype.sum_prod_type]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      apply Finset.sum_eq_zero
      intro w hw
      rcases w.2 with ⟨hL, hM, hnotall⟩
      have hAway : ∃ a, w.1 a = false ∧ w.1 (finRotate (n + 1) a) = true ∧
          r ≠ a ∧ r ≠ finRotate (n + 1) a := by
        by_contra h
        apply hnotall
        intro a ha hb
        by_contra hinc
        exact h ⟨a, ha, hb, (not_or.mp hinc).1, (not_or.mp hinc).2⟩
      rcases hAway with ⟨a, ha, hb, hra, hrb⟩
      exact sum_rootSlotFiber_fixedAmplitudeWordTerm_eq_zero_of_ML_away
        hc hn p q x l r a w.1 hBE hAgree hNotOne ha hb hra hrb

/-- The fixed-amplitude summand on a canonical root-incident term index. -/
noncomputable def rootIncidentTermTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ) {l : Fin (n + 1)}
    (i : RootIncidentTermIndex n l) : ℂ :=
  fixedAmplitudeWordTerm (N := N) c x p q i.σ.1 i.w

/-- The sum of the two constant root-slot/word fibers is exactly T₀. -/
theorem sum_rootSlotWordConstantFiberTerm_eq_constantWordSumPerturbed
    {N n : ℕ} {c : ℝ} (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (l : Fin (n + 1)) (t : ℝ) :
    (∑ i : {i : RootSlotWordFiberIndex n l // rootSlotWordConstant i},
      rootSlotWordFiberTerm (N := N) c x p (perturbedMomenta p l t) i.1) =
      constantWordSumPerturbed (N := N) c x p l t := by
  classical
  let e := rootSlotWordConstantEquiv (n := n) (l := l)
  let f : Equiv.Perm (Fin (n + 1)) × Bool → ℂ := fun q =>
    fixedAmplitudeWordTerm (N := N) c x p (perturbedMomenta p l t)
      q.1 (fun _ => q.2)
  calc
    _ = ∑ i : {i : RootSlotWordFiberIndex n l // rootSlotWordConstant i},
        f (e i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rcases i.2 with hT | hF
          · simp [f, e, rootSlotWordFiberTerm, rootSlotWordConstantEquiv,
              rootSlotWordConstantSubtypeEquiv, rootSlotFiberEquiv,
              constantWordEquiv, hT]
          · simp [f, e, rootSlotWordFiberTerm, rootSlotWordConstantEquiv,
              rootSlotWordConstantSubtypeEquiv, rootSlotFiberEquiv,
              constantWordEquiv, hF]
    _ = ∑ q : Equiv.Perm (Fin (n + 1)) × Bool, f q := Equiv.sum_comp e f
    _ = constantWordSumPerturbed (N := N) c x p l t := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool]
      unfold constantWordSumPerturbed
      apply Finset.sum_congr rfl
      intro σ hσ
      simp [f, fixedAmplitudeWordTerm, wordCoefficient_false, wordCoefficient_true,
        wordPhase_false, wordPhase_true]; ring

/-- Convert a good root-slot/word index to its unique canonical T₁ index. -/
noncomputable def rootSlotWordGoodToIncidentEquiv {n : ℕ} {l : Fin (n + 1)}
    (hn : 0 < n) :
    {i : RootSlotWordFiberIndex n l // rootSlotWordGood l i} ≃
      RootIncidentTermIndex n l :=
  rootSlotWordGoodEquiv.trans (rootIncidentFiberEquiv hn).symm

/-- The good-fiber summand is the fixed-amplitude term indexed by its canonical
root-incident T₁ index. -/
theorem rootSlotWordGoodFiberTerm_eq_incidentTerm {N n : ℕ} {c : ℝ}
    {l : Fin (n + 1)} (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ)
    (hn : 0 < n) (i : {i : RootSlotWordFiberIndex n l // rootSlotWordGood l i}) :
    rootSlotWordFiberTerm (N := N) c x p q i.1 =
      rootIncidentTermTerm (N := N) c x p q (rootSlotWordGoodToIncidentEquiv hn i) := by
  let j := rootSlotWordGoodToIncidentEquiv hn i
  have hdata : rootIncidentFiberUnderlying j = rootSlotWordGoodEquiv i := by
    exact (rootIncidentFiberEquiv hn).apply_symm_apply (rootSlotWordGoodEquiv i)
  have hraw := congrArg Subtype.val hdata
  have hσ := congrArg (fun d : RootFiberRawData n => d.2.1) hraw
  have hw := congrArg (fun d : RootFiberRawData n => d.2.2) hraw
  have hσ' : j.σ.1 = i.1.1.val.2 := by
    simpa [rootIncidentFiberUnderlying, rootSlotWordGoodEquiv] using hσ
  have hw' : j.w = i.1.2 := by
    simpa [rootIncidentFiberUnderlying, rootSlotWordGoodEquiv] using hw
  unfold rootSlotWordFiberTerm rootIncidentTermTerm
  change fixedAmplitudeWordTerm (N := N) c x p q i.1.1.val.2 i.1.2 =
    fixedAmplitudeWordTerm (N := N) c x p q j.σ.1 j.w
  rw [hσ', hw']

/-- Reindex the sum of all good root-slot/word fibers as paired T₁ terms. -/
theorem sum_rootSlotWordGoodFiberTerm_eq_sum_t1PairTerm {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (l : Fin (n + 1)) (t : ℝ) (hn : 0 < n) :
    (∑ i : {i : RootSlotWordFiberIndex n l // rootSlotWordGood l i},
      rootSlotWordFiberTerm (N := N) c x p (perturbedMomenta p l t) i.1) =
      ∑ i : T1PairIndex n l, t1PairTerm (N := N) c x p l t i := by
  classical
  let e := rootSlotWordGoodToIncidentEquiv (n := n) (l := l) hn
  let f : RootIncidentTermIndex n l → ℂ :=
    rootIncidentTermTerm (N := N) c x p (perturbedMomenta p l t)
  calc
    _ = ∑ i : {i : RootSlotWordFiberIndex n l // rootSlotWordGood l i},
        f (e i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact rootSlotWordGoodFiberTerm_eq_incidentTerm x p
            (perturbedMomenta p l t) hn i
    _ = ∑ j : RootIncidentTermIndex n l, f j := Equiv.sum_comp e f
    _ = ∑ j : T1PairIndex n l × Bool,
        f (t1PairSideEquiv j) := (Equiv.sum_comp t1PairSideEquiv f).symm
    _ = ∑ i : T1PairIndex n l, t1PairTerm (N := N) c x p l t i := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i hi
      simp [f, t1PairTerm, rootIncidentTermTerm, t1PairSideEquiv,
        t1PairSideForward, fixedAmplitudeWordTerm, perturbedWordTerm]; ring

/-- The full root-slot/word sum partitions into its two constant words, good
root-incident fibers, and the nonconstant fibers canceled by an away ML edge. -/
theorem sum_rootSlotWordFiberTerm_eq_constant_good_bad {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    (∑ i : RootSlotWordFiberIndex n l,
      rootSlotWordFiberTerm (N := N) c x p q i) =
      (∑ i : RootSlotWordConstantIndex n l,
        rootSlotWordFiberTerm (N := N) c x p q i.1) +
      (∑ i : RootSlotWordGoodIndex n l,
        rootSlotWordFiberTerm (N := N) c x p q i.1) +
      ∑ i : RootSlotWordBadIndex n l,
        rootSlotWordFiberTerm (N := N) c x p q i.1 := by
  classical
  let f : RootSlotWordFiberIndex n l → ℂ :=
    rootSlotWordFiberTerm (N := N) c x p q
  change (∑ i : RootSlotWordFiberIndex n l, f i) =
    (∑ i : RootSlotWordConstantIndex n l, f i.1) +
    (∑ i : RootSlotWordGoodIndex n l, f i.1) +
    ∑ i : RootSlotWordBadIndex n l, f i.1
  have houter := Fintype.sum_subtype_add_sum_subtype
    (rootSlotWordSurvivor l) f
  have hinner := Fintype.sum_subtype_add_sum_subtype
    (fun i : RootSlotWordSurvivorIndex n l => rootSlotWordConstant i.1)
    (fun i => f i.1)
  have hconst :
      (∑ i : {i : RootSlotWordSurvivorIndex n l // rootSlotWordConstant i.1},
        f i.1.1) = ∑ i : RootSlotWordConstantIndex n l, f i.1 := by
    let e := rootSlotWordSurvivorConstantEquiv (n := n) (l := l)
    calc
      _ = ∑ i : {i : RootSlotWordSurvivorIndex n l // rootSlotWordConstant i.1},
          f (e i).1 := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = ∑ i : RootSlotWordConstantIndex n l, f i.1 :=
        Equiv.sum_comp e (fun i => f i.1)
  have hgood :
      (∑ i : {i : RootSlotWordSurvivorIndex n l // ¬ rootSlotWordConstant i.1},
        f i.1.1) = ∑ i : RootSlotWordGoodIndex n l, f i.1 := by
    let e := rootSlotWordSurvivorGoodEquiv (n := n) (l := l)
    calc
      _ = ∑ i : {i : RootSlotWordSurvivorIndex n l // ¬ rootSlotWordConstant i.1},
          f (e i).1 := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = ∑ i : RootSlotWordGoodIndex n l, f i.1 :=
        Equiv.sum_comp e (fun i => f i.1)
  have hbad :
      (∑ i : {i : RootSlotWordFiberIndex n l // ¬ rootSlotWordSurvivor l i},
        f i.1) = ∑ i : RootSlotWordBadIndex n l, f i.1 := by
    let e := rootSlotWordSurvivorComplementEquiv (n := n) (l := l)
    calc
      _ = ∑ i : {i : RootSlotWordFiberIndex n l // ¬ rootSlotWordSurvivor l i},
          f (e i).1 := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = ∑ i : RootSlotWordBadIndex n l, f i.1 :=
        Equiv.sum_comp e (fun i => f i.1)
  calc
    _ = (∑ i : RootSlotWordSurvivorIndex n l, f i.1) +
        ∑ i : {i : RootSlotWordFiberIndex n l // ¬ rootSlotWordSurvivor l i}, f i.1 :=
      houter.symm
    _ = ((∑ i : RootSlotWordConstantIndex n l, f i.1) +
        ∑ i : RootSlotWordGoodIndex n l, f i.1) +
        ∑ i : RootSlotWordBadIndex n l, f i.1 := by
      rw [← hinner, hconst, hgood, hbad]

end PottsDiscontinuity.BetheAnsatz
