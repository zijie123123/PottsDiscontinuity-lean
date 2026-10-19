module

public import PottsDiscontinuity.TorusCrossing.Lattice

/-!
# Closed one-cochains are exact (planar Poincare lemma on the rotated lattice)

A `ZMod 2`-valued function `f` on medial vertices is a *cochain*; its *degree* at a cell is
the sum over the four corners.  If the degree vanishes at every primal cell strictly between
two vertical lines, the left-ray potential `g(z) = sum_{a <= z.1} f(a, z.2) + c(z.2)` is a
primitive: `g` of the two dual endpoints of `m` sums to `f m`, for every medial vertex `m`
whose abscissa is between the two lines.  The correction `c` absorbs the (arbitrary) defects
on the left line; defects on the right line never enter.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

/-- Degree of a cochain at a cell: the sum over its four corners. -/
def cdeg (f : Cell → ZMod 2) (c : Cell) : ZMod 2 :=
  f c + f (c.1 + 1, c.2) + f (c.1, c.2 + 1) + f (c.1 + 1, c.2 + 1)

/-- Partial row sum of `f` over columns `x0 + 1, ..., i` of row `j`. -/
def rowSum (x0 : ℤ) (f : Cell → ZMod 2) (j i : ℤ) : ZMod 2 :=
  ∑ a ∈ Finset.Icc (x0 + 1) i, f (a, j)

/-- Defect of the cochain at the primal cell `(x0, k)` of the left line (zero for odd cells). -/
def leftDefect (x0 : ℤ) (f : Cell → ZMod 2) (k : ℤ) : ZMod 2 :=
  if IsPrimal (x0, k) then cdeg f (x0, k) else 0

/-- Accumulated left defects below row `j`, counted from row `y0`. -/
def leftCorr (x0 y0 : ℤ) (f : Cell → ZMod 2) (j : ℤ) : ZMod 2 :=
  ∑ k ∈ Finset.Ico y0 j, leftDefect x0 f k

/-- The left-ray potential. -/
def leftPotential (x0 y0 : ℤ) (f : Cell → ZMod 2) (z : Cell) : ZMod 2 :=
  rowSum x0 f z.2 z.1 + leftCorr x0 y0 f z.2

theorem rowSum_succ (x0 : ℤ) (f : Cell → ZMod 2) (j i : ℤ) (h : x0 ≤ i) :
    rowSum x0 f j (i + 1) = rowSum x0 f j i + f (i + 1, j) := by
  unfold rowSum
  rw [show Finset.Icc (x0 + 1) (i + 1) = insert (i + 1) (Finset.Icc (x0 + 1) i) by
    ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
  rw [Finset.sum_insert (by simp)]
  ring

theorem rowSum_of_le (x0 : ℤ) (f : Cell → ZMod 2) (j i : ℤ) (h : i ≤ x0) :
    rowSum x0 f j i = 0 := by
  unfold rowSum
  rw [Finset.Icc_eq_empty (by omega)]
  simp

/-- The two-step recursion for the sum of two consecutive row sums. -/
theorem rowSum_pair_step (x0 : ℤ) (f : Cell → ZMod 2) (b X : ℤ) (hX : x0 ≤ X - 2) :
    rowSum x0 f b X + rowSum x0 f (b - 1) X =
      rowSum x0 f b (X - 2) + rowSum x0 f (b - 1) (X - 2) + cdeg f (X - 1, b - 1) := by
  have h1 : rowSum x0 f b X = rowSum x0 f b (X - 2) + f (X - 1, b) + f (X, b) := by
    have := rowSum_succ x0 f b (X - 2) hX
    have h2 := rowSum_succ x0 f b (X - 1) (by omega)
    rw [show X - 2 + 1 = X - 1 by ring] at this
    rw [show X - 1 + 1 = X by ring] at h2
    rw [h2, this]
  have h2 : rowSum x0 f (b - 1) X =
      rowSum x0 f (b - 1) (X - 2) + f (X - 1, b - 1) + f (X, b - 1) := by
    have := rowSum_succ x0 f (b - 1) (X - 2) hX
    have h2 := rowSum_succ x0 f (b - 1) (X - 1) (by omega)
    rw [show X - 2 + 1 = X - 1 by ring] at this
    rw [show X - 1 + 1 = X by ring] at h2
    rw [h2, this]
  rw [h1, h2]
  unfold cdeg
  rw [show X - 1 + 1 = X by ring, show b - 1 + 1 = b by ring]
  ring

/-- Core identity: with left defects absorbed, consecutive row sums add up to the defect of the
left line. -/
theorem rowSum_pair (x0 : ℤ) (w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hdeg : ∀ c : Cell, IsPrimal c → x0 < c.1 → c.1 < x0 + w → cdeg f c = 0)
    (b : ℤ) : ∀ n : ℕ, (n : ℤ) ≤ w → ((x0 + n + b) % 2 = 0) →
      rowSum x0 f b (x0 + n) + rowSum x0 f (b - 1) (x0 + n) = leftDefect x0 f (b - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hpar
    have hnotprim : n % 2 = 0 → ¬ IsPrimal (x0, b - 1) := by
      intro h; unfold IsPrimal; dsimp only; omega
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · -- n = 0
        have : leftDefect x0 f (b - 1) = 0 := by
          unfold leftDefect; split_ifs with hh
          · exact absurd hh (hnotprim rfl)
          · rfl
        rw [this, rowSum_of_le x0 f b (x0 + ((0 : ℕ) : ℤ)) (by simp),
          rowSum_of_le x0 f (b - 1) (x0 + ((0 : ℕ) : ℤ)) (by simp)]
        simp
      · -- n = 1
        have hprim : IsPrimal (x0, b - 1) := by
          unfold IsPrimal; dsimp only; push_cast at hpar; omega
        unfold leftDefect; simp only [hprim, ite_true]
        unfold cdeg
        have e1 : rowSum x0 f b (x0 + ((1 : ℕ) : ℤ)) = f (x0 + 1, b) := by
          push_cast
          rw [rowSum_succ x0 f b x0 le_rfl, rowSum_of_le x0 f b x0 le_rfl]; simp
        have e2 : rowSum x0 f (b - 1) (x0 + ((1 : ℕ) : ℤ)) = f (x0 + 1, b - 1) := by
          push_cast
          rw [rowSum_succ x0 f (b - 1) x0 le_rfl, rowSum_of_le x0 f (b - 1) x0 le_rfl]; simp
        rw [e1, e2, hx0 (x0, b - 1) (by dsimp only; omega), hx0 (x0, b - 1 + 1) (by dsimp only; omega)]
        simp only [zero_add]
        ring_nf
    · -- n ≥ 2
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
      have hprim : IsPrimal (x0 + ((k + 2 : ℕ) : ℤ) - 1, b - 1) := by
        unfold IsPrimal; dsimp only; push_cast at hpar ⊢; omega
      have hstep := rowSum_pair_step x0 f b (x0 + ((k + 2 : ℕ) : ℤ)) (by push_cast; omega)
      have hih := ih k (by omega) (by push_cast at hn ⊢; omega) (by push_cast at hpar ⊢; omega)
      have hd := hdeg (x0 + ((k + 2 : ℕ) : ℤ) - 1, b - 1) hprim (by push_cast; omega)
        (by push_cast at hn ⊢; omega)
      rw [hstep, hd, add_zero]
      rw [show x0 + ((k + 2 : ℕ) : ℤ) - 2 = x0 + (k : ℤ) by push_cast; ring]
      exact hih


/-- Integer-indexed version of `rowSum_pair`. -/
theorem rowSum_pair' (x0 w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hdeg : ∀ c : Cell, IsPrimal c → x0 < c.1 → c.1 < x0 + w → cdeg f c = 0)
    (b X : ℤ) (h1 : x0 ≤ X) (h2 : X ≤ x0 + w) (hp : (X + b) % 2 = 0) :
    rowSum x0 f b X + rowSum x0 f (b - 1) X = leftDefect x0 f (b - 1) := by
  have := rowSum_pair x0 w f hx0 hdeg b (X - x0).toNat (by omega) (by omega)
  rwa [show x0 + ((X - x0).toNat : ℤ) = X by omega] at this

theorem leftCorr_succ (x0 y0 : ℤ) (f : Cell → ZMod 2)
    (hy0 : ∀ m : Cell, m.2 ≤ y0 → f m = 0) (b : ℤ) :
    leftCorr x0 y0 f b + leftCorr x0 y0 f (b - 1) = leftDefect x0 f (b - 1) := by
  by_cases h : y0 ≤ b - 1
  · unfold leftCorr
    rw [show Finset.Ico y0 b = insert (b - 1) (Finset.Ico y0 (b - 1)) by
      ext a; simp only [Finset.mem_Ico, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp)]
    have two : ∀ z : ZMod 2, z + z = 0 := fun z => by fin_cases z <;> decide
    generalize ∑ k ∈ Finset.Ico y0 (b - 1), leftDefect x0 f k = S
    generalize leftDefect x0 f (b - 1) = d
    calc d + S + S = d + (S + S) := by ring
      _ = d := by rw [two S, add_zero]
  · unfold leftCorr
    rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega)]
    have hd : leftDefect x0 f (b - 1) = 0 := by
      unfold leftDefect cdeg
      split_ifs
      · rw [hy0 (x0, b - 1) (by dsimp only; omega), hy0 (x0 + 1, b - 1) (by dsimp only; omega),
          hy0 (x0, b - 1 + 1) (by dsimp only; omega), hy0 (x0 + 1, b - 1 + 1) (by dsimp only; omega)]
        simp
      · rfl
    rw [hd]; simp

/-- **Planar Poincare lemma** (relative to the left line).  If the cochain `f` vanishes on and
to the left of the line `x0`, on and below the row `y0`, and has vanishing degree at every
primal cell strictly between the lines `x0` and `x0 + w`, then the left-ray potential is a
primitive of `f` at every medial vertex with abscissa in `(x0, x0 + w]`. -/
theorem zmod2_aux1 (R1' R1 R2 C1 C2 D F : ZMod 2) (h1 : R1 + R2 = D) (hcc : C1 + C2 = D)
    (h2 : R1 = R1' + F) : (R1' + C1) + (R2 + C2) = F := by
  subst h2; revert R1' R2 C1 C2 D F; decide

theorem zmod2_aux2 (R1' R2' C1 C2 D F : ZMod 2) (h1 : R1' + R2' = D) (hcc : C1 + C2 = D) :
    (R1' + F + C1) + (R2' + C2) = F := by
  revert R1' R2' C1 C2 D F; decide

theorem leftPotential_primitive (x0 y0 w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hy0 : ∀ m : Cell, m.2 ≤ y0 → f m = 0)
    (hdeg : ∀ c : Cell, IsPrimal c → x0 < c.1 → c.1 < x0 + w → cdeg f c = 0)
    (m : Cell) (hm1 : x0 < m.1) (hm2 : m.1 ≤ x0 + w) :
    leftPotential x0 y0 f (dualEnds m).1 + leftPotential x0 y0 f (dualEnds m).2 = f m := by
  obtain ⟨a, b⟩ := m
  dsimp only at hm1 hm2
  have hcc := leftCorr_succ x0 y0 f hy0 b
  unfold dualEnds leftPotential
  split_ifs with hpar
  · dsimp only
    have h1 := rowSum_pair' x0 w f hx0 hdeg b a (by omega) (by omega) (by omega)
    have h2 := rowSum_succ x0 f b (a - 1) (by omega)
    rw [show a - 1 + 1 = a by ring] at h2
    exact zmod2_aux1 _ _ _ _ _ _ _ h1 hcc h2
  · dsimp only
    have h1 := rowSum_pair' x0 w f hx0 hdeg b (a - 1) (by omega) (by omega) (by omega)
    have h2 := rowSum_succ x0 f b (a - 1) (by omega)
    rw [show a - 1 + 1 = a by ring] at h2
    rw [h2]
    exact zmod2_aux2 _ _ _ _ _ _ h1 hcc


/-- Full row sums vanish for a cochain that is closed at every primal cell of the strip
`x0 ≤ x ≤ x0 + w` and supported in `x0 < a ≤ x0 + w`, `b > y0`. -/
theorem rowSum_full_zero (x0 y0 w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hxw : ∀ m : Cell, x0 + w < m.1 → f m = 0)
    (hy0 : ∀ m : Cell, m.2 ≤ y0 → f m = 0)
    (hclosed : ∀ c : Cell, IsPrimal c → x0 ≤ c.1 → c.1 ≤ x0 + w → cdeg f c = 0)
    (hw : 0 ≤ w) (j : ℤ) : rowSum x0 f j (x0 + w) = 0 := by
  have hld : ∀ k, leftDefect x0 f k = 0 := by
    intro k; unfold leftDefect; split_ifs with hk
    · exact hclosed _ hk le_rfl (by simpa using hw)
    · rfl
  -- consecutive full row sums agree
  have hpair : ∀ b : ℤ, rowSum x0 f b (x0 + w) + rowSum x0 f (b - 1) (x0 + w) = 0 := by
    intro b
    have hdeg' : ∀ c : Cell, IsPrimal c → x0 < c.1 → c.1 < x0 + (w + 1) → cdeg f c = 0 :=
      fun c hc h1 h2 => hclosed c hc h1.le (by omega)
    by_cases hpar : (x0 + w + b) % 2 = 0
    · have := rowSum_pair' x0 w f hx0 (fun c hc h1 h2 => hclosed c hc h1.le h2.le) b (x0 + w)
        (by omega) le_rfl hpar
      rwa [hld] at this
    · have := rowSum_pair' x0 (w + 1) f hx0 hdeg' b (x0 + w + 1) (by omega) (by omega) (by omega)
      rw [hld, rowSum_succ x0 f b (x0 + w) (by omega), rowSum_succ x0 f (b - 1) (x0 + w) (by omega),
        hxw (x0 + w + 1, b) (by dsimp only; omega), hxw (x0 + w + 1, b - 1) (by dsimp only; omega)]
        at this
      simpa using this
  have two : ∀ z : ZMod 2, z + z = 0 := fun z => by fin_cases z <;> decide
  -- induction upward from the row y0
  have hup : ∀ n : ℕ, rowSum x0 f (y0 + n) (x0 + w) = 0 := by
    intro n
    induction n with
    | zero =>
      unfold rowSum
      apply Finset.sum_eq_zero
      intro a _; exact hy0 _ (by dsimp only; omega)
    | succ n ih =>
      have := hpair (y0 + ((n + 1 : ℕ) : ℤ))
      rw [show y0 + ((n + 1 : ℕ) : ℤ) - 1 = y0 + (n : ℤ) by push_cast; ring, ih, add_zero] at this
      exact this
  by_cases hj : y0 ≤ j
  · have := hup (j - y0).toNat
    rwa [show y0 + ((j - y0).toNat : ℤ) = j by omega] at this
  · unfold rowSum
    apply Finset.sum_eq_zero
    intro a _; exact hy0 _ (by dsimp only; omega)

/-- **Boundary behaviour of the primitive of a globally closed cochain.** -/
theorem leftPotential_zero_of_closed (x0 y0 w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hxw : ∀ m : Cell, x0 + w < m.1 → f m = 0)
    (hy0 : ∀ m : Cell, m.2 ≤ y0 → f m = 0)
    (hclosed : ∀ c : Cell, IsPrimal c → x0 ≤ c.1 → c.1 ≤ x0 + w → cdeg f c = 0)
    (hw : 0 ≤ w) (z : Cell) (hz : z.1 ≤ x0 ∨ x0 + w ≤ z.1) :
    leftPotential x0 y0 f z = 0 := by
  have hld : ∀ k, leftDefect x0 f k = 0 := by
    intro k; unfold leftDefect; split_ifs with hk
    · exact hclosed _ hk le_rfl (by simpa using hw)
    · rfl
  have hcorr : leftCorr x0 y0 f z.2 = 0 := by
    unfold leftCorr; exact Finset.sum_eq_zero (fun k _ => hld k)
  unfold leftPotential
  rw [hcorr, add_zero]
  rcases hz with hz | hz
  · exact rowSum_of_le x0 f _ _ hz
  · have h0 := rowSum_full_zero x0 y0 w f hx0 hxw hy0 hclosed hw z.2
    by_cases hzw : z.1 = x0 + w
    · rw [hzw]; exact h0
    · have : z.1 = x0 + w + (z.1 - (x0 + w)) := by ring
      -- extend by zeros beyond the strip
      unfold rowSum at h0 ⊢
      rw [← h0]
      symm
      apply Finset.sum_subset
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
      · intro a ha hna
        simp only [Finset.mem_Icc] at ha hna
        exact hxw _ (by dsimp only; omega)
end PottsDiscontinuity.TorusCrossing
