module

public import PottsDiscontinuity.Torus.Darts

/-!
# A canonical orientation of every smoothed loop

On an even medial torus the checkerboard arrow field has alternating types 5 and 6.
Both turning pairings are compatible at every vertex. It therefore gives a canonical
orientation and an actual cyclic-orbit carrier for the loops of every smoothing.
This does not impose any turning-number or homology condition on those loops.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Checkerboard colour of a medial vertex. -/
def checker (v : Fin N × Fin M) : Bool := decide ((v.1.val + v.2.val) % 2 = 0)

private theorem nxt_mod_two (hN : Even N) (i : Fin N) :
    (nxt i).val % 2 = 1 - i.val % 2 := by
  have hn : N % 2 = 0 := by rcases hN with ⟨k, hk⟩; omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Fin.pos i).ne'
  rw [nxt, coe_finRotate]
  split_ifs with hi
  · subst i
    simp only [Fin.val_last]
    omega
  · omega

theorem checker_nxt_x (hN : Even N) (i : Fin N) (j : Fin M) :
    checker (nxt i, j) = !checker (i, j) := by
  have hn := nxt_mod_two hN i
  by_cases ha : ((nxt i).val + j.val) % 2 = 0
  · have hb : (i.val + j.val) % 2 ≠ 0 := by omega
    simp only [checker, ha, hb, decide_true, decide_false, Bool.not_false]
  · have hb : (i.val + j.val) % 2 = 0 := by omega
    simp only [checker, ha, hb, decide_true, decide_false, Bool.not_true]

theorem checker_nxt_y (hM : Even M) (i : Fin N) (j : Fin M) :
    checker (i, nxt j) = !checker (i, j) := by
  have hm := nxt_mod_two hM j
  by_cases ha : (i.val + (nxt j).val) % 2 = 0
  · have hb : (i.val + j.val) % 2 ≠ 0 := by omega
    simp only [checker, ha, hb, decide_true, decide_false, Bool.not_false]
  · have hb : (i.val + j.val) % 2 = 0 := by omega
    simp only [checker, ha, hb, decide_true, decide_false, Bool.not_true]

theorem checker_prv_x (hN : Even N) (i : Fin N) (j : Fin M) :
    checker (prv i, j) = !checker (i, j) := by
  have h := checker_nxt_x hN (prv i) j
  simp only [nxt, prv, Equiv.apply_symm_apply] at h
  rw [h, Bool.not_not]

theorem checker_prv_y (hM : Even M) (i : Fin N) (j : Fin M) :
    checker (i, prv j) = !checker (i, j) := by
  have h := checker_nxt_y hM i (prv j)
  simp only [nxt, prv, Equiv.apply_symm_apply] at h
  rw [h, Bool.not_not]

/-- Orient each edge with its black checkerboard face on the same side. -/
def checkerArrows (N M : ℕ) : ArrowConfig N M where
  horiz v := checker v
  vert v := !checker v

/-- Both pairings are compatible with the canonical checkerboard orientation. -/
theorem checkerArrows_compatible (hN : Even N) (hM : Even M) (s : Smoothing N M) :
    CompatibleConfig (checkerArrows N M) s := by
  rintro ⟨i, j⟩
  change Compatible (s (i, j)) (checker (prv i, j)) (checker (i, j))
    (!checker (i, prv j)) (!checker (i, j))
  rw [checker_prv_x hN, checker_prv_y hM, Bool.not_not]
  cases s (i, j) <;> cases checker (i, j) <;> decide

/-- The canonically oriented loops of a smoothing, as cyclic classes of directed darts. -/
abbrev Loop (hN : Even N) (hM : Even M) (s : Smoothing N M) :=
  DirectedLoop (checkerArrows N M) s (checkerArrows_compatible hN hM s)

/-- Number of smoothed loops, with one canonical orientation per loop. -/
noncomputable def loopCount (hN : Even N) (hM : Even M) (s : Smoothing N M) : ℕ :=
  Fintype.card (Loop hN hM s)

end PottsDiscontinuity.Torus
