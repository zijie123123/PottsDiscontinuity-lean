module

public import PottsDiscontinuity.TorusRC.LiftedPaths

/-! # Explicit vertical zigzags in the lifted right half -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- A nearest-neighbor zigzag in the two columns x and x+1. -/
def columnZigzagSite (x : ℤ) (hx : Even x) (t : ℕ) : RotatedVertex :=
  ⟨(x + (t % 2 : ℕ), t), by
    obtain ⟨k, hk⟩ := hx
    refine ⟨k + ((t + 1) / 2 : ℕ), ?_⟩
    omega⟩

theorem columnZigzagSite_adj (x : ℤ) (hx : Even x) (t : ℕ) :
    rotatedLattice.Adj (columnZigzagSite x hx t) (columnZigzagSite x hx (t + 1)) := by
  have ht : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases ht with ht | ht <;>
    norm_num [rotatedLattice, columnZigzagSite, Nat.add_mod, ht]

theorem columnZigzagSite_even (x : ℤ) (hx : Even x) (t : ℕ) (ht : Even t) :
    columnZigzagSite x hx t = liftedColumnSite x t hx (by exact_mod_cast ht) := by
  apply Subtype.ext
  have ht0 : t % 2 = 0 := Nat.even_iff.mp ht
  simp [columnZigzagSite, liftedColumnSite, ht0]

theorem columnZigzagSite_index (hNp : 0 < N) (hMp : 0 < M)
    (x : ℤ) (hx : Even x) (t : ℕ) :
    liftedEdgeIndex hNp hMp (columnZigzagSite x hx t)
      (columnZigzagSite x hx (t + 1)) =
      (periodicCoordinate hNp (x + 1), periodicCoordinate hMp (t + 1)) := by
  have hxmax : max (x + (t % 2 : ℕ)) (x + ((t + 1) % 2 : ℕ)) = x + 1 := by
    have ht : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases ht with ht | ht <;> simp [Nat.add_mod, ht]
  change (periodicCoordinate hNp (max (x + (t % 2 : ℕ))
    (x + ((t + 1) % 2 : ℕ))), periodicCoordinate hMp (max (t : ℤ) (t + 1 : ℕ))) = _
  rw [hxmax, max_eq_right (by omega)]
  rfl

/-- Every finite portion of an open zigzag gives a localized lifted path.
The endpoint is allowed to be the top seam lift at height M. -/
theorem columnZigzag_box_connection (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b x : ℤ) (hx : Even x) (s t R : ℕ)
    (hst : s ≤ t) (hR : t - s ≤ R) (hR1 : 1 ≤ R)
    (ha : a ≤ x) (hb : x + 1 ≤ b)
    (hopen : ∀ k, s ≤ k → k < t →
      A (periodicCoordinate hNp (x + 1), periodicCoordinate hMp (k + 1)) = true) :
    liftedBoxConnection hNp hMp A a b R
      (columnZigzagSite x hx s) (columnZigzagSite x hx t) := by
  have hwalk (d : ℕ) (hd : s + d ≤ t) :
      ∃ w : (liftedStripGraph hNp hMp A a b).Walk
          (columnZigzagSite x hx s) (columnZigzagSite x hx (s + d)),
        ∀ z ∈ w.support, inLiftedBox R (columnZigzagSite x hx s) z := by
    induction d with
    | zero =>
      refine ⟨.nil, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      simp [inLiftedBox]
    | succ d ih =>
      obtain ⟨w, hw⟩ := ih (by omega)
      have hadj : (liftedStripGraph hNp hMp A a b).Adj
          (columnZigzagSite x hx (s + d)) (columnZigzagSite x hx (s + (d + 1))) := by
        refine ⟨columnZigzagSite_adj x hx (s + d), ?_, ?_, ?_⟩
        · rw [← Nat.add_assoc, columnZigzagSite_index]
          exact hopen (s + d) (by omega) (by omega)
        · dsimp [columnZigzagSite]
          constructor <;> omega
        · dsimp [columnZigzagSite]
          constructor <;> omega
      refine ⟨w.append (.cons hadj .nil), ?_⟩
      intro z hz
      rw [SimpleGraph.Walk.support_append] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hw z hz
      · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.tail_cons, List.mem_singleton] at hz
        subst z
        dsimp [inLiftedBox, columnZigzagSite]
        constructor <;> apply abs_le.mpr <;> constructor <;> omega
  have hw := hwalk (t - s) (by omega)
  rw [Nat.add_sub_of_le hst] at hw
  exact hw

end PottsDiscontinuity.TorusRC
