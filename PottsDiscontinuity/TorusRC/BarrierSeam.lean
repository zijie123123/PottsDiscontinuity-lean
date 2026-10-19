module

public import PottsDiscontinuity.TorusRC.CylinderEvents
public import PottsDiscontinuity.TorusTopology.LiftedEdgeCover

/-! # The seam edges fixed by the source barrier event -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength TorusTopology

variable {N M : ℕ}

/-- The zigzag immediately below the horizontal seam, at horizontal coordinate
`k`. Its edge from `k` to `k+1` has indexed row zero. -/
def seamZigzagSite (k : ℕ) : RotatedVertex :=
  ⟨((k : ℤ), -((k % 2 : ℕ) : ℤ)), by
    refine ⟨((k / 2 : ℕ) : ℤ), ?_⟩
    omega⟩

theorem seamZigzagSite_adj (k : ℕ) :
    rotatedLattice.Adj (seamZigzagSite k) (seamZigzagSite (k + 1)) := by
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with hk | hk <;>
    norm_num [rotatedLattice, seamZigzagSite, Nat.add_mod, hk]

theorem seamZigzagSite_index (hN : 0 < N) (hM : 0 < M) (k : ℕ)
    (hk : k + 1 < N) :
    liftedEdgeIndex hN hM (seamZigzagSite k) (seamZigzagSite (k + 1)) =
      (⟨k + 1, hk⟩, ⟨0, hM⟩) := by
  have hx : max (k : ℤ) ((k + 1 : ℕ) : ℤ) = (k + 1 : ℕ) :=
    max_eq_right (by omega)
  have hy : max (-((k % 2 : ℕ) : ℤ)) (-(((k + 1) % 2 : ℕ) : ℤ)) = 0 := by
    have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk2 with hk2 | hk2 <;> norm_num [Nat.add_mod, hk2]
  change (periodicCoordinate hN (max (k : ℤ) ((k + 1 : ℕ) : ℤ)),
    periodicCoordinate hM (max (-((k % 2 : ℕ) : ℤ)) (-(((k + 1) % 2 : ℕ) : ℤ)))) = _
  rw [hx, hy]
  exact Prod.ext (periodicCoordinate_nat hN ⟨k + 1, hk⟩)
    (periodicCoordinate_nat hM ⟨0, hM⟩)

/-- If all seam edges with indices `1,...,K` are open, they themselves give
an open crossing of the lifted annular strip. -/
theorem leftStripCrossing_of_seamOpen (hN : 0 < N) (hM : 0 < M)
    (A : RCConfig N M) (n : ℕ) (hn : 3 * n < N)
    (hopen : ∀ i : Fin N, 1 ≤ i.val → i.val ≤ 3 * n →
      A (i, ⟨0, hM⟩) = true) :
    torusRCLeftStripCrossing hN hM A n := by
  have hreach (t : ℕ) (ht : t ≤ 3 * n) :
      (liftedStripGraph hN hM A 0 (3 * n : ℕ)).Reachable
        (seamZigzagSite 0) (seamZigzagSite t) := by
    induction t with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ t ih =>
        have htN : t + 1 < N := by omega
        apply (ih (by omega)).trans
        apply SimpleGraph.Adj.reachable
        refine ⟨seamZigzagSite_adj t, ?_, ?_, ?_⟩
        · rw [seamZigzagSite_index hN hM t htN]
          exact hopen ⟨t + 1, htN⟩ (by simp) ht
        · change 0 ≤ (t : ℤ) ∧ (t : ℤ) ≤ ((3 * n : ℕ) : ℤ)
          constructor <;> omega
        · change 0 ≤ ((t + 1 : ℕ) : ℤ) ∧
            ((t + 1 : ℕ) : ℤ) ≤ ((3 * n : ℕ) : ℤ)
          constructor <;> omega
  exact ⟨seamZigzagSite 0, seamZigzagSite (3 * n), rfl, rfl, hreach _ le_rfl⟩

/-- The unique closed seam edge of B lies strictly inside its left strip.
In particular, every right-half seam edge is open under B. -/
theorem barrier_closed_seam_edge_range (hN : 0 < N) (hM : 0 < M)
    (A : RCConfig N M) (n : ℕ) (hn : 3 * n < N)
    (hB : A ∈ torusRCBarrier hN hM n) :
    ∃ i₀ : Fin N, 1 ≤ i₀.val ∧ i₀.val ≤ 3 * n ∧
      A (i₀, ⟨0, hM⟩) = false ∧
      ∀ i : Fin N, i ≠ i₀ → A (i, ⟨0, hM⟩) = true := by
  obtain ⟨i₀, hclosed, hopen⟩ := hB.2
  have hrange : 1 ≤ i₀.val ∧ i₀.val ≤ 3 * n := by
    by_contra h
    apply hB.1
    apply leftStripCrossing_of_seamOpen hN hM A n hn
    intro i hi1 hin
    apply hopen i
    intro heq
    subst i
    exact h ⟨hi1, hin⟩
  exact ⟨i₀, hrange.1, hrange.2, hclosed, hopen⟩

theorem barrier_seam_open_outside_left_strip (hN : 0 < N) (hM : 0 < M)
    (A : RCConfig N M) (n : ℕ) (hn : 3 * n < N)
    (hB : A ∈ torusRCBarrier hN hM n) (i : Fin N)
    (hi : i.val = 0 ∨ 3 * n < i.val) : A (i, ⟨0, hM⟩) = true := by
  obtain ⟨i₀, hi1, hin, _, hopen⟩ := barrier_closed_seam_edge_range hN hM A n hn hB
  apply hopen i
  intro heq
  subst i
  omega

end PottsDiscontinuity.TorusRC
