module

public import PottsDiscontinuity.TorusRC.ColumnZigzag
public import PottsDiscontinuity.TorusRC.LiftedEvent

/-! # Completing the localized chain with bounded seam collars -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- Open vertical-zigzag edges in the bottom and top collars of width L. -/
def columnCollarOpen (hNp : 0 < N) (hMp : 0 < M) (x : ℤ) (L : ℕ)
    (A : RCConfig N M) : Prop :=
  ∀ k, k < M → k < L ∨ M - L ≤ k →
    A (periodicCoordinate hNp (x + 1), periodicCoordinate hMp (k + 1)) = true

theorem columnZigzagSite_chain (x : ℤ) (hx : Even x) (n j : ℕ) :
    columnZigzagSite x hx (2 * n * j) = liftedChainSite x hx n j := by
  have ht : Even (2 * n * j) := ⟨n * j, by ring⟩
  rw [columnZigzagSite_even x hx _ ht]
  apply Subtype.ext
  dsimp [liftedChainSite, liftedColumnSite]

/-- Only boxes meeting the horizontal seam require forced zigzags. Their
required edges lie in collars of width R+2n, independently of the height M. -/
theorem liftedCPrime_of_interior_and_collar (hNp : 0 < N) (hMp : 0 < M)
    (a b x : ℤ) (hx : Even x) (hMeven : Even M) (n R : ℕ)
    (hn : 0 < n) (hR : 2 * n ≤ R) (ha : a ≤ x) (hb : x + 1 ≤ b)
    (A : RCConfig N M) (hcollar : columnCollarOpen hNp hMp x (R + 2 * n) A)
    (hinterior : ∀ j < M / (2 * n),
      R < 2 * n * j → 2 * n * j + R < M →
      liftedBoxConnection hNp hMp A a b R
        (liftedChainSite x hx n j) (liftedChainSite x hx n (j + 1))) :
    A ∈ liftedCPrime hNp hMp a b x hx hMeven n R := by
  have hR1 : 1 ≤ R := by omega
  have hdiv : 2 * n * (M / (2 * n)) ≤ M := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self M (2 * n)
  have hmod := Nat.mod_lt M (show 0 < 2 * n by omega)
  have hdecomp := Nat.mod_add_div M (2 * n)
  have hterminal : M - 2 * n * (M / (2 * n)) ≤ R := by omega
  change (∀ j < M / (2 * n), _) ∧ _
  constructor
  · intro j hj
    by_cases hbottom : R < 2 * n * j
    · by_cases htop : 2 * n * j + R < M
      · exact hinterior j hj hbottom htop
      · have ht : 2 * n * (j + 1) ≤ M :=
          (Nat.mul_le_mul_left (2 * n) (Nat.succ_le_of_lt hj)).trans hdiv
        have hconn := columnZigzag_box_connection hNp hMp A a b x hx
          (2 * n * j) (2 * n * (j + 1)) R (Nat.mul_le_mul_left _ (Nat.le_succ j))
          (by simpa [Nat.mul_add, Nat.mul_one] using hR) hR1 ha hb
          (fun k hsk hkt => hcollar k (by omega) (Or.inr (by omega)))
        rwa [columnZigzagSite_chain, columnZigzagSite_chain] at hconn
    · have ht : 2 * n * (j + 1) ≤ M :=
        (Nat.mul_le_mul_left (2 * n) (Nat.succ_le_of_lt hj)).trans hdiv
      have hconn := columnZigzag_box_connection hNp hMp A a b x hx
        (2 * n * j) (2 * n * (j + 1)) R (Nat.mul_le_mul_left _ (Nat.le_succ j))
        (by simpa [Nat.mul_add, Nat.mul_one] using hR) hR1 ha hb
        (fun k hsk hkt => hcollar k (by omega) (Or.inl (by
          have heq : 2 * n * (j + 1) = 2 * n * j + 2 * n := by ring
          omega)))
      rwa [columnZigzagSite_chain, columnZigzagSite_chain] at hconn
  · have hconn := columnZigzag_box_connection hNp hMp A a b x hx
      (2 * n * (M / (2 * n))) M R hdiv hterminal hR1 ha hb
      (fun k hsk hkt => hcollar k hkt (Or.inr (by omega)))
    rw [columnZigzagSite_chain, columnZigzagSite_even x hx M hMeven] at hconn
    exact hconn

end PottsDiscontinuity.TorusRC
