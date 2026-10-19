module

public import PottsDiscontinuity.TorusRC.LiftedPaths
public import PottsDiscontinuity.TorusRC.Measure

/-! # Rectangle crossing event and the crossing estimate (3.19) contract -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open CorrLength Torus

variable {N M : ℕ}

/-- A bottom-to-top primal crossing of the lifted rectangle
`[0,3n] × [0,n]`. The horizontal strip graph forces every edge of the path
to remain in the rectangle's horizontal span; the walk-support condition
imposes the two vertical sides. -/
def torusRCVerticalRectangleCrossing (hN : 0 < N) (hM : 0 < M)
    (n : ℕ) (A : RCConfig N M) : Prop :=
  ∃ u v : RotatedVertex,
    u.val.2 = 0 ∧ v.val.2 = (n : ℤ) ∧
      ∃ w : (liftedStripGraph hN hM A 0 (3 * (n : ℤ))).Walk u v,
        ∀ z ∈ w.support, 0 ≤ z.val.2 ∧ z.val.2 ≤ (n : ℤ)

/-- Exact named premise for source equation (3.19): a uniformly positive
probability of a bottom-to-top crossing of `[0,3n] × [0,n]`, for even torus
periods large enough that the finite graph is simple. -/
def h319 (q : Set.Ici (1 : ℝ)) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (N M n : ℕ) (hN : Even N) (hM : Even M),
      (hN4 : 4 ≤ N) → (hM4 : 4 ≤ M) → (hn : 0 < n) →
        (h3nN : 3 * n ≤ N) → (h3nM : 3 * n ≤ M) →
          let hNpos : 0 < N := by omega
          let hMpos : 0 < M := by omega
          c ≤ torusRCProbability hN hM q
            {A | torusRCVerticalRectangleCrossing hNpos hMpos n A}

end PottsDiscontinuity.TorusRC
