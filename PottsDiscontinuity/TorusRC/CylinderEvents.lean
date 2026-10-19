module

public import PottsDiscontinuity.Torus.LoopStatistics
public import PottsDiscontinuity.TorusRC.LiftedEvent

/-! # Barrier and seam-closed cylinder events for Lemma 3.15 -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- A left-to-right primal crossing of the lifted strip with horizontal
coordinates in `[0,3n]`. The vertical coordinate is unrestricted, so this is
the annular crossing used in the source event B. -/
def torusRCLeftStripCrossing (hN : 0 < N) (hM : 0 < M)
    (A : RCConfig N M) (n : ℕ) : Prop :=
  ∃ u v : RotatedVertex,
    u.val.1 = 0 ∧ v.val.1 = ((3 * n : ℕ) : ℤ) ∧
      (liftedStripGraph hN hM A 0 ((3 * n : ℕ) : ℤ)).Reachable u v

/-- Every indexed primal edge crossing the seam row is open, except for one. -/
def torusRCSeamAllButOneOpen (hM : 0 < M)
    (A : RCConfig N M) : Prop :=
  ∃ i₀ : Fin N,
    A (i₀, (⟨0, hM⟩ : Fin M)) = false ∧
      ∀ i : Fin N, i ≠ i₀ → A (i, (⟨0, hM⟩ : Fin M)) = true

/-- Source event B: no primal crossing of the left annular strip, and all but
one of the indexed primal seam edges are open. The absence of the crossing is
equivalent, by annular crossing duality, to the dual winding barrier used by
the topological implication. -/
def torusRCBarrier (hN : 0 < N) (hM : 0 < M) (n : ℕ) : Set (RCConfig N M) :=
  {A | ¬ torusRCLeftStripCrossing hN hM A n ∧ torusRCSeamAllButOneOpen hM A}

/-- Closing all indexed edges in the seam row cuts the vertical torus into a
cylinder with distinct bottom and top rows. -/
def torusRCSeamClosed (A : RCConfig N M) : RCConfig N M :=
  fun e => if e.2.val = 0 then false else A e

@[simp] theorem torusRCSeamClosed_seam (hM : 0 < M) (A : RCConfig N M)
    (i : Fin N) : torusRCSeamClosed A (i, (⟨0, hM⟩ : Fin M)) = false := by
  simp [torusRCSeamClosed]

@[simp] theorem torusRCSeamClosed_away (A : RCConfig N M)
    (i : Fin N) (j : Fin M) (hj : j.val ≠ 0) :
    torusRCSeamClosed A (i, j) = A (i, j) := by
  simp [torusRCSeamClosed, hj]

/-- The clean cylinder crossing event used by T3: there are `r` different
open primal clusters of the seam-closed configuration, each joining row zero
to the top row. The vertices are existential, so the event handles every
horizontal location and both checkerboard parities. -/
def torusRCSeamClosedCylinderCrossings (hN : Even N) (hM : Even M)
    (r : ℕ) (A : RCConfig N M) : Prop :=
  ∃ x : Fin r → FaceVertex N M true,
    (∀ i, (x i).val.2.val = 0) ∧
      (∀ i, ∃ y : FaceVertex N M true,
        y.val.2.val + 1 = M ∧
          (diamondOpenGraph hN hM true A).Reachable (x i) y) ∧
      ∀ i j, i ≠ j →
        ¬ (diamondOpenGraph hN hM true A).Reachable (x i) (x j)

/-- Exact topological premise T2. It is discharged by `TorusTopology.hBCU_proved`
in `TorusTopology/BarrierEvent.lean`.
The event B is `torusRCBarrier`, and C prime is `torusCPrime`. -/
def hBCU (hN : Even N) (hM : Even M) (hNpos : 0 < N) (hMpos : 0 < M)
    (hNdiv : 8 ∣ N) (n : ℕ) : Prop :=
  8 * n ≤ N → N / 2 < M →
    ∀ A : RCConfig N M,
      A ∈ torusRCBarrier hNpos hMpos n →
      A ∈ torusCPrime hNpos hMpos hNdiv hM n →
      rcVerticalWinding hN hM ⟨0, hMpos⟩ A = 1

/-- Exact topological premise T3. It states that `U ≥ r` forces `r` distinct
bottom-to-top clusters after the seam row is closed. -/
def hUr (hN : Even N) (hM : Even M) (hMpos : 0 < M) (r : ℕ) : Prop :=
  ∀ A : RCConfig N M,
    r ≤ rcVerticalWinding hN hM ⟨0, hMpos⟩ A →
      torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed A)

end PottsDiscontinuity.TorusRC
