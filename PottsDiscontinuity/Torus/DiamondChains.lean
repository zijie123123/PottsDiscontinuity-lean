module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import PottsDiscontinuity.Torus.DiamondGraph

/-!
# Indexed primal chains on the torus

The incidence matrix retains each indexed open edge, including parallel edges and
edges with identified endpoints. Its kernel is the actual space of conserved flows.
This is the chain model for the forthcoming winding-based net characterization.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The full indexed open-edge carrier; no quotient by endpoint pairs is taken. -/
abbrev OpenDiamondEdge (A : RCConfig N M) := {v : Fin N × Fin M // A v = true}

theorem card_openDiamondEdge (A : RCConfig N M) :
    Fintype.card (OpenDiamondEdge A) = openCount A := by
  exact Fintype.card_subtype _

/-- Signed incidence: each indexed edge points from endpoint false to endpoint true. -/
def diamondIncidence (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Matrix (FaceVertex N M true) (OpenDiamondEdge A) ℚ :=
  fun u e => (if faceEndpoint hN hM true e.val true = u then 1 else 0) -
    if faceEndpoint hN hM true e.val false = u then 1 else 0

/-- Boundary of an indexed rational one-chain. -/
def diamondBoundary (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    (OpenDiamondEdge A → ℚ) →ₗ[ℚ] (FaceVertex N M true → ℚ) :=
  Matrix.toLin' (diamondIncidence hN hM A)

/-- The potential difference across each open indexed edge. -/
def diamondCoboundary (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    (FaceVertex N M true → ℚ) →ₗ[ℚ] (OpenDiamondEdge A → ℚ) where
  toFun f e := f (faceEndpoint hN hM true e.val true) - f (faceEndpoint hN hM true e.val false)
  map_add' f g := by ext e; simp only [Pi.add_apply]; ring
  map_smul' c f := by ext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem diamondCoboundary_apply (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : FaceVertex N M true → ℚ) (e : OpenDiamondEdge A) :
    diamondCoboundary hN hM A f e =
      f (faceEndpoint hN hM true e.val true) - f (faceEndpoint hN hM true e.val false) := rfl

/-- Conserved indexed flows on the actual open primal subgraph. -/
def diamondCycleSpace (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Submodule ℚ (OpenDiamondEdge A → ℚ) := LinearMap.ker (diamondBoundary hN hM A)

end PottsDiscontinuity.Torus
