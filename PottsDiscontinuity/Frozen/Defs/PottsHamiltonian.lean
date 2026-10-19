module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.VertexBoundary

/-!
# Definition `pottsHamiltonian` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

open Classical in
/-- The Potts Hamiltonian `Hⁱ_G(σ) = -∑_{{x,y} ∈ E} 1[σₓ = σ_y] - ∑_{x ∈ ∂V} 1[σₓ = i]`
on the subgraph induced by `V`, spins in `{1, …, q}`, boundary condition `i ∈ {0, …, q}`. -/
noncomputable def pottsHamiltonian (q : ℕ) (V : Finset (ℤ × ℤ)) (i : Fin (q + 1))
    (σ : ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q) : ℝ :=
  -(∑ e : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet,
      if ∀ x ∈ e.1, ∀ y ∈ e.1, σ x = σ y then (1 : ℝ) else 0) -
    ∑ x : ↥(V : Set (ℤ × ℤ)),
      if x.1 ∈ vertexBoundary V ∧ (σ x : ℕ) = (i : ℕ) then (1 : ℝ) else 0

end PottsDiscontinuity
