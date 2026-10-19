module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.PottsHamiltonian

/-!
# Definition `pottsProb` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

open Classical in
/-- The finite-volume Potts measure `μⁱ_{G,β}[σ] = exp(-β Hⁱ_G(σ)) / ∑_{σ'} exp(-β Hⁱ_G(σ'))`. -/
noncomputable def pottsProb (q : ℕ) (V : Finset (ℤ × ℤ)) (β : ℝ) (i : Fin (q + 1))
    (σ : ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q) : ℝ :=
  Real.exp (-β * pottsHamiltonian q V i σ) /
    ∑ σ' : ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q, Real.exp (-β * pottsHamiltonian q V i σ')

end PottsDiscontinuity
