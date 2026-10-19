module

public import PottsDiscontinuity.Bethe.Theorem23Derivative

/-! # Local analytic Bethe branches at regular solutions -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem discreteCoordinateResidual_zero_iff {Δ : ℝ} {N n : ℕ} (hN : 0 < N)
    (q : Fin (n / 2) → ℝ) :
    discreteCoordinateResidual Δ N n q = 0 ↔
      DiscreteBetheEquation Δ N n (discreteSymLift n q) := by
  have hsym := discreteSymLift_mem n q
  have hres : discreteBetheResidual Δ N n (discreteSymLift n q) ∈ R_n_sym n :=
    (R_n_sym n).sub_mem hsym (discreteBetheMap_mem_R_n_sym Δ N n _ hsym)
  constructor
  · intro h
    have heq : discreteBetheResidual Δ N n (discreteSymLift n q) = 0 := by
      apply discreteSym_ext hres (R_n_sym n).zero_mem
      intro i
      exact congrFun h i
    apply (discreteBetheMap_fixed_iff_equation hN _).1
    have hzero : discreteSymLift n q - discreteBetheMap Δ N n (discreteSymLift n q) = 0 := heq
    exact (sub_eq_zero.mp hzero).symm
  · intro h
    have heq := (discreteBetheMap_fixed_iff_equation hN _).2 h
    funext i
    change discreteSymLift n q (discreteHalfIndex n i) -
      discreteBetheMap Δ N n (discreteSymLift n q) (discreteHalfIndex n i) = 0
    rw [heq, sub_self]

end PottsDiscontinuity.Bethe
