/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.WiredPotentialSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

namespace PottsDiscontinuity.FK

variable {V : Type*} [Fintype V] (G : SimpleGraph V)
  (ξ : BoundaryCondition V) (A : Configuration G) (v₀ : V)

/-- Evaluation of a componentwise potential at the chosen base vertex. -/
def componentPotentialEvaluation :
    componentConstantFunctions G ξ A →ₗ[ℝ] ℝ where
  toFun f := f.1 v₀
  map_add' _f _g := rfl
  map_smul' _c _f := rfl

/-- Potentials normalized to vanish at `v₀`. -/
def normalizedComponentPotentials :
    Submodule ℝ (componentConstantFunctions G ξ A) :=
  LinearMap.ker (componentPotentialEvaluation G ξ A v₀)

omit [Fintype V] in
theorem componentPotentialEvaluation_surjective :
    Function.Surjective (componentPotentialEvaluation G ξ A v₀) := by
  intro c
  refine ⟨⟨fun _ => c, ?_⟩, rfl⟩
  intro u v h
  rfl

omit [Fintype V] in
theorem componentPotentialEvaluation_range_eq_top :
    LinearMap.range (componentPotentialEvaluation G ξ A v₀) = ⊤ :=
  LinearMap.range_eq_top.mpr (componentPotentialEvaluation_surjective G ξ A v₀)

omit [Fintype V] in
theorem normalizedComponentPotentials_finrank_add_one [Finite V] :
    Module.finrank ℝ (normalizedComponentPotentials G ξ A v₀) + 1 =
      componentCount G ξ A := by
  classical
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (componentPotentialEvaluation G ξ A v₀)
  rw [componentPotentialEvaluation_range_eq_top] at hrank
  rw [finrank_top, Module.finrank_self ℝ] at hrank
  rw [componentConstantFunctions_finrank] at hrank
  change Module.finrank ℝ (LinearMap.ker (componentPotentialEvaluation G ξ A v₀)) + 1 =
    componentCount G ξ A
  calc
    Module.finrank ℝ (LinearMap.ker (componentPotentialEvaluation G ξ A v₀)) + 1 =
        1 + Module.finrank ℝ (LinearMap.ker (componentPotentialEvaluation G ξ A v₀)) :=
      Nat.add_comm _ _
    _ = componentCount G ξ A := hrank

end PottsDiscontinuity.FK
