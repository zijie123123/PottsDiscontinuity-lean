module

public import PottsDiscontinuity.Torus.DiamondCycleRank
public import PottsDiscontinuity.Torus.RibbonChainComplex
public import PottsDiscontinuity.Torus.RibbonHandleBound

/-!
# Homology of the capped ribbon subgraph

Take conserved indexed flows modulo the actual capped face boundaries. Its dimension
is twice the independently counted attachment handles. This makes the cellular genus
content explicit while keeping the comparison with torus winding classes separate.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

open Module

variable {N M : ℕ}

/-- Capped face boundaries, with the proved zero divergence recorded in the codomain. -/
def ribbonFaceCycleBoundary (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    (RibbonBoundaryComponent hN hM A → ℚ) →ₗ[ℚ] diamondCycleSpace hN hM A :=
  (ribbonFaceBoundary hN hM A).codRestrict (diamondCycleSpace hN hM A)
    (ribbonFaceBoundary_mem_cycleSpace hN hM A)

/-- The actual cellular boundary subspace inside conserved flows. -/
def ribbonBoundarySpace (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Submodule ℚ (diamondCycleSpace hN hM A) :=
  LinearMap.range (ribbonFaceCycleBoundary hN hM A)

/-- First rational homology after capping each boundary component by a disc. -/
abbrev CappedRibbonHomology (hN : Even N) (hM : Even M) (A : RCConfig N M) :=
  (diamondCycleSpace hN hM A) ⧸ ribbonBoundarySpace hN hM A

theorem finrank_ribbonBoundarySpace (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    finrank ℚ (ribbonBoundarySpace hN hM A) =
      finrank ℚ (LinearMap.range (ribbonFaceBoundary hN hM A)) := by
  have hm : (ribbonBoundarySpace hN hM A).map (diamondCycleSpace hN hM A).subtype =
      LinearMap.range (ribbonFaceBoundary hN hM A) := by
    rw [ribbonBoundarySpace, ← LinearMap.range_comp]
    rfl
  rw [← Submodule.finrank_map_subtype_eq (diamondCycleSpace hN hM A)
    (ribbonBoundarySpace hN hM A), hm]

/-- Cellular Euler homology: the first capped Betti number is twice the handle count. -/
theorem finrank_cappedRibbonHomology (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    finrank ℚ (CappedRibbonHomology hN hM A) = 2 * ribbonHandleCount hN hM A := by
  have hq := (ribbonBoundarySpace hN hM A).finrank_quotient_add_finrank
  have hb := finrank_range_ribbonFaceBoundary hN hM A
  have hc := finrank_diamondCycleSpace hN hM A
  have he := euler_ribbonHandleCount hN hM A
  rw [finrank_ribbonBoundarySpace] at hq
  change finrank ℚ (CappedRibbonHomology hN hM A) +
    finrank ℚ (LinearMap.range (ribbonFaceBoundary hN hM A)) =
      finrank ℚ (diamondCycleSpace hN hM A) at hq
  omega

theorem finrank_cappedRibbonHomology_open (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) :
    finrank ℚ (CappedRibbonHomology hN hM (openRCConfig N M)) = 2 := by
  rw [finrank_cappedRibbonHomology, ribbonHandleCount_open hN hM hNp hMp]

end PottsDiscontinuity.Torus
