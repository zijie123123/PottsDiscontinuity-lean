/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import PottsDiscontinuity.Duality.RectangleDualPotential
public import PottsDiscontinuity.Duality.RectangleOpenFlow

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

def rectangleConfigurationOfCarrier (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Configuration (rectangleGraph a w h) := by
  change Finset (rectangleGraph a w h).edgeSet
  exact A

def rectangleCarrierOfConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    Finset (rectanglePrimalEdgeCarrier a w h) := by
  change Finset (rectangleGraph a w h).edgeSet
  exact A

abbrev rectangleOpenDivSpace (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :=
  @Min.min (Submodule ℝ (RectanglePrimalFlow a w h)) inferInstance
    (rectangleOpenFlowSubmodule a w h (rectangleConfigurationOfCarrier a w h A))
    (rectangleDivergenceFreeFlowSubmodule a w h)

def rectanglePrimalBondSubtype (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) : RectanglePrimalBond a w h :=
  ⟨rectanglePrimalEdgeBond a w h e,
    rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩

 theorem rectangleDualCurlKernel_openSupport
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (φ : rectangleDualPotentialCurlKernel a w h A)
    (b : RectanglePrimalBond a w h)
    (hb : rectanglePrimalBondToEdge a w h b ∉ A) :
    rectanglePotentialCurlMap a w h φ.1 b = 0 := by
  let e := rectanglePrimalBondToEdge a w h b
  have heq : rectanglePrimalEdgeBondEquiv a w h e = b := by
    exact (rectanglePrimalEdgeBondEquiv a w h).right_inv b
  have hzero := φ.2 e (by simpa [e] using hb)
  change rectanglePotentialCurlMap a w h φ.1
    (rectanglePrimalBondSubtype a w h e) = 0 at hzero
  have hbond : rectanglePrimalBondSubtype a w h e =
      rectanglePrimalEdgeBondEquiv a w h e := by
    apply Subtype.ext
    rfl
  have hvalue : rectanglePotentialCurlMap a w h φ.1
      (rectanglePrimalBondSubtype a w h e) =
      rectanglePotentialCurlMap a w h φ.1 b := by
    rw [hbond, heq]
  rw [hvalue] at hzero
  exact hzero

 theorem rectangleOpenFlow_mem_curlKernel
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (F : rectangleOpenDivSpace a w h A) :
    (rectanglePotentialCurlLinearEquiv a w h).symm
      ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩ ∈
      rectangleDualPotentialCurlKernel a w h A := by
  intro e he
  have hclosed : rectanglePrimalBondToEdge a w h
      ((rectanglePrimalEdgeBondEquiv a w h) e) ∉ A := by
    have hedge : rectanglePrimalBondToEdge a w h
      ((rectanglePrimalEdgeBondEquiv a w h) e) = e :=
      (rectanglePrimalEdgeBondEquiv a w h).left_inv e
    rw [hedge]
    exact he
  have hzero := (Submodule.mem_inf.mp F.2).1
    ((rectanglePrimalEdgeBondEquiv a w h) e) hclosed
  have hF : rectanglePotentialCurlMap a w h
      ((rectanglePotentialCurlLinearEquiv a w h).symm
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩) = F.1 := by
    have hh := congrArg Subtype.val
      ((rectanglePotentialCurlLinearEquiv a w h).apply_symm_apply
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩)
    change rectanglePotentialCurlMap a w h
      ((rectanglePotentialCurlLinearEquiv a w h).symm
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩) = F.1 at hh
    exact hh
  have hFedge := congrFun hF (rectanglePrimalEdgeBondEquiv a w h e)
  have hbond : rectanglePrimalBondSubtype a w h e =
      rectanglePrimalEdgeBondEquiv a w h e := by
    apply Subtype.ext
    rfl
  change rectanglePotentialCurlMap a w h
    ((rectanglePotentialCurlLinearEquiv a w h).symm
      ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩)
    (rectanglePrimalBondSubtype a w h e) = 0
  rw [hbond, hFedge]
  exact hzero

def rectangleDualCurlKernelToOpenIntersection
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    rectangleDualPotentialCurlKernel a w h A →ₗ[ℝ]
      rectangleOpenDivSpace a w h A where
  toFun φ := by
    refine ⟨(rectanglePotentialCurlLinearEquiv a w h φ.1).1, ?_⟩
    apply Submodule.mem_inf.mpr
    constructor
    · intro b hb
      exact rectangleDualCurlKernel_openSupport a w h A φ b hb
    · exact (rectanglePotentialCurlLinearEquiv a w h φ.1).2
  map_add' φ ψ := by
    apply Subtype.ext
    change (rectanglePotentialCurlLinearEquiv a w h (φ.1 + ψ.1)).1 =
      (rectanglePotentialCurlLinearEquiv a w h φ.1).1 +
        (rectanglePotentialCurlLinearEquiv a w h ψ.1).1
    exact congrArg Subtype.val
      (map_add (rectanglePotentialCurlLinearEquiv a w h).toLinearMap φ.1 ψ.1)
  map_smul' c φ := by
    apply Subtype.ext
    change (rectanglePotentialCurlLinearEquiv a w h (c • φ.1)).1 =
      c • (rectanglePotentialCurlLinearEquiv a w h φ.1).1
    exact congrArg Subtype.val
      (map_smul (rectanglePotentialCurlLinearEquiv a w h).toLinearMap c φ.1)

def rectangleOpenIntersectionToDualCurlKernel
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    (rectangleOpenDivSpace a w h A) →ₗ[ℝ]
      rectangleDualPotentialCurlKernel a w h A where
  toFun F := by
    let d : rectangleDivergenceFreeFlowSubmodule a w h :=
      ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩
    refine ⟨(rectanglePotentialCurlLinearEquiv a w h).symm d, ?_⟩
    exact rectangleOpenFlow_mem_curlKernel a w h A F
  map_add' F G := by
    apply Subtype.ext
    change (rectanglePotentialCurlLinearEquiv a w h).symm
        ⟨F.1 + G.1, ?_⟩ =
      (rectanglePotentialCurlLinearEquiv a w h).symm
          ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩ +
        (rectanglePotentialCurlLinearEquiv a w h).symm
          ⟨G.1, (Submodule.mem_inf.mp G.2).2⟩
    · exact map_add ((rectanglePotentialCurlLinearEquiv a w h).symm).toLinearMap
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩
        ⟨G.1, (Submodule.mem_inf.mp G.2).2⟩
  map_smul' c F := by
    apply Subtype.ext
    change (rectanglePotentialCurlLinearEquiv a w h).symm
        ⟨c • F.1, ?_⟩ =
      c • (rectanglePotentialCurlLinearEquiv a w h).symm
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩
    · exact map_smul ((rectanglePotentialCurlLinearEquiv a w h).symm).toLinearMap c
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩

 theorem rectangleDualCurlKernelOpenEquiv_bijective
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Function.Bijective (rectangleDualCurlKernelToOpenIntersection a w h A) := by
  constructor
  · intro φ ψ hxy
    have hflow := congrArg Subtype.val hxy
    apply Subtype.ext
    apply (rectanglePotentialCurlLinearEquiv a w h).injective
    apply Subtype.ext
    exact hflow
  · intro F
    refine ⟨rectangleOpenIntersectionToDualCurlKernel a w h A F, ?_⟩
    apply Subtype.ext
    have hval := congrArg Subtype.val
      ((rectanglePotentialCurlLinearEquiv a w h).apply_symm_apply
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩)
    exact hval

noncomputable def rectangleDualCurlKernelOpenLinearEquiv
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    rectangleDualPotentialCurlKernel a w h A ≃ₗ[ℝ]
      rectangleOpenDivSpace a w h A :=
  LinearEquiv.ofBijective (rectangleDualCurlKernelToOpenIntersection a w h A)
    (rectangleDualCurlKernelOpenEquiv_bijective a w h A)

noncomputable def rectangleDualPotentialCurlKernelSignedKernelEquiv
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    rectangleDualPotentialCurlKernel a w h A ≃ₗ[ℝ]
      LinearMap.ker (signedDivergence (rectangleGraph a w h)
        (rectangleConfigurationOfCarrier a w h A)
        (rectangleOpenEdgeOrientation a w h (rectangleConfigurationOfCarrier a w h A))) :=
  (rectangleDualCurlKernelOpenLinearEquiv a w h A).trans
    (rectangleOpenFlowDivergenceKernelEquiv a w h (rectangleConfigurationOfCarrier a w h A)).symm

private theorem rectangleDualComponentCount_eq_potentialFinrank_add_one
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    componentCount (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h)
      (rectangleDualConfiguration a w h A) =
      Module.finrank ℝ (rectangleDualPotentialCurlKernel a w h A) + 1 := by
  exact (rectangleDualPotentialCurlKernel_finrank_add_one a w h A).symm

 theorem rectangleEuler_additive (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    componentCount (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h A) +
        Fintype.card (RectangleVertex a w h) =
      A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h)))
          (rectangleConfigurationOfCarrier a w h A) + 1 := by
  have hdim := rectangleSignedFlowDimension a w h (rectangleConfigurationOfCarrier a w h A)
  have heq := (rectangleDualPotentialCurlKernelSignedKernelEquiv a w h A).finrank_eq
  have hpot := rectangleDualComponentCount_eq_potentialFinrank_add_one a w h A
  calc
    componentCount (rectangleDualGraph a w h) (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h A) + Fintype.card (RectangleVertex a w h) =
        (Module.finrank ℝ (rectangleDualPotentialCurlKernel a w h A) + 1) +
          Fintype.card (RectangleVertex a w h) := by rw [hpot]
    _ = Module.finrank ℝ (LinearMap.ker
        (signedDivergence (rectangleGraph a w h)
          (rectangleConfigurationOfCarrier a w h A)
          (rectangleOpenEdgeOrientation a w h (rectangleConfigurationOfCarrier a w h A)))) +
          Fintype.card (RectangleVertex a w h) + 1 := by rw [heq]; ring
    _ = A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h)))
          (rectangleConfigurationOfCarrier a w h A) + 1 := by
      rw [hdim]
      rfl

theorem rectangleEuler_additive_config (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    componentCount (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h (rectangleCarrierOfConfiguration a w h A)) +
        Fintype.card (RectangleVertex a w h) =
      A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A + 1 := by
  have hEuler := rectangleEuler_additive a w h (rectangleCarrierOfConfiguration a w h A)
  have hc : (rectangleCarrierOfConfiguration a w h A).card = A.card := rfl
  calc
    _ = (rectangleCarrierOfConfiguration a w h A).card +
        componentCount (rectangleGraph a w h)
          (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A + 1 := hEuler
    _ = A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A + 1 := by rw [hc]

 theorem rectangleEuler_additive_card_config (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    componentCount (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h (rectangleCarrierOfConfiguration a w h A)) +
        (w + 1) * (h + 1) =
      A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A + 1 := by
  rw [← card_rectangleVertex a w h]
  exact rectangleEuler_additive_config a w h A

end
end PottsDiscontinuity.FK
