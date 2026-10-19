/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleFlowIntegration
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

/-- Zero-exterior dual potentials as an actual linear subspace of all
expanded-face functions. -/
def rectangleExteriorPotentialSubmodule (a : LatticeVertex) (w h : ℕ) :
    Submodule ℝ (RectangleDualVertex a w h → ℝ) where
  carrier := {φ | ∀ z, z.1 ∈ rectangleDualBoundary a w h → φ z = 0}
  zero_mem' := by simp
  add_mem' := by
    intro φ ψ hφ hψ z hz
    simp [hφ z hz, hψ z hz]
  smul_mem' := by
    intro c φ hφ z hz
    simp [hφ z hz]

private def rectanglePotentialAsExterior (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) : RectangleExteriorPotential a w h :=
  ⟨φ.1, φ.2⟩

private theorem rectanglePrimalFlowDivergence_add
    (a : LatticeVertex) (w h : ℕ) (F G : RectanglePrimalBond a w h → ℝ)
    (v : LatticeVertex) :
    rectanglePrimalFlowDivergence a w h (F + G) v =
      rectanglePrimalFlowDivergence a w h F v + rectanglePrimalFlowDivergence a w h G v := by
  classical
  unfold rectanglePrimalFlowDivergence
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hs : b.1.1.source = v <;> simp [hs]; ring

private theorem rectanglePrimalFlowDivergence_smul
    (a : LatticeVertex) (w h : ℕ) (c : ℝ) (F : RectanglePrimalBond a w h → ℝ)
    (v : LatticeVertex) :
    rectanglePrimalFlowDivergence a w h (c • F) v =
      c * rectanglePrimalFlowDivergence a w h F v := by
  classical
  unfold rectanglePrimalFlowDivergence
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑ b : rectangleActualIncidentBonds a w h v,
      if b.1.1.source = v then c * F b.1 else -(c * F b.1)) =
        ∑ b : rectangleActualIncidentBonds a w h v,
          c * (if b.1.1.source = v then F b.1 else -F b.1) := by
            apply Finset.sum_congr rfl
            intro b hb
            by_cases hs : b.1.1.source = v <;> simp [hs]
    _ = c * ∑ b : rectangleActualIncidentBonds a w h v,
          (if b.1.1.source = v then F b.1 else -F b.1) := by
            rw [Finset.mul_sum]

/-- Actual rectangle flows whose incidence divergence vanishes at every
primal rectangle vertex. -/
def rectangleDivergenceFreeFlowSubmodule (a : LatticeVertex) (w h : ℕ) :
    Submodule ℝ (RectanglePrimalBond a w h → ℝ) where
  carrier := {F | ∀ v, v ∈ latticeRectangle a w h →
    rectanglePrimalFlowDivergence a w h F v = 0}
  zero_mem' := by
    intro v hv
    simp [rectanglePrimalFlowDivergence]
  add_mem' := by
    intro F G hF hG v hv
    rw [rectanglePrimalFlowDivergence_add, hF v hv, hG v hv]
    ring
  smul_mem' := by
    intro c F hF v hv
    rw [rectanglePrimalFlowDivergence_smul, hF v hv]
    ring

def rectanglePotentialExtendedLinear (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) (z : LatticeVertex) : ℝ :=
  if hz : z ∈ rectangleDualExpanded a w h then φ.1 ⟨z, hz⟩ else 0

private theorem rectanglePotentialExtendedLinear_add (a : LatticeVertex) (w h : ℕ)
    (φ ψ : rectangleExteriorPotentialSubmodule a w h) (z : LatticeVertex) :
    rectanglePotentialExtendedLinear a w h (φ + ψ) z =
      rectanglePotentialExtendedLinear a w h φ z +
        rectanglePotentialExtendedLinear a w h ψ z := by
  by_cases hz : z ∈ rectangleDualExpanded a w h <;>
    simp [rectanglePotentialExtendedLinear, hz]

private theorem rectanglePotentialExtendedLinear_smul (a : LatticeVertex) (w h : ℕ)
    (c : ℝ) (φ : rectangleExteriorPotentialSubmodule a w h) (z : LatticeVertex) :
    rectanglePotentialExtendedLinear a w h (c • φ) z =
      c * rectanglePotentialExtendedLinear a w h φ z := by
  by_cases hz : z ∈ rectangleDualExpanded a w h <;>
    simp [rectanglePotentialExtendedLinear, hz]

def rectanglePotentialCurlValue (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) (b : LatticeBond) : ℝ :=
  match b.axis with
  | .horizontal => rectanglePotentialExtendedLinear a w h φ (b.faceBase true) -
      rectanglePotentialExtendedLinear a w h φ (b.faceBase false)
  | .vertical => rectanglePotentialExtendedLinear a w h φ (b.faceBase false) -
      rectanglePotentialExtendedLinear a w h φ (b.faceBase true)

private theorem rectanglePotentialCurlValue_eq_flow (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) (b : LatticeBond) :
    rectanglePotentialCurlValue a w h φ b =
      rectangleCurlFlow a w h (rectanglePotentialAsExterior a w h φ) b := by
  cases b.axis <;> rfl

/-- Curl as a linear map from zero-exterior potentials into all actual
rectangle-edge flows. -/
def rectanglePotentialCurlMap (a : LatticeVertex) (w h : ℕ) :
    rectangleExteriorPotentialSubmodule a w h →ₗ[ℝ]
      (RectanglePrimalBond a w h → ℝ) where
  toFun φ b := rectanglePotentialCurlValue a w h φ b.1
  map_add' φ ψ := by
    funext b
    cases hax : b.1.axis
    · simp only [rectanglePotentialCurlValue, hax, Pi.add_apply]
      rw [rectanglePotentialExtendedLinear_add, rectanglePotentialExtendedLinear_add]
      abel
    · simp only [rectanglePotentialCurlValue, hax, Pi.add_apply]
      rw [rectanglePotentialExtendedLinear_add, rectanglePotentialExtendedLinear_add]
      abel
  map_smul' c φ := by
    funext b
    cases hax : b.1.axis
    · simp only [rectanglePotentialCurlValue, hax,
        Pi.smul_apply, smul_eq_mul]
      rw [rectanglePotentialExtendedLinear_smul, rectanglePotentialExtendedLinear_smul]
      simp only [RingHom.id_apply]
      ring
    · simp only [rectanglePotentialCurlValue, hax,
        Pi.smul_apply, smul_eq_mul]
      rw [rectanglePotentialExtendedLinear_smul, rectanglePotentialExtendedLinear_smul]
      simp only [RingHom.id_apply]
      ring

 theorem rectanglePotentialCurlMap_mem_divergenceFree
    (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) :
    rectanglePotentialCurlMap a w h φ ∈ rectangleDivergenceFreeFlowSubmodule a w h := by
  intro v hv
  have hfun : rectanglePotentialCurlMap a w h φ =
      fun b => rectangleCurlFlow a w h (rectanglePotentialAsExterior a w h φ) b.1 := by
    funext b
    exact rectanglePotentialCurlValue_eq_flow a w h φ b.1
  rw [hfun]
  change rectanglePrimalCurlDivergence a w h
      (rectanglePotentialAsExterior a w h φ) v = 0
  exact rectanglePrimalCurlDivergence_eq_zero a w h
    (rectanglePotentialAsExterior a w h φ) v hv

/-- The actual curl map with its mathematically proved divergence-free range. -/
def rectanglePotentialCurlIntoDivergenceFree (a : LatticeVertex) (w h : ℕ) :
    rectangleExteriorPotentialSubmodule a w h →ₗ[ℝ]
      rectangleDivergenceFreeFlowSubmodule a w h where
  toFun φ := ⟨rectanglePotentialCurlMap a w h φ,
    rectanglePotentialCurlMap_mem_divergenceFree a w h φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    exact map_add (rectanglePotentialCurlMap a w h) φ ψ
  map_smul' c φ := by
    apply Subtype.ext
    exact map_smul (rectanglePotentialCurlMap a w h) c φ

private theorem rectanglePotential_bottomFace_boundary
    (a : LatticeVertex) (w h n : ℕ) (hn : n < w) :
    rectangleFlowVertex a (n : ℤ) (-1) ∈ rectangleDualBoundary a w h := by
  simp [rectangleDualBoundary, rectangleDualInterior, rectangleDualExpanded,
    latticeRectangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    rectangleFlowVertex, rectangleFlowX, rectangleFlowY]; omega

private theorem rectangleExtendedPotential_zero_of_boundary
    (a : LatticeVertex) (w h : ℕ) (φ : RectangleExteriorPotential a w h)
    (z : LatticeVertex) (hz : z ∈ rectangleDualBoundary a w h) :
    rectangleExtendedPotential a w h φ z = 0 := by
  rw [rectangleExtendedPotential_of_mem a w h φ z (Finset.mem_filter.mp hz).1]
  exact φ.2 ⟨z, (Finset.mem_filter.mp hz).1⟩ hz

private theorem rectangleExteriorPotential_ext_atInterior
    (a : LatticeVertex) (w h : ℕ)
    (φ ψ : RectangleExteriorPotential a w h)
    (hcurl : ∀ b : RectanglePrimalBond a w h,
      rectangleCurlFlow a w h φ b.1 = rectangleCurlFlow a w h ψ b.1)
    (n m : ℕ) (hn : n < w) (hm : m < h) :
    rectangleExtendedPotential a w h φ (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
      rectangleExtendedPotential a w h ψ (rectangleFlowVertex a (n : ℤ) (m : ℤ)) := by
  have hedgeMem (j : ℕ) (hj : j < h) :
      (⟨rectangleFlowVertex a (n : ℤ) (j : ℤ), .horizontal⟩ : LatticeBond).source ∈
          latticeRectangle a w h ∧
        (⟨rectangleFlowVertex a (n : ℤ) (j : ℤ), .horizontal⟩ : LatticeBond).target ∈
          latticeRectangle a w h := by
    constructor <;> rw [mem_latticeRectangle] <;>
      simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY,
        LatticeBond.source, LatticeBond.target] <;> omega
  have hrow (j : ℕ) (hj : j < h) :
      rectangleExtendedPotential a w h φ (rectangleFlowVertex a (n : ℤ) (j : ℤ)) =
        rectangleExtendedPotential a w h ψ (rectangleFlowVertex a (n : ℤ) (j : ℤ)) := by
    induction j with
    | zero =>
        have hc := hcurl ⟨⟨rectangleFlowVertex a (n : ℤ) (0 : ℤ), .horizontal⟩,
          hedgeMem 0 hj⟩
        simp [rectangleCurlFlow, LatticeBond.faceBase, rectangleFlowVertex,
          rectangleFlowX, rectangleFlowY] at hc
        have hface : (a.1 + (n : ℤ), a.2 - 1) =
            rectangleFlowVertex a (n : ℤ) (-1) := by
          ext <;> simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]; ring
        have hbd := rectanglePotential_bottomFace_boundary a w h n hn
        have hbd' : (a.1 + (n : ℤ), a.2 - 1) ∈ rectangleDualBoundary a w h := by
          rw [hface]
          exact hbd
        have hφbot := rectangleExtendedPotential_zero_of_boundary a w h φ _ hbd'
        have hψbot := rectangleExtendedPotential_zero_of_boundary a w h ψ _ hbd'
        rw [hφbot, hψbot] at hc
        simpa [rectangleFlowVertex, rectangleFlowX, rectangleFlowY] using hc
    | succ j ih =>
        have hc := hcurl ⟨⟨rectangleFlowVertex a (n : ℤ) (j.succ : ℤ), .horizontal⟩,
          hedgeMem j.succ hj⟩
        simp [rectangleCurlFlow, LatticeBond.faceBase, rectangleFlowVertex,
          rectangleFlowX, rectangleFlowY] at hc
        have htop : (a.1 + (n : ℤ), a.2 + ((j : ℤ) + 1)) =
            rectangleFlowVertex a (n : ℤ) (j.succ : ℤ) := by
          ext <;> simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
        have hbottom : (a.1 + (n : ℤ), a.2 + ((j : ℤ) + 1) - 1) =
            rectangleFlowVertex a (n : ℤ) (j : ℤ) := by
          ext <;> simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]; omega
        rw [htop, hbottom] at hc
        have hprev := ih (by omega)
        rw [hprev] at hc
        linarith
  exact hrow m hm

private theorem rectangleExteriorPotential_ext_of_curl_eq
    (a : LatticeVertex) (w h : ℕ)
    (φ ψ : RectangleExteriorPotential a w h)
    (hcurl : ∀ b : RectanglePrimalBond a w h,
      rectangleCurlFlow a w h φ b.1 = rectangleCurlFlow a w h ψ b.1) :
    φ = ψ := by
  apply Subtype.ext
  funext z
  by_cases hI : z.1 ∈ rectangleDualInterior a w h
  · have hprop := (Finset.mem_filter.mp hI).2
    let n : ℕ := (z.1.1 - a.1).toNat
    let m : ℕ := (z.1.2 - a.2).toNat
    have hxn : 0 ≤ z.1.1 - a.1 := by omega
    have hym : 0 ≤ z.1.2 - a.2 := by omega
    have hx : z.1.1 = a.1 + (n : ℤ) := by
      dsimp [n]
      rw [Int.toNat_of_nonneg hxn]
      omega
    have hy : z.1.2 = a.2 + (m : ℤ) := by
      dsimp [m]
      rw [Int.toNat_of_nonneg hym]
      omega
    have hn : n < w := by omega
    have hm : m < h := by omega
    have hcoords : z.1 = rectangleFlowVertex a (n : ℤ) (m : ℤ) := by
      ext <;> simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY, hx, hy]
    have hp := rectangleExteriorPotential_ext_atInterior a w h φ ψ hcurl n m hn hm
    have hex : z.1 ∈ rectangleDualExpanded a w h := (Finset.mem_filter.mp hI).1
    have hexV : rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ rectangleDualExpanded a w h := by
      simpa [hcoords] using hex
    have hsub : z = ⟨rectangleFlowVertex a (n : ℤ) (m : ℤ), hexV⟩ := by
      apply Subtype.ext
      exact hcoords
    rw [rectangleExtendedPotential_of_mem a w h φ _ hexV,
      rectangleExtendedPotential_of_mem a w h ψ _ hexV] at hp
    rw [hsub]
    exact hp
  · have hb : z.1 ∈ rectangleDualBoundary a w h := by
      apply Finset.mem_filter.mpr
      refine ⟨z.2, ?_⟩
      exact hI
    rw [φ.2 z hb, ψ.2 z hb]

/-- Curl determines a zero-exterior potential uniquely by row-wise recurrence
from the lower wired boundary. -/
theorem rectanglePotentialCurlMap_injective (a : LatticeVertex) (w h : ℕ) :
    Function.Injective (rectanglePotentialCurlMap a w h) := by
  intro φ ψ hφψ
  have heq := rectangleExteriorPotential_ext_of_curl_eq a w h
    (rectanglePotentialAsExterior a w h φ) (rectanglePotentialAsExterior a w h ψ) (by
      intro b
      have hb := congrFun hφψ b
      change rectanglePotentialCurlValue a w h φ b.1 =
        rectanglePotentialCurlValue a w h ψ b.1 at hb
      rw [rectanglePotentialCurlValue_eq_flow, rectanglePotentialCurlValue_eq_flow] at hb
      exact hb)
  apply Subtype.ext
  exact congrArg Subtype.val heq

 theorem rectanglePotentialCurlInto_injective
    (a : LatticeVertex) (w h : ℕ) :
    Function.Injective (rectanglePotentialCurlIntoDivergenceFree a w h) := by
  intro φ ψ hφψ
  apply rectanglePotentialCurlMap_injective a w h
  exact congrArg Subtype.val hφψ

 theorem rectanglePotentialCurlInto_surjective
    (a : LatticeVertex) (w h : ℕ) :
    Function.Surjective (rectanglePotentialCurlIntoDivergenceFree a w h) := by
  intro F
  let actualF : RectangleDivergenceFreeFlow a w h := ⟨F.1, F.2⟩
  let extPot := rectangleFlowExteriorPotential a w h actualF
  let φ : rectangleExteriorPotentialSubmodule a w h := ⟨extPot.1, extPot.2⟩
  refine ⟨φ, ?_⟩
  apply Subtype.ext
  funext b
  calc
    rectanglePotentialCurlMap a w h φ b =
        rectangleCurlFlow a w h (rectanglePotentialAsExterior a w h φ) b.1 := by
          exact rectanglePotentialCurlValue_eq_flow a w h φ b.1
    _ = F.1 b := by
      simpa [actualF, extPot, φ, rectanglePotentialAsExterior] using
        rectangleFlowExteriorPotential_curl_eq_flow a w h actualF b

/-- The finite discrete-curl map is a genuine linear equivalence between
zero-exterior dual potentials and divergence-free flows on actual rectangle
edges. -/
noncomputable def rectanglePotentialCurlLinearEquiv (a : LatticeVertex) (w h : ℕ) :
    rectangleExteriorPotentialSubmodule a w h ≃ₗ[ℝ]
      rectangleDivergenceFreeFlowSubmodule a w h :=
  LinearEquiv.ofBijective (rectanglePotentialCurlIntoDivergenceFree a w h)
    ⟨rectanglePotentialCurlInto_injective a w h,
      rectanglePotentialCurlInto_surjective a w h⟩

end PottsDiscontinuity.FK
