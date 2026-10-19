module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.TorusExploration.CylinderProduct

/-! Union over actual bottom and top endpoints of distinct cylinder crossings. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus FK CorrLength MeasureTheory
variable {N M : ℕ}
noncomputable section
open scoped Classical
local instance cylinderUnionEdgeDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullCylinderGraph hN hM).edgeSet := Classical.decEq _
local instance cylinderUnionVertexDecidableEq : DecidableEq (FaceVertex N M true) := Classical.decEq _

abbrev BottomVertex (N M : ℕ) := {v : FaceVertex N M true // v.val.2.val=0}
abbrev TopVertex (N M : ℕ) := {v : FaceVertex N M true // v.val.2.val+1=M}

lemma card_bottomVertex_le : Fintype.card (BottomVertex N M) ≤ N := by
  suffices h : Fintype.card (BottomVertex N M) ≤ Fintype.card (Fin N) by simpa using h
  apply Fintype.card_le_of_injective (fun v : BottomVertex N M => v.val.val.1)
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext h
  apply Fin.ext
  exact u.property.trans v.property.symm

lemma card_topVertex_le : Fintype.card (TopVertex N M) ≤ N := by
  suffices h : Fintype.card (TopVertex N M) ≤ Fintype.card (Fin N) by simpa using h
  apply Fintype.card_le_of_injective (fun v : TopVertex N M => v.val.val.1)
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext h
  apply Fin.ext
  have hu := u.property
  have hv := v.property
  omega

/-- Periodic continuation of a finite list, with no distinguished default vertex. -/
def periodicEndpoints {V : Type*} {r : ℕ} (hr : 0 < r) (x : Fin r → V) : ℕ → V :=
  fun n => x ⟨n%r,Nat.mod_lt n hr⟩

/-- The choices include both endpoints; allowing all top endpoints gives a
rigorous upper union bound without the informal fixed-endpoint equality in (af). -/
def cylinderEndpointEvent (hN : Even N) (hM : Even M) (r : ℕ) (hr : 0 < r)
    (z : (Fin r → BottomVertex N M) × (Fin r → TopVertex N M)) :
    Set (Configuration (fullCylinderGraph hN hM)) :=
  distinctConnections (fullCylinderGraph hN hM)
    (fun n => (periodicEndpoints hr z.1 n).val)
    (fun n => (periodicEndpoints hr z.2 n).val) r

lemma cylinderCrossings_subset_endpoint_union (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (r : ℕ) (hr : 0 < r) :
    {C | TorusRC.torusRCSeamClosedCylinderCrossings hN hM r
      (cylinderIndexedConfiguration hN hM hN4 hM4 C)} ⊆
      ⋃ z, cylinderEndpointEvent hN hM r hr z := by
  intro C hC
  obtain ⟨x,hx,hy,hd⟩ := hC
  choose y hyTop hyConn using hy
  let z : (Fin r → BottomVertex N M) × (Fin r → TopVertex N M) :=
    (fun i => ⟨x i,hx i⟩,fun i => ⟨y i,hyTop i⟩)
  apply Set.mem_iUnion.2 ⟨z,?_⟩
  have hg := openGraph_cylinderIndexedConfiguration hN hM hN4 hM4 C
  rw [cylinderIndexedConfiguration_eq_seamClosed] at hg
  constructor
  · intro i hi
    have hc := hyConn ⟨i,hi⟩
    rw [← hg] at hc
    simpa only [FK.ActualConnected,z,periodicEndpoints,Nat.mod_eq_of_lt hi,Subtype.coe_mk] using hc
  · intro i hi k hk hik hc
    apply hd ⟨i,hi⟩ ⟨k,hk⟩ (fun h => hik (congrArg Fin.val h))
    rw [← hg]
    simpa only [FK.ActualConnected,z,periodicEndpoints,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hk,Subtype.coe_mk] using hc

/-- Union bound over at most N^(2r) bottom/top endpoint choices. -/
theorem cylinderCrossings_probability_le (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (r : ℕ) (hr : 1 ≤ r) :
    (measure (fullCylinderGraph hN hM) θ (BoundaryCondition.free ∅)
      {C | TorusRC.torusRCSeamClosedCylinderCrossings hN hM r
        (cylinderIndexedConfiguration hN hM hN4 hM4 C)}).toReal ≤
      (N : ℝ)^(2*r) *
        (Real.sqrt (μ.real (CorrLength.connectionEvent (0,0) (diagonalSite (2*(M-1))))))^(r-1) := by
  let G := fullCylinderGraph hN hM
  let : Fintype G.edgeSet := Fintype.ofFinite _
  let ν := measure G θ (BoundaryCondition.free ∅)
  let Z := (Fin r → BottomVertex N M) × (Fin r → TopVertex N M)
  let c := Real.sqrt (μ.real (CorrLength.connectionEvent (0,0) (diagonalSite (2*(M-1)))))
  have hcard : Fintype.card Z ≤ N^(2*r) := by
    simp only [Z,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
    calc
      _ ≤ N^r*N^r := Nat.mul_le_mul
        (Nat.pow_le_pow_left card_bottomVertex_le r) (Nat.pow_le_pow_left card_topVertex_le r)
      _ = _ := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ ν.real (⋃ z : Z, cylinderEndpointEvent hN hM r (by omega) z) :=
      measureReal_mono (cylinderCrossings_subset_endpoint_union hN hM hN4 hM4 r (by omega))
    _ ≤ ∑ z : Z, ν.real (cylinderEndpointEvent hN hM r (by omega) z) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _z : Z, c^(r-1) := by
      apply Finset.sum_le_sum
      intro z _
      exact cylinder_distinctConnections_le hN hM hN4 hM4 θ μ hμ
        (fun n => (periodicEndpoints (by omega) z.1 n).val)
        (fun n => (periodicEndpoints (by omega) z.2 n).val)
        (fun n => (periodicEndpoints (by omega) z.1 n).property)
        (fun n => (periodicEndpoints (by omega) z.2 n).property) r hr
    _ = (Fintype.card Z : ℝ)*c^(r-1) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

end
end PottsDiscontinuity.TorusExploration
