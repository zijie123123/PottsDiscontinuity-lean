module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.RayIndex
public import PottsDiscontinuity.FK.BoxExhaustion

/-! Finiteness of the nonzero-index region and the jump across a simple circuit. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK FK.Medial Filter
noncomputable section

lemma rayIndex_left_telescope (v : LatticeVertex) {u w : LatticeVertex}
    (p : squareLattice.Walk u w) (hleft : ∀ x ∈ p.support, v.1 ≤ x.1) :
    rayIndex v p = (if u.2 < v.2 then 1 else 0) - (if w.2 < v.2 then 1 else 0) := by
  induction p with
  | nil => simp [rayIndex]
  | @cons u z w h p ih =>
    have hu := hleft u (by simp)
    have ht : ∀ x ∈ p.support, v.1 ≤ x.1 := by
      intro x hx
      exact hleft x (by simp [hx])
    simp only [rayIndex, rayStep, ite_eq_left hu, mul_one, ih ht]
    omega

lemma rayIndex_zero_of_right (v : LatticeVertex) {u w : LatticeVertex}
    (p : squareLattice.Walk u w) (hright : ∀ x ∈ p.support, x.1 < v.1) :
    rayIndex v p = 0 := by
  induction p with
  | nil => rfl
  | @cons u z w h p ih =>
    have hu := hright u (by simp)
    have ht : ∀ x ∈ p.support, x.1 < v.1 := by
      intro x hx
      exact hright x (by simp [hx])
    simp only [rayIndex, rayStep, ite_eq_right (not_le_of_gt hu), mul_zero, zero_add, ih ht]

lemma rayIndex_zero_of_level (v : LatticeVertex) {u w : LatticeVertex}
    (p : squareLattice.Walk u w) (k : ℤ)
    (hk : ∀ x ∈ p.support, (if x.2 < v.2 then (1 : ℤ) else 0) = k) :
    rayIndex v p = 0 := by
  induction p with
  | nil => rfl
  | @cons u z w h p ih =>
    have hu := hk u (by simp)
    have hz := hk z (by simp)
    have ht : ∀ x ∈ p.support, (if x.2 < v.2 then (1 : ℤ) else 0) = k := by
      intro x hx
      exact hk x (by simp [hx])
    simp only [rayIndex, rayStep, hu, hz, sub_self, zero_mul, zero_add, ih ht]

/-- The nonzero horizontal-ray index has finite support for every finite closed walk. -/
theorem finite_nonzero_rayIndex {z : LatticeVertex} (p : squareLattice.Walk z z) :
    {v | rayIndex v p ≠ 0}.Finite := by
  have hevent (x : LatticeVertex) : ∀ᶠ n : ℕ in atTop, x ∈ latticeBox (0,0) n := by
    obtain ⟨N, hN⟩ := origin_latticeBox_exhaustive x
    exact eventually_atTop.2 ⟨N, fun n hn => latticeBox_mono _ hn hN⟩
  have hh := (eventually_all_finset p.support.toFinset).2 fun x _ => hevent x
  obtain ⟨N, hN⟩ := hh.exists
  have hb (x : LatticeVertex) (hx : x ∈ p.support) :
      -(N : ℤ) ≤ x.1 ∧ x.1 ≤ (N : ℤ) ∧ -(N : ℤ) ≤ x.2 ∧ x.2 ≤ (N : ℤ) := by
    have h := (mem_latticeBox (0,0) x N).1 (hN x (by simpa using hx))
    dsimp at h
    omega
  apply (Finset.finite_toSet (latticeBox (0,0) (N+1))).subset
  intro v hv
  change rayIndex v p ≠ 0 at hv
  rw [Finset.mem_coe, mem_latticeBox]
  dsimp
  by_contra hn
  have hcases : v.1 ≤ -(N : ℤ) ∨ (N : ℤ) < v.1 ∨
      v.2 ≤ -(N : ℤ) ∨ (N : ℤ) < v.2 := by omega
  apply hv
  rcases hcases with hl | hr | hb' | ht
  · rw [rayIndex_left_telescope v p (fun x hx => by have := hb x hx; omega)]
    omega
  · exact rayIndex_zero_of_right v p (fun x hx => by have := hb x hx; omega)
  · apply rayIndex_zero_of_level v p 0
    intro x hx
    have h := hb x hx
    rw [ite_eq_right (by omega)]
  · apply rayIndex_zero_of_level v p 1
    intro x hx
    have h := hb x hx
    rw [ite_eq_left (by omega)]

/-- A nonzero index places the marked vertex in a finite component after only
those primal edges crossing the circuit have been removed. This is discrete separation. -/
theorem finite_avoidance_component_of_rayIndex_ne_zero {z : LatticeVertex}
    (p : squareLattice.Walk z z) (v : LatticeVertex) (hv : rayIndex v p ≠ 0) :
    {w | (circuitAvoidanceGraph p).Reachable v w}.Finite := by
  apply (finite_nonzero_rayIndex p).subset
  intro w hw
  change rayIndex w p ≠ 0
  rw [← rayIndex_eq_of_avoidance_reachable p hw]
  exact hv

/-- A trail crosses its used vertical edge with a nonzero unit jump in the ray index. -/
theorem rayIndex_jump_of_vertical_edge (x y : ℤ) {u w : LatticeVertex}
    (p : squareLattice.Walk u w) (hp : p.IsTrail)
    (he : s((x,y-1),(x,y)) ∈ p.edges) :
    rayIndex (x,y) p ≠ rayIndex (x+1,y) p := by
  induction p with
  | nil => simp at he
  | @cons u z w h p ih =>
    by_cases hhead : s(u,z) = s((x,y-1),(x,y))
    · have htail : s((x,y-1),(x,y)) ∉ p.edges := by
        have hn := (List.nodup_cons.1 (by simpa only [SimpleGraph.Walk.edges_cons] using hp.edges_nodup)).1
        simpa only [hhead] using hn
      have ht := rayIndex_horizontal_invariant x y p htail
      have hxy : y-1 < y := by omega
      have hxx : ¬x+1 ≤ x := by omega
      rcases Sym2.eq_iff.1 hhead with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        simp only [rayIndex, rayStep, ite_eq_left hxy, lt_self_iff_false,
          ite_false, le_refl, ite_true, ite_eq_right hxx, mul_zero, mul_one] <;> omega
    · have ht : s((x,y-1),(x,y)) ∈ p.edges := by
        simpa only [SimpleGraph.Walk.edges_cons, List.mem_cons, Ne.symm hhead, false_or] using he
      have hij := ih hp.of_cons ht
      have hs := rayStep_horizontal_invariant x y u z h hhead
      simp only [rayIndex]
      omega

end
end PottsDiscontinuity.Duality
