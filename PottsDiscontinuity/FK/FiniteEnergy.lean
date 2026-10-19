/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Generalized open bounds: p/(p+(1-p)q) and p; closed bounds: 1-p and 1-p/(p+(1-p)q). -/
module

public import PottsDiscontinuity.FK.SingleEdgeLaw
public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.FK.WiredRemoval
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsDiscontinuity.FK

open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance finiteEnergyEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
local instance finiteEnergyEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance finiteEnergyRemainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _
local instance finiteEnergyRemovedFintype (R : Configuration G) :
    Fintype (RemovedConfiguration G R) := Fintype.ofFinite _

def edgeRemovedBoolEquiv (e : G.edgeSet) :
    RemovedConfiguration G ({e} : Configuration G) ≃ Bool where
  toFun B := decide (e ∈ B.val)
  invFun b := if b then ⟨{e}, by simp⟩ else ⟨∅, by simp⟩
  left_inv B := by
    apply Subtype.ext
    by_cases he : e ∈ B.val
    · have hB : B.val = {e} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨he, fun x hx => by simpa using B.property hx⟩
      simp [hB]
    · have hB : B.val = ∅ := by
        rcases Finset.subset_singleton_iff.mp B.property with hEmpty | hSingle
        · exact hEmpty
        · exact (he (by simp [hSingle])).elim
      simp [hB]
  right_inv b := by cases b <;> simp

def configurationEdgeStateEquiv (e : G.edgeSet) :
    Configuration G ≃ RemainingConfiguration G ({e} : Configuration G) × Bool :=
  (configurationSplitEquiv G ({e} : Configuration G)).trans
    (Equiv.prodCongr (Equiv.refl _) (edgeRemovedBoolEquiv e))

omit [Finite V] in
@[simp] private theorem configurationEdgeStateEquiv_symm_apply_false (e : G.edgeSet)
    (A : RemainingConfiguration G ({e} : Configuration G)) :
    (configurationEdgeStateEquiv e).symm (A, false) = A.val := by
  simp [configurationEdgeStateEquiv, configurationSplitEquiv_symm_apply,
    edgeRemovedBoolEquiv]

omit [Finite V] in
@[simp] private theorem configurationEdgeStateEquiv_symm_apply_true (e : G.edgeSet)
    (A : RemainingConfiguration G ({e} : Configuration G)) :
    (configurationEdgeStateEquiv e).symm (A, true) = insert e A.val := by
  simp [configurationEdgeStateEquiv, configurationSplitEquiv_symm_apply,
    edgeRemovedBoolEquiv]

private theorem configurationProbability_edgeState_sum (q : Parameters)
    (ξ : BoundaryCondition V) (e : G.edgeSet) (f : Configuration G → ℝ) :
    (∑ C : Configuration G, configurationProbability G q ξ C * f C) =
      ∑ A : RemainingConfiguration G ({e} : Configuration G),
        (configurationProbability G q ξ A.val * f A.val +
          configurationProbability G q ξ (insert e A.val) * f (insert e A.val)) := by
  classical
  rw [← (configurationEdgeStateEquiv e).symm.sum_comp, Fintype.sum_prod_type]
  simp only [configurationEdgeStateEquiv_symm_apply_false,
    configurationEdgeStateEquiv_symm_apply_true, Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro A hA
  ring

/-- For an event invariant under toggling one original edge, its open-edge mass
lies between the FK single-edge conditional weights times its total mass. -/
theorem configurationProbability_edge_finite_energy
    (q : Parameters) (ξ : BoundaryCondition V) (s : Set (Configuration G))
    {u v : V} (huv : G.Adj u v)
    (hstable : ∀ A, A ∈ s ↔ A.erase ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ ∈ s) :
    (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) * (measure G q ξ s).toReal ≤
        (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ A})).toReal ∧
      (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ A})).toReal ≤
        edgeParameter q * (measure G q ξ s).toReal := by
  classical
  let e : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr huv⟩
  let P : Configuration G → ℝ := configurationProbability G q ξ
  let eventIndicator (t : Set (Configuration G)) : Configuration G → ℝ :=
    t.indicator (fun _ => (1 : ℝ))
  have habsent (A : RemainingConfiguration G {e}) : e ∉ A.val := by
    intro heA
    exact (Finset.disjoint_left.mp A.property heA) (by simp)
  have hstableInsert (A : RemainingConfiguration G {e}) :
      insert e A.val ∈ s ↔ A.val ∈ s := by
    have hh := hstable (insert e A.val)
    simpa [e, habsent A] using hh
  have hbaseIndicator (A : RemainingConfiguration G {e}) :
      eventIndicator s A.val = if A.val ∈ s then 1 else 0 := by
    simp [eventIndicator, Set.indicator]
  have hinsertIndicator (A : RemainingConfiguration G {e}) :
      eventIndicator s (insert e A.val) = if A.val ∈ s then 1 else 0 := by
    simp [eventIndicator, Set.indicator, hstableInsert A]
  have hmass : (measure G q ξ s).toReal =
      ∑ A : RemainingConfiguration G {e},
        if A.val ∈ s then P A.val + P (insert e A.val) else 0 := by
    rw [measure_toReal_eq_indicator_sum]
    rw [configurationProbability_edgeState_sum q ξ e (eventIndicator s)]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hsA : A.val ∈ s <;> simp [P, eventIndicator, hstableInsert, hsA]
  have hopen :
      (measure G q ξ (s ∩ {A | e ∈ A})).toReal =
        ∑ A : RemainingConfiguration G {e},
          if A.val ∈ s then P (insert e A.val) else 0 := by
    rw [measure_toReal_eq_indicator_sum]
    rw [configurationProbability_edgeState_sum q ξ e (eventIndicator (s ∩ {A | e ∈ A}))]
    simp [P, eventIndicator, Set.indicator, habsent, hstableInsert]
  have htermLower (A : RemainingConfiguration G {e}) :
      (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) *
          (if A.val ∈ s then P A.val + P (insert e A.val) else 0) ≤
        (if A.val ∈ s then P (insert e A.val) else 0) := by
    by_cases hA : A.val ∈ s
    · simp only [ite_eq_left hA]
      have hr := configurationProbability_pair_ratio_bounds q ξ A.val huv
        (by simpa [e] using habsent A)
      have hden : 0 < P A.val + P (insert e A.val) := by
        exact add_pos (configurationProbability_pos G q ξ A.val)
          (configurationProbability_pos G q ξ (insert e A.val))
      have h := (le_div_iff₀ hden).mp hr.1
      simpa [P] using h
    · simp [hA]
  have htermUpper (A : RemainingConfiguration G {e}) :
      (if A.val ∈ s then P (insert e A.val) else 0) ≤
        edgeParameter q *
          (if A.val ∈ s then P A.val + P (insert e A.val) else 0) := by
    by_cases hA : A.val ∈ s
    · simp only [ite_eq_left hA]
      have hr := configurationProbability_pair_ratio_bounds q ξ A.val huv
        (by simpa [e] using habsent A)
      have hden : 0 < P A.val + P (insert e A.val) := by
        exact add_pos (configurationProbability_pos G q ξ A.val)
          (configurationProbability_pos G q ξ (insert e A.val))
      have h := (div_le_iff₀ hden).mp hr.2
      simpa [P] using h
    · simp [hA]
  constructor
  · rw [hmass, hopen]
    calc
      (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) *
          (∑ A : RemainingConfiguration G {e},
            if A.val ∈ s then P A.val + P (insert e A.val) else 0) =
        ∑ A : RemainingConfiguration G {e},
          (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) *
            (if A.val ∈ s then P A.val + P (insert e A.val) else 0) := by
              rw [Finset.mul_sum]
      _ ≤ ∑ A : RemainingConfiguration G {e},
          (if A.val ∈ s then P (insert e A.val) else 0) :=
        Finset.sum_le_sum (fun A _ => htermLower A)
  · rw [hmass, hopen]
    calc
      (∑ A : RemainingConfiguration G {e},
          (if A.val ∈ s then P (insert e A.val) else 0) ) ≤
        ∑ A : RemainingConfiguration G {e},
          edgeParameter q *
            (if A.val ∈ s then P A.val + P (insert e A.val) else 0) :=
        Finset.sum_le_sum (fun A _ => htermUpper A)
      _ = edgeParameter q *
          (∑ A : RemainingConfiguration G {e},
            if A.val ∈ s then P A.val + P (insert e A.val) else 0) := by
              rw [Finset.mul_sum]


/-- For an event invariant under toggling one original edge, its closed-edge mass
lies between the FK single-edge conditional weights times its total mass. -/
theorem configurationProbability_edge_finite_energy_closed
    (q : Parameters) (ξ : BoundaryCondition V) (s : Set (Configuration G))
    {u v : V} (huv : G.Adj u v)
    (hstable : ∀ A, A ∈ s ↔ A.erase ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ ∈ s) :
    (1 - edgeParameter q) * (measure G q ξ s).toReal ≤
        (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A})).toReal ∧
      (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A})).toReal ≤
        (1 - (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val))) * (measure G q ξ s).toReal := by
  classical
  let e : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr huv⟩
  let opened : Set (Configuration G) := {A | e ∈ A}
  have hopen := configurationProbability_edge_finite_energy q ξ s huv hstable
  have hpartition :
      (measure G q ξ (s ∩ opened)).toReal +
        (measure G q ξ (s ∩ {A | e ∉ A})).toReal =
          (measure G q ξ s).toReal := by
    have h := MeasureTheory.measureReal_inter_add_sdiff (μ := measure G q ξ) (s := s)
      (t := opened) (by simp [opened])
    have hset : s \ opened = s ∩ {A | e ∉ A} := by
      ext A
      simp [opened]
    change ((measure G q ξ (s ∩ opened)).toReal) +
      ((measure G q ξ (s ∩ {A | e ∉ A})).toReal) =
        ((measure G q ξ s).toReal)
    rw [← hset]
    exact h
  have hopen' :
      (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) * (measure G q ξ s).toReal ≤
        (measure G q ξ (s ∩ opened)).toReal ∧
      (measure G q ξ (s ∩ opened)).toReal ≤
        edgeParameter q * (measure G q ξ s).toReal := by
    simpa [e, opened] using hopen
  constructor <;> nlinarith [hpartition, hopen'.1, hopen'.2]

end
end PottsDiscontinuity.FK
