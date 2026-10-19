/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
The normalization helper is adapted from the same source.
Extended from the self-dual parameter to independent interior p and all q >= 1. -/
module

public import Mathlib.Data.Int.Interval
public import PottsDiscontinuity.Duality.Parameters
public import PottsDiscontinuity.Duality.RectangleDualConfiguration
public import PottsDiscontinuity.Duality.RectangleEuler
public import PottsDiscontinuity.FK.ProbabilityProduct

@[expose] public section

namespace PottsDiscontinuity.FK.FiniteProbability

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

omit [Nonempty α] in
lemma partition_mul_left (c : ℝ) (w : α → ℝ) :
    partition (fun a => c * w a) = c * partition w := by
  simp [partition, Finset.mul_sum]

lemma pmf_map_equiv_of_common_factor (e : α ≃ β) (c : ℝ)
    (w : α → ℝ) (v : β → ℝ)
    (hc : 0 < c) (hw : ∀ a, 0 < w a) (hv : ∀ b, 0 < v b)
    (h : ∀ a, w a = c * v (e a)) :
    (pmf w hw).map e = pmf v hv := by
  have hpart : partition w = c * partition v := by
    calc
      partition w = partition (fun a => c * v (e a)) := by
        congr 1
        funext a
        exact h a
      _ = c * partition (fun a => v (e a)) := partition_mul_left c _
      _ = c * partition v := by rw [partition_equiv e v]
  ext b
  rw [map_equiv_apply, pmf_apply, pmf_apply]
  rw [h (e.symm b), e.apply_symm_apply, hpart]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hpv : partition v ≠ 0 := (partition_pos v hv).ne'
  congr 1
  field_simp [hcne, hpv]

end PottsDiscontinuity.FK.FiniteProbability

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.Duality

noncomputable section

local instance rectanglePrimalConfigurationEdgeFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectangleGraph a w h).edgeSet := Fintype.ofFinite _

local instance rectangleDualConfigurationEdgeFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectangleDualGraph a w h).edgeSet := Fintype.ofFinite _

def rectangleCarrierConfigurationEquiv (a : LatticeVertex) (w h : ℕ) :
    Configuration (rectangleGraph a w h) ≃
      Finset (rectanglePrimalEdgeCarrier a w h) where
  toFun A := by
    change Finset (rectangleGraph a w h).edgeSet
    exact A
  invFun A := by
    change Finset (rectangleGraph a w h).edgeSet
    exact A
  left_inv A := rfl
  right_inv A := rfl

/-- The actual finite configuration bijection: primal open edges map to the
complementary open dual edges, with wired dual boundary condition. -/
noncomputable def rectanglePrimalDualConfigurationEquiv (a : LatticeVertex)
    (w h : ℕ) : Configuration (rectangleGraph a w h) ≃
      Configuration (rectangleDualGraph a w h) :=
  (rectangleCarrierConfigurationEquiv a w h).trans
    (rectangleDualConfigurationEquiv a w h)

@[simp] theorem rectanglePrimalDualConfigurationEquiv_apply (a : LatticeVertex)
    (w h : ℕ) (A : Configuration (rectangleGraph a w h)) :
    rectanglePrimalDualConfigurationEquiv a w h A =
      rectangleDualConfiguration a w h
        (rectangleCarrierConfigurationEquiv a w h A) := by
  simp [rectanglePrimalDualConfigurationEquiv]

/-- Exact state characterization, independent of the internal carrier equivalence. -/
@[simp] theorem mem_rectanglePrimalDualConfigurationEquiv (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualGraphEdgeEquiv a w h e ∈ rectanglePrimalDualConfigurationEquiv a w h A ↔
      e.primalEdge ∉ A := by
  simp only [rectanglePrimalDualConfigurationEquiv_apply, mem_rectangleDualConfiguration]
  rfl

/-- The configuration-independent ratio of primal-free and dual-wired weights. -/
def rectangleDualityFactor (θ : Parameters) (a : LatticeVertex) (w h : ℕ) : ℝ :=
  (edgeParameter θ + θ.val * (1 - edgeParameter θ)) ^
      Nat.card (rectangleGraph a w h).edgeSet *
    θ.val ^ ((w + 1) * (h + 1)) /
      θ.val ^ (Nat.card (rectangleGraph a w h).edgeSet + 1)

lemma rectangleDualityFactor_pos (θ : Parameters) (a : LatticeVertex) (w h : ℕ) :
    0 < rectangleDualityFactor θ a w h := by
  unfold rectangleDualityFactor
  exact div_pos (mul_pos
    (pow_pos (dualParameter_den_pos (clusterWeight_pos θ) (edgeParameter_pos θ)
      (edgeParameter_lt_one θ)) _) (pow_pos (clusterWeight_pos θ) _))
    (pow_pos (clusterWeight_pos θ) _)

private lemma dual_weight_algebra {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (a b k l V N : ℕ) (hcard : a + b = N) (heuler : l + V = a + k + 1) :
    p ^ a * (1 - p) ^ b * q ^ k =
      ((p + q * (1 - p)) ^ N * q ^ V / q ^ (N + 1)) *
        (dualParameter q p ^ b * (1 - dualParameter q p) ^ a * q ^ l) := by
  let D := p + q * (1 - p)
  have hD : D ≠ 0 := (dualParameter_den_pos hq hp hp1).ne'
  have hqne : q ≠ 0 := hq.ne'
  have hqexp : V + b + l = N + 1 + k := by omega
  rw [one_sub_dualParameter hq hp hp1, dualParameter]
  change _ = (D ^ N * q ^ V / q ^ (N + 1)) *
    ((q * (1 - p) / D) ^ b * (p / D) ^ a * q ^ l)
  calc
    _ = (p ^ a * (1 - p) ^ b) *
        (q ^ (V + b + l) / q ^ (N + 1)) * (D ^ N / D ^ (a + b)) := by
      rw [hqexp, hcard, pow_add]
      field_simp
    _ = (D ^ N * q ^ V / q ^ (N + 1)) *
        ((q * (1 - p) / D) ^ b * (p / D) ^ a * q ^ l) := by
      simp only [div_pow, mul_pow, pow_add]
      field_simp

/-- Exact free/wired weight transport at complementary edge parameters. -/
theorem rectangle_weight_eq_factor_mul_dual_weight
    (θ : Parameters) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    weight (rectangleGraph a w h) θ (BoundaryCondition.free ∅) A =
      rectangleDualityFactor θ a w h *
        weight (rectangleDualGraph a w h) (dualParameters θ)
          (rectangleDualBoundaryCondition a w h)
          (rectanglePrimalDualConfigurationEquiv a w h A) := by
  let B := rectanglePrimalDualConfigurationEquiv a w h A
  have hcard : A.card + B.card = Nat.card (rectangleGraph a w h).edgeSet := by
    exact rectangleDualConfiguration_card_add_eq_primal_edgeSet a w h A
  have hEuler := rectangleEuler_additive_card_config a w h A
  have hsub : Nat.card (rectangleGraph a w h).edgeSet - A.card = B.card := by omega
  have hsubD : Nat.card (rectangleDualGraph a w h).edgeSet - B.card = A.card := by
    rw [rectangleDualGraph_edgeSet_card_eq_primal_edgeSet]
    omega
  change (edgeParameter θ) ^ A.card * (1 - edgeParameter θ) ^
      (Nat.card (rectangleGraph a w h).edgeSet - A.card) * θ.val ^ _ =
    rectangleDualityFactor θ a w h *
      (dualParameter θ.val (edgeParameter θ) ^ B.card *
        (1 - dualParameter θ.val (edgeParameter θ)) ^
          (Nat.card (rectangleDualGraph a w h).edgeSet - B.card) * θ.val ^ _)
  rw [hsub, hsubD]
  exact dual_weight_algebra (clusterWeight_pos θ) (edgeParameter_pos θ)
    (edgeParameter_lt_one θ) A.card B.card _ _ _ _ hcard hEuler

/-- The genuine primal-free law pushes forward to the genuine dual-wired law
at `p*`, for every independent interior `p` and `q ≥ 1`. -/
theorem rectangleFKLaw_map_primalDualConfigurationEquiv
    (θ : Parameters) (a : LatticeVertex) (w h : ℕ) :
    (law (rectangleGraph a w h) θ (BoundaryCondition.free ∅)).map
        (rectanglePrimalDualConfigurationEquiv a w h) =
      law (rectangleDualGraph a w h) (dualParameters θ)
        (rectangleDualBoundaryCondition a w h) :=
  FiniteProbability.pmf_map_equiv_of_common_factor
    (rectanglePrimalDualConfigurationEquiv a w h) (rectangleDualityFactor θ a w h)
    _ _ (rectangleDualityFactor_pos θ a w h) (weight_pos _ θ _)
    (weight_pos _ (dualParameters θ) _)
    (rectangle_weight_eq_factor_mul_dual_weight θ a w h)

/-- The admissible FK parameter record at the exact frozen critical point. -/
def criticalParameters (q : Set.Ici (1 : ℝ)) : Parameters where
  val := q
  property := q.property
  edgeProbability := ⟨rcCriticalParameter q, rcCriticalParameter_mem_Ioo q⟩

lemma dualParameters_criticalParameters (q : Set.Ici (1 : ℝ)) :
    dualParameters (criticalParameters q) = criticalParameters q := by
  unfold dualParameters criticalParameters
  congr 1
  apply Subtype.ext
  exact dualParameter_rcCriticalParameter q

attribute [local instance] configurationMeasurableSpace

end
end PottsDiscontinuity.FK
