module

public import PottsDiscontinuity.FK.Model
public import PottsDiscontinuity.FK.ProbabilityProduct
public import PottsDiscontinuity.TorusCrossing.Euler

/-!
# Exact weight duality of the mixed board at the self-dual point

At `p = p_c(q)` the Fortuin-Kasteleyn weight of a primal configuration `A` (rows wired) is a fixed
constant multiple of the weight of the complementary dual configuration (side columns wired).
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

theorem card_endEdgeSet {ends : Cell → Cell × Cell} {P M : Finset Cell} (hD : EndData ends P M) :
    Nat.card (endGraph ends P M).edgeSet = M.card := by
  rw [← Nat.card_congr (endEdgeEquiv hD)]
  simp

namespace Rect

variable (R : Rect)

/-- Weight of the primal configuration `A` (rows wired). -/
noncomputable def wP (q : Set.Ici (1 : ℝ)) (A : Finset Cell) : ℝ :=
  FK.weight R.pG (critParams q) R.sepBC (cfgOf R.pData A)

/-- Weight of the complementary dual configuration (side columns wired). -/
noncomputable def wD (q : Set.Ici (1 : ℝ)) (A : Finset Cell) : ℝ :=
  FK.weight R.dG (critParams q) R.dualBC (cfgOf R.dData (R.inner \ A))

theorem wP_pos (q : Set.Ici (1 : ℝ)) (A : Finset Cell) : 0 < R.wP q A :=
  FK.weight_pos _ _ _ _

theorem wD_pos (q : Set.Ici (1 : ℝ)) (A : Finset Cell) : 0 < R.wD q A :=
  FK.weight_pos _ _ _ _

/-- The cross-multiplied form of the exact weight duality. -/
theorem weight_cross (hh : 0 < R.h) (q : Set.Ici (1 : ℝ)) (A : Finset Cell) (hA : A ⊆ R.inner) :
    R.wP q A * R.wD q ∅ = R.wP q ∅ * R.wD q A := by
  have hE := R.euler hh A hA
  have hcard : A.card ≤ R.inner.card := Finset.card_le_card hA
  have hcardd : (R.inner \ A).card = R.inner.card - A.card := Finset.card_sdiff_of_subset hA
  unfold wP wD FK.weight
  rw [card_endEdgeSet R.pData, card_endEdgeSet R.dData, card_cfgOf R.pData A hA,
    card_cfgOf R.pData ∅ (Finset.empty_subset _), card_cfgOf R.dData _ Finset.sdiff_subset,
    card_cfgOf R.dData _ Finset.sdiff_subset, Finset.sdiff_empty, hcardd]
  simp only [Finset.card_empty, Nat.sub_zero, Nat.sub_self, pow_zero, mul_one, one_mul, critParams_val]
  have hq : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
  set s := Real.sqrt q.val with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hq
  have hss : s ^ 2 = q.val := Real.sq_sqrt hq.le
  have hp : FK.edgeParameter (critParams q) = s * (1 - FK.edgeParameter (critParams q)) := by
    rw [critParams_edge]
    field_simp
    ring
  set p := FK.edgeParameter (critParams q) with hpdef
  set t := 1 - p with ht
  have ht0 : 0 < t := FK.one_sub_edgeParameter_pos (critParams q)
  -- Euler relation in natural-number form
  have hnat : R.kD A + R.kP ∅ = R.kP A + A.card + R.kD ∅ := by
    unfold kD kP at *
    omega
  unfold kP kD at hnat
  rw [Finset.sdiff_empty] at hnat
  obtain ⟨b, hb⟩ : ∃ b, R.inner.card = A.card + b := ⟨R.inner.card - A.card, by omega⟩
  rw [hb, show A.card + b - A.card = b by omega, hp]
  rw [← hss]
  set kPA := FK.componentCount R.pG R.sepBC (cfgOf R.pData A)
  set kP0 := FK.componentCount R.pG R.sepBC (cfgOf R.pData ∅)
  set kDA := FK.componentCount R.dG R.dualBC (cfgOf R.dData (R.inner \ A))
  set kD0 := FK.componentCount R.dG R.dualBC (cfgOf R.dData R.inner)
  rw [show A.card + b - b = A.card by omega]
  have key : (s ^ 2) ^ kP0 * (s ^ 2) ^ kDA = (s ^ 2) ^ kPA * (s ^ 2) ^ kD0 * s ^ (2 * A.card) := by
    rw [← pow_add, ← pow_add, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  calc (s * t) ^ A.card * t ^ b * (s ^ 2) ^ kPA * ((s * t) ^ (A.card + b) * (s ^ 2) ^ kD0)
      = (s ^ 2) ^ kPA * (s ^ 2) ^ kD0 * s ^ (2 * A.card) *
          (t ^ (A.card + b) * (s * t) ^ b * t ^ A.card) := by ring
    _ = t ^ (A.card + b) * (s ^ 2) ^ kP0 * ((s * t) ^ b * t ^ A.card * (s ^ 2) ^ kDA) := by
      rw [← key]; ring


/-- Bijection between primal and complementary dual configurations. -/
noncomputable def dualEquiv : FK.Configuration R.pG ≃ FK.Configuration R.dG where
  toFun C := cfgOf R.dData (R.inner \ openMedials R.pData C)
  invFun D := cfgOf R.pData (R.inner \ openMedials R.dData D)
  left_inv C := by
    simp only
    rw [openMedials_cfgOf R.dData _ Finset.sdiff_subset,
      Finset.sdiff_sdiff_eq_self (openMedials_subset R.pData C), cfgOf_openMedials]
  right_inv D := by
    simp only
    rw [openMedials_cfgOf R.pData _ Finset.sdiff_subset,
      Finset.sdiff_sdiff_eq_self (openMedials_subset R.dData D), cfgOf_openMedials]

theorem weight_dualEquiv (hh : 0 < R.h) (q : Set.Ici (1 : ℝ)) (C : FK.Configuration R.pG) :
    FK.weight R.pG (critParams q) R.sepBC C =
      (R.wP q ∅ / R.wD q ∅) *
        FK.weight R.dG (critParams q) R.dualBC (R.dualEquiv C) := by
  have hA := openMedials_subset R.pData C
  have h1 : FK.weight R.pG (critParams q) R.sepBC C = R.wP q (openMedials R.pData C) := by
    unfold wP; rw [cfgOf_openMedials]
  have h2 : FK.weight R.dG (critParams q) R.dualBC (R.dualEquiv C) =
      R.wD q (openMedials R.pData C) := rfl
  rw [h1, h2]
  have := R.weight_cross hh q _ hA
  have hpos := R.wD_pos q ∅
  field_simp
  linarith

end Rect

lemma pmf_scale {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) (hc : 0 < c) (v : α → ℝ)
    (hv : ∀ a, 0 < v a) :
    FK.FiniteProbability.pmf (fun a => c * v a) (fun a => mul_pos hc (hv a)) =
      FK.FiniteProbability.pmf v hv := by
  ext a
  rw [FK.FiniteProbability.pmf_apply, FK.FiniteProbability.pmf_apply]
  unfold FK.FiniteProbability.partition
  rw [← Finset.mul_sum]
  congr 1
  exact mul_div_mul_left _ _ hc.ne'


namespace Rect

variable (R : Rect)

noncomputable local instance pEdgeFintype : Fintype R.pG.edgeSet := Fintype.ofFinite _
noncomputable local instance dEdgeFintype : Fintype R.dG.edgeSet := Fintype.ofFinite _

/-- The primal law with wired rows maps onto the dual law with wired side columns. -/
theorem law_map_dualEquiv (hh : 0 < R.h) (q : Set.Ici (1 : ℝ)) :
    (FK.law R.pG (critParams q) R.sepBC).map R.dualEquiv =
      FK.law R.dG (critParams q) R.dualBC := by
  have hc : 0 < R.wP q ∅ / R.wD q ∅ := div_pos (R.wP_pos q ∅) (R.wD_pos q ∅)
  have h1 := FK.FiniteProbability.pmf_map_equiv_of_weight_eq R.dualEquiv
    (FK.weight R.pG (critParams q) R.sepBC)
    (fun b => (R.wP q ∅ / R.wD q ∅) * FK.weight R.dG (critParams q) R.dualBC b)
    (FK.weight_pos _ _ _) (fun b => mul_pos hc (FK.weight_pos _ _ _ b))
    (fun a => R.weight_dualEquiv hh q a)
  have h2 := pmf_scale (R.wP q ∅ / R.wD q ∅) hc (FK.weight R.dG (critParams q) R.dualBC)
    (FK.weight_pos _ _ _)
  exact h1.trans h2

attribute [local instance] FK.configurationMeasurableSpace

/-- Exact finite-volume duality on events. -/
theorem measure_preimage_dualEquiv (hh : 0 < R.h) (q : Set.Ici (1 : ℝ))
    (S : Set (FK.Configuration R.dG)) :
    FK.measure R.pG (critParams q) R.sepBC (R.dualEquiv ⁻¹' S) =
      FK.measure R.dG (critParams q) R.dualBC S := by
  have hmap := congrArg PMF.toMeasure (R.law_map_dualEquiv hh q)
  rw [← PMF.toMeasure_map _ _ measurable_from_top] at hmap
  change (FK.law R.pG (critParams q) R.sepBC).toMeasure (R.dualEquiv ⁻¹' S) = _
  rw [← MeasureTheory.Measure.map_apply measurable_from_top
    MeasurableSpace.measurableSet_top]
  exact congrArg (fun μ : MeasureTheory.Measure (FK.Configuration R.dG) => μ S) hmap

end Rect

end PottsDiscontinuity.TorusCrossing
