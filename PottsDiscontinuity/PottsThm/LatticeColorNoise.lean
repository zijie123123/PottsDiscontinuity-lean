module

public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Set Topology
open scoped ENNReal

noncomputable section

abbrev LatticeVertex := ℤ × ℤ

def latticeShiftEquiv (a : LatticeVertex) : LatticeVertex ≃ LatticeVertex where
  toFun x := x + a
  invFun x := x - a
  left_inv x := by simp
  right_inv x := by simp

theorem eventually_latticeShift_disjoint (F G : Finset LatticeVertex) :
    ∀ᶠ a : LatticeVertex in cofinite,
      Disjoint F (G.map (latticeShiftEquiv a).symm.toEmbedding) := by
  classical
  let bad : Finset LatticeVertex := (G ×ˢ F).image fun p => p.1 - p.2
  filter_upwards [bad.eventually_cofinite_notMem] with a ha
  apply Finset.disjoint_left.mpr
  intro x hxF hxshift
  obtain ⟨y, hyG, hyx⟩ := Finset.mem_map.mp hxshift
  have hbad : a ∈ bad := by
    apply Finset.mem_image.mpr
    refine ⟨(y, x), Finset.mem_product.mpr ⟨hyG, hxF⟩, ?_⟩
    have heq : y - a = x := by
      simpa [latticeShiftEquiv] using hyx
    apply Prod.ext
    · have hcoord := congrArg Prod.fst heq
      change y.1 - a.1 = x.1 at hcoord
      change y.1 - x.1 = a.1
      omega
    · have hcoord := congrArg Prod.snd heq
      change y.2 - a.2 = x.2 at hcoord
      change y.2 - x.2 = a.2
      omega
  exact (ha hbad).elim

end
end PottsDiscontinuity.PottsThm
