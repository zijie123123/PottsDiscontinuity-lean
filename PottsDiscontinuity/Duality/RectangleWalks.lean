/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Only rectangle walk maps, coordinate bounds, and support preimages retained. -/
module

public import PottsDiscontinuity.Duality.LatticeWalkInterpolation
public import PottsDiscontinuity.Duality.Rectangle
public import PottsDiscontinuity.FK.Graph

@[expose] public section

namespace PottsDiscontinuity.FK
open Curves unitInterval
noncomputable section
def rectangleOpenGraphToSquare (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    openGraph (rectangleGraph a w h) A →g squareLattice where
  toFun := fun v => v.val
  map_rel' := fun huv =>
    (rectangleGraph_adj_iff a w h _ _).mp (openGraph_le (rectangleGraph a w h) A huv)

private theorem complex_segment_coordinate_bounds (a b : ℂ) {z : ℂ}
    {l r d u : ℝ}
    (hz : z ∈ segment ℝ a b)
    (hax : l ≤ a.re) (hbx : l ≤ b.re)
    (hxa : a.re ≤ r) (hxb : b.re ≤ r)
    (hay : d ≤ a.im) (hby : d ≤ b.im)
    (hya : a.im ≤ u) (hyb : b.im ≤ u) :
    l ≤ z.re ∧ z.re ≤ r ∧ d ≤ z.im ∧ z.im ≤ u := by
  rw [segment_eq_image] at hz
  rcases hz with ⟨t, ht, rfl⟩
  simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im, add_zero]
  constructor
  · nlinarith [ht.1, ht.2]
  constructor
  · nlinarith [ht.1, ht.2]
  constructor
  · nlinarith [ht.1, ht.2]
  · nlinarith [ht.1, ht.2]

 def unitMesh : PositiveMesh := ⟨1, by norm_num⟩

theorem latticeWalkPath_coordinate_bounds {u v : LatticeVertex}
    (p : squareLattice.Walk u v) {l r d top : ℝ}
    (hpoints : ∀ x ∈ p.support,
      l ≤ (x.1 : ℝ) ∧ (x.1 : ℝ) ≤ r ∧
      d ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ top) :
    ∀ t : I,
      l ≤ (latticeWalkPath unitMesh p t).re ∧
      (latticeWalkPath unitMesh p t).re ≤ r ∧
      d ≤ (latticeWalkPath unitMesh p t).im ∧
      (latticeWalkPath unitMesh p t).im ≤ top := by
  intro t
  have hmem : latticeWalkPath unitMesh p t ∈ Set.range (latticeWalkPath unitMesh p) :=
    ⟨t, rfl⟩
  obtain ⟨x, y, hx, hy, _, hseg⟩ := latticeWalkPath_range_subset_segments unitMesh p hmem
  rw [Path.range_segment] at hseg
  have hx' := hpoints x hx
  have hy' := hpoints y hy
  have hcoords := complex_segment_coordinate_bounds
    (latticeEmbed unitMesh x) (latticeEmbed unitMesh y) hseg
    (by simpa [unitMesh] using hx'.1) (by simpa [unitMesh] using hy'.1)
    (by simpa [unitMesh] using hx'.2.1) (by simpa [unitMesh] using hy'.2.1)
    (by simpa [unitMesh] using hx'.2.2.1) (by simpa [unitMesh] using hy'.2.2.1)
    (by simpa [unitMesh] using hx'.2.2.2) (by simpa [unitMesh] using hy'.2.2.2)
  simpa [unitMesh] using hcoords

theorem rectangleOpenWalk_mapped_support_preimage (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v) {x : LatticeVertex}
    (hx : x ∈ (p.map (rectangleOpenGraphToSquare a w h A)).support) :
    ∃ z ∈ p.support, z.val = x := by
  rw [SimpleGraph.Walk.support_map] at hx
  rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
  exact ⟨z, hz, rfl⟩

end
end PottsDiscontinuity.FK
