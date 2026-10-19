/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.WholePlaneDualGraph
public import Mathlib.Analysis.Convex.Segment

@[expose] public section

namespace PottsDiscontinuity.FK.Medial

noncomputable section

/-- The midpoint of a normalized bond belongs to its actual segment. -/
theorem LatticeBond.midpoint_mem_segment (e : LatticeBond) (δ : PositiveMesh) :
    e.midpoint δ ∈ segment ℝ (latticeEmbed δ e.source) (latticeEmbed δ e.target) := by
  rw [segment_eq_image]
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  simp only [Complex.real_smul]
  norm_num
  dsimp [LatticeBond.midpoint]
  ring

/-- The actual center of the unit face whose lower-left lattice corner is `u`. -/
def dualFaceCenter (δ : PositiveMesh) (u : LatticeVertex) : ℂ :=
  latticeEmbed δ u + (δ.val : ℂ) * (1 + Complex.I) / 2

/-- The complete geometric segment of an original primal bond. -/
def primalBondSegment (δ : PositiveMesh) (b : LatticeBond) : Set ℂ :=
  segment ℝ (latticeEmbed δ b.source) (latticeEmbed δ b.target)

/-- The complete geometric segment joining the centers at the source and target
face bases of the normalized dual bond `d`. -/
def dualBondSegment (δ : PositiveMesh) (d : LatticeBond) : Set ℂ :=
  segment ℝ (dualFaceCenter δ d.source) (dualFaceCenter δ d.target)

private theorem segment_coordinate_parameter (δ : PositiveMesh) {z a b : ℂ}
    (hz : z ∈ segment ℝ a b) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      z.re / δ.val = (1 - t) * (a.re / δ.val) + t * (b.re / δ.val) ∧
      z.im / δ.val = (1 - t) * (a.im / δ.val) + t * (b.im / δ.val) := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, htz⟩ := hz
  refine ⟨t, ht0, ht1, ?_, ?_⟩
  · have hre := congrArg Complex.re htz
    simp only [Complex.real_smul, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
    calc
      z.re / δ.val = ((1 - t) * a.re + t * b.re) / δ.val := by rw [hre]
      _ = (1 - t) * (a.re / δ.val) + t * (b.re / δ.val) := by field_simp
  · have him := congrArg Complex.im htz
    simp only [Complex.real_smul, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at him
    calc
      z.im / δ.val = ((1 - t) * a.im + t * b.im) / δ.val := by rw [him]
      _ = (1 - t) * (a.im / δ.val) + t * (b.im / δ.val) := by field_simp

private theorem latticeEmbed_re_div (δ : PositiveMesh) (u : LatticeVertex) :
    (latticeEmbed δ u).re / δ.val = (u.1 : ℝ) := by
  rw [latticeEmbed_re, div_eq_iff δ.property.ne']
  ring

private theorem latticeEmbed_im_div (δ : PositiveMesh) (u : LatticeVertex) :
    (latticeEmbed δ u).im / δ.val = (u.2 : ℝ) := by
  rw [latticeEmbed_im, div_eq_iff δ.property.ne']
  ring

private theorem dualFaceCenter_re_div (δ : PositiveMesh) (u : LatticeVertex) :
    (dualFaceCenter δ u).re / δ.val = (u.1 : ℝ) + 1 / 2 := by
  simp [dualFaceCenter, latticeEmbed, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  field_simp [ne_of_gt δ.property]

private theorem dualFaceCenter_im_div (δ : PositiveMesh) (u : LatticeVertex) :
    (dualFaceCenter δ u).im / δ.val = (u.2 : ℝ) + 1 / 2 := by
  simp [dualFaceCenter, latticeEmbed, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  field_simp [ne_of_gt δ.property]

private theorem primal_horizontal_coords (δ : PositiveMesh) (x y : ℤ) {z : ℂ}
    (hz : z ∈ primalBondSegment δ ⟨(x, y), .horizontal⟩) :
    (x : ℝ) ≤ z.re / δ.val ∧ z.re / δ.val ≤ (x : ℝ) + 1 ∧
      z.im / δ.val = (y : ℝ) := by
  have hs := segment_coordinate_parameter δ hz
  rcases hs with ⟨t, ht0, ht1, hre, him⟩
  have hre' : z.re / δ.val = (1 - t) * (x : ℝ) + t * ((x + 1 : ℤ) : ℝ) := by
    simpa only [primalBondSegment, LatticeBond.source, LatticeBond.target,
      latticeEmbed_re_div] using hre
  have him' : z.im / δ.val = (1 - t) * (y : ℝ) + t * (y : ℝ) := by
    simpa only [primalBondSegment, LatticeBond.source, LatticeBond.target,
      latticeEmbed_im_div] using him
  simp only [Int.cast_add, Int.cast_one] at hre' him'
  constructor <;> [nlinarith; constructor <;> nlinarith]

private theorem primal_vertical_coords (δ : PositiveMesh) (x y : ℤ) {z : ℂ}
    (hz : z ∈ primalBondSegment δ ⟨(x, y), .vertical⟩) :
    z.re / δ.val = (x : ℝ) ∧ (y : ℝ) ≤ z.im / δ.val ∧
      z.im / δ.val ≤ (y : ℝ) + 1 := by
  have hs := segment_coordinate_parameter δ hz
  rcases hs with ⟨t, ht0, ht1, hre, him⟩
  have hre' : z.re / δ.val = (1 - t) * (x : ℝ) + t * (x : ℝ) := by
    simpa only [primalBondSegment, LatticeBond.source, LatticeBond.target,
      latticeEmbed_re_div] using hre
  have him' : z.im / δ.val = (1 - t) * (y : ℝ) + t * ((y + 1 : ℤ) : ℝ) := by
    simpa only [primalBondSegment, LatticeBond.source, LatticeBond.target,
      latticeEmbed_im_div] using him
  simp only [Int.cast_add, Int.cast_one] at hre' him'
  constructor <;> [nlinarith; constructor <;> nlinarith]

private theorem dual_horizontal_coords (δ : PositiveMesh) (x y : ℤ) {z : ℂ}
    (hz : z ∈ dualBondSegment δ ⟨(x, y), .horizontal⟩) :
    (x : ℝ) + 1 / 2 ≤ z.re / δ.val ∧
      z.re / δ.val ≤ (x : ℝ) + 1 + 1 / 2 ∧
      z.im / δ.val = (y : ℝ) + 1 / 2 := by
  have hs := segment_coordinate_parameter δ hz
  rcases hs with ⟨t, ht0, ht1, hre, him⟩
  have hre' : z.re / δ.val =
      (1 - t) * ((x : ℝ) + 1 / 2) + t * (((x + 1 : ℤ) : ℝ) + 1 / 2) := by
    simpa [dualBondSegment, LatticeBond.source, LatticeBond.target,
      dualFaceCenter_re_div] using hre
  have him' : z.im / δ.val =
      (1 - t) * ((y : ℝ) + 1 / 2) + t * ((y : ℝ) + 1 / 2) := by
    simpa [dualBondSegment, LatticeBond.source, LatticeBond.target,
      dualFaceCenter_im_div] using him
  simp only [Int.cast_add, Int.cast_one] at hre' him'
  constructor <;> [nlinarith; constructor <;> nlinarith]

private theorem dual_vertical_coords (δ : PositiveMesh) (x y : ℤ) {z : ℂ}
    (hz : z ∈ dualBondSegment δ ⟨(x, y), .vertical⟩) :
    z.re / δ.val = (x : ℝ) + 1 / 2 ∧
      (y : ℝ) + 1 / 2 ≤ z.im / δ.val ∧
      z.im / δ.val ≤ (y : ℝ) + 1 + 1 / 2 := by
  have hs := segment_coordinate_parameter δ hz
  rcases hs with ⟨t, ht0, ht1, hre, him⟩
  have hre' : z.re / δ.val =
      (1 - t) * ((x : ℝ) + 1 / 2) + t * ((x : ℝ) + 1 / 2) := by
    simpa [dualBondSegment, LatticeBond.source, LatticeBond.target,
      dualFaceCenter_re_div] using hre
  have him' : z.im / δ.val =
      (1 - t) * ((y : ℝ) + 1 / 2) + t * (((y + 1 : ℤ) : ℝ) + 1 / 2) := by
    simpa [dualBondSegment, LatticeBond.source, LatticeBond.target,
      dualFaceCenter_im_div] using him
  simp only [Int.cast_add, Int.cast_one] at hre' him'
  constructor <;> [nlinarith; constructor <;> nlinarith]

private theorem int_cast_half_impossible (a b : ℤ) (h : (a : ℝ) = (b : ℝ) + 1 / 2) : False := by
  have hh : (2 : ℤ) * a = 2 * b + 1 := by
    exact_mod_cast (show (2 : ℝ) * (a : ℝ) = 2 * (b : ℝ) + 1 by nlinarith)
  omega

private theorem crossing_of_intersection (δ : PositiveMesh) (b d : LatticeBond)
    (h : (primalBondSegment δ b ∩ dualBondSegment δ d).Nonempty) :
    d = dualBondOfPrimal b := by
  rcases h with ⟨z, hp, hd⟩
  rcases b with ⟨⟨x,y⟩, ab⟩
  rcases d with ⟨⟨u,v⟩, ad⟩
  cases ab <;> cases ad
  · have p := primal_horizontal_coords δ x y hp
    have q := dual_horizontal_coords δ u v hd
    exact False.elim (int_cast_half_impossible y v (p.2.2.symm.trans q.2.2))
  · have p := primal_horizontal_coords δ x y hp
    have q := dual_vertical_coords δ u v hd
    rcases p with ⟨px₁, px₂, py⟩
    rcases q with ⟨qx, qy₁, qy₂⟩
    have hu₁ : (u : ℝ) < (x : ℝ) + 1 := by linarith
    have hu₂ : (x : ℝ) - 1 < (u : ℝ) := by linarith
    have hv₁ : (v : ℝ) < (y : ℝ) := by linarith
    have hv₂ : (y : ℝ) < (v : ℝ) + 2 := by linarith
    have hu₁' : u < x + 1 := by exact_mod_cast hu₁
    have hu₂' : x - 1 < u := by exact_mod_cast hu₂
    have hv₁' : v < y := by exact_mod_cast hv₁
    have hv₂' : y < v + 2 := by exact_mod_cast hv₂
    have hu : u = x := by omega
    have hv : v = y - 1 := by omega
    subst u; subst v
    simp [dualBondOfPrimal]
  · have p := primal_vertical_coords δ x y hp
    have q := dual_horizontal_coords δ u v hd
    rcases p with ⟨px, py₁, py₂⟩
    rcases q with ⟨qx₁, qx₂, qy⟩
    have hu₁ : (u : ℝ) < (x : ℝ) := by linarith
    have hu₂ : (x : ℝ) < (u : ℝ) + 2 := by linarith
    have hv₁ : (v : ℝ) < (y : ℝ) + 1 := by linarith
    have hv₂ : (y : ℝ) - 1 < (v : ℝ) := by linarith
    have hu₁' : u < x := by exact_mod_cast hu₁
    have hu₂' : x < u + 2 := by exact_mod_cast hu₂
    have hv₁' : v < y + 1 := by exact_mod_cast hv₁
    have hv₂' : y - 1 < v := by exact_mod_cast hv₂
    have hu : u = x - 1 := by omega
    have hv : v = y := by omega
    subst u; subst v
    simp [dualBondOfPrimal]
  · have p := primal_vertical_coords δ x y hp
    have q := dual_vertical_coords δ u v hd
    exact False.elim (int_cast_half_impossible x u (p.1.symm.trans q.1))

/-- A primal unit segment and a dual face-center segment meet exactly when
these normalized bonds cross. -/
theorem primalDualSegments_intersect_iff (δ : PositiveMesh) (b d : LatticeBond) :
    (primalBondSegment δ b ∩ dualBondSegment δ d).Nonempty ↔
      d = dualBondOfPrimal b := by
  constructor
  · exact crossing_of_intersection δ b d
  · intro h
    subst d
    refine ⟨b.midpoint δ, ?_, ?_⟩
    · exact b.midpoint_mem_segment δ
    · have hm : b.midpoint δ =
          midpoint ℝ (dualFaceCenter δ (dualBondOfPrimal b).source)
            (dualFaceCenter δ (dualBondOfPrimal b).target) := by
        rw [midpoint_eq_smul_add]
        rcases b with ⟨⟨x,y⟩, ax⟩
        cases ax <;> apply Complex.ext <;>
          simp [LatticeBond.midpoint, dualBondOfPrimal, LatticeBond.source,
            LatticeBond.target, dualFaceCenter, latticeEmbed,
            Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
      rw [dualBondSegment, hm]
      exact (_root_.midpoint_mem_segment (𝕜 := ℝ) (E := ℂ) _ _)

/-- No actual primal lattice vertex lies on any dual face-center bond. -/
theorem latticeVertex_not_mem_dualBondSegment (δ : PositiveMesh)
    (u : LatticeVertex) (d : LatticeBond) :
    latticeEmbed δ u ∉ dualBondSegment δ d := by
  rcases u with ⟨x,y⟩
  rcases d with ⟨⟨a,b⟩, ax⟩
  intro hz
  cases ax
  · have q := dual_horizontal_coords δ a b hz
    have hy : (y : ℝ) = (b : ℝ) + 1 / 2 := by
      simpa only [latticeEmbed_im_div] using q.2.2
    exact False.elim (int_cast_half_impossible y b hy)
  · have q := dual_vertical_coords δ a b hz
    have hx : (x : ℝ) = (a : ℝ) + 1 / 2 := by
      simpa only [latticeEmbed_re_div] using q.1
    exact False.elim (int_cast_half_impossible x a hx)

end
end PottsDiscontinuity.FK.Medial
