module

public import Mathlib.Analysis.Convex.Segment
public import FixedPointTheorems.brouwer
public import Mathlib

/-! # Straight-segment interpolation of lifted walks -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Set

noncomputable section

/-- Coordinate embedding of an integer cell in the real plane. -/
def cellEmbed (z : ℤ × ℤ) : ℝ × ℝ := (z.1,z.2)

theorem cellEmbed_injective : Function.Injective cellEmbed := by
  intro u v h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    change (u.1:ℝ) = (v.1:ℝ) at hx
    exact_mod_cast hx
  · have hy := congrArg Prod.snd h
    change (u.2:ℝ) = (v.2:ℝ) at hy
    exact_mod_cast hy

/-- Polygonal interpolation retains every edge and every repeated visit. -/
def polygonWalkPath {V : Type*} {G : SimpleGraph V} (f : V → ℝ × ℝ) :
    {u v : V} → G.Walk u v → Path (f u) (f v)
  | _,_,.nil => Path.refl _
  | u,_,.cons (v := v) _ p => (Path.segment (f u) (f v)).trans (polygonWalkPath f p)

theorem polygonWalkPath_range {V : Type*} {G : SimpleGraph V}
    (f : V → ℝ × ℝ) {u v : V} (w : G.Walk u v) :
    Set.range (polygonWalkPath f w) ⊆
      {z | ∃ x y : V, x ∈ w.support ∧ y ∈ w.support ∧
        (x = y ∨ G.Adj x y) ∧ z ∈ segment ℝ (f x) (f y)} := by
  induction w with
  | nil =>
    rintro z ⟨t,rfl⟩
    exact ⟨_,_,by simp,by simp,Or.inl rfl,left_mem_segment ℝ _ _⟩
  | @cons u v z huv p ih =>
    intro x hx
    change x ∈ Set.range ((Path.segment (f u) (f v)).trans (polygonWalkPath f p)) at hx
    rw [Path.trans_range] at hx
    rcases hx with hx | hx
    · exact ⟨u,v,by simp,by simp,Or.inr huv,by simpa only [Path.range_segment] using hx⟩
    · obtain ⟨a,b,ha,hb,hab,hseg⟩ := ih hx
      exact ⟨a,b,by simp [ha],by simp [hb],hab,hseg⟩

/-- Coordinatewise bounds on all visited vertices bound the entire polygonal
interpolation, including its edge interiors. -/
theorem polygonWalkPath_mem_Icc {V : Type*} {G : SimpleGraph V}
    (f : V → ℝ × ℝ) {u v : V} (w : G.Walk u v) (a b : ℝ × ℝ)
    (hbox : ∀ z ∈ w.support, f z ∈ Set.Icc a b) :
    ∀ t, polygonWalkPath f w t ∈ Set.Icc a b := by
  intro t
  obtain ⟨x,y,hx,hy,_,hseg⟩ := polygonWalkPath_range f w ⟨t,rfl⟩
  exact (convex_Icc a b).segment_subset (hbox x hx) (hbox y hy) hseg

/-- An integer point on a unit diagonal segment must be an endpoint. -/
theorem integer_mem_diagonal_segment {p q z : ℤ × ℤ}
    (hx : |p.1-q.1| = 1) (_hy : |p.2-q.2| = 1)
    (hz : cellEmbed z ∈ segment ℝ (cellEmbed p) (cellEmbed q)) : z = p ∨ z = q := by
  rw [segment_eq_image] at hz
  obtain ⟨t,⟨ht0,ht1⟩,htz⟩ := hz
  have hxeq := congrArg Prod.fst htz
  change (1-t)*(p.1:ℝ)+t*(q.1:ℝ) = (z.1:ℝ) at hxeq
  have hxne : p.1 ≠ q.1 := by intro heq; simp [heq] at hx
  have hdx : (q.1:ℝ)-(p.1:ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hxne.symm)
  have hpmin : (0:ℝ) ≤ (p.1:ℝ)-(min p.1 q.1:ℤ) := by exact_mod_cast sub_nonneg.mpr (min_le_left _ _)
  have hqmin : (0:ℝ) ≤ (q.1:ℝ)-(min p.1 q.1:ℤ) := by exact_mod_cast sub_nonneg.mpr (min_le_right _ _)
  have hpmax : (0:ℝ) ≤ (max p.1 q.1:ℤ)-(p.1:ℝ) := by exact_mod_cast sub_nonneg.mpr (le_max_left _ _)
  have hqmax : (0:ℝ) ≤ (max p.1 q.1:ℤ)-(q.1:ℝ) := by exact_mod_cast sub_nonneg.mpr (le_max_right _ _)
  have hzlo : (min p.1 q.1:ℤ) ≤ z.1 := by
    have h : ((min p.1 q.1:ℤ):ℝ) ≤ z.1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hpmin,mul_nonneg ht0 hqmin]
    exact_mod_cast h
  have hzhi : z.1 ≤ (max p.1 q.1:ℤ) := by
    have h : (z.1:ℝ) ≤ (max p.1 q.1:ℤ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hpmax,mul_nonneg ht0 hqmax]
    exact_mod_cast h
  have hcoord : z.1 = p.1 ∨ z.1 = q.1 := by
    have h := abs_le.mp (le_of_eq hx)
    omega
  rcases hcoord with heq | heq
  · have heqR : (z.1:ℝ) = p.1 := by exact_mod_cast heq
    have hprod : t*((q.1:ℝ)-p.1) = 0 := by nlinarith
    have ht : t = 0 := (mul_eq_zero.mp hprod).resolve_right hdx
    left
    apply cellEmbed_injective
    simpa [ht] using htz.symm
  · have heqR : (z.1:ℝ) = q.1 := by exact_mod_cast heq
    have hprod : (1-t)*((q.1:ℝ)-p.1) = 0 := by nlinarith
    have ht : t = 1 := by have h := (mul_eq_zero.mp hprod).resolve_right hdx; linarith
    right
    apply cellEmbed_injective
    simpa [ht] using htz.symm

end

end PottsDiscontinuity.TorusRC
