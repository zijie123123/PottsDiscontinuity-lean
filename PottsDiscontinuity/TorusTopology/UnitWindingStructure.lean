module

public import PottsDiscontinuity.TorusTopology.PositiveLoops
public import PottsDiscontinuity.TorusTopology.VerticalSupport

/-! The exact vertical support when U=1. Horizontal winding is unrestricted. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
open scoped Classical
variable {N M : ℕ}

/-- The corrected vertical-loop structure used in Corollary 3.13(ii): precisely two loops,
with opposite unit vertical
windings. There is no horizontal-winding conclusion. -/
theorem U_one_vertical_loop_structure
    (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M)
    (hU : rcVerticalWinding hN hM j A = 1) :
    ∃ q₁ q₂ : Loop hN hM (rcSmoothing A), q₁ ≠ q₂ ∧
      (∀ q, (loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0 ↔
          q = q₁ ∨ q = q₂)) ∧
      loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) j q₁ = 1 ∧
      loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) j q₂ = -1 := by
  let f := loopVertical (checkerArrows N M) (rcSmoothing A)
    (checkerArrows_compatible hN hM (rcSmoothing A)) j
  let S := verticalWindingLoops hN hM j A
  have hmem (q) : q ∈ S ↔ f q ≠ 0 := by simp [S,verticalWindingLoops,f]
  have hcard : S.card ≤ 2 := verticalWindingLoops_card_le_two_of_U_eq_one hN hM j A hU
  have hmass : ∑ q ∈ S, (f q).natAbs = 2 := by
    have he := two_mul_verticalWindingCount hN (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)) j
    change 2 * rcVerticalWinding hN hM j A = _ at he
    have hf : ∑ q ∈ S, (f q).natAbs = verticalMass _ _
        (checkerArrows_compatible hN hM (rcSmoothing A)) j := by
      simp only [S,verticalWindingLoops,Finset.sum_filter,verticalMass]
      apply Finset.sum_congr rfl
      intro q _
      by_cases h : f q = 0 <;> simp_all [f]
    rw [hf]
    omega
  have hsum : ∑ q ∈ S, f q = 0 := by
    rw [show S = univ.filter (fun q => f q ≠ 0) from rfl,Finset.sum_filter_ne_zero]
    exact sum_vertical_winding_zero hN hM j A
  obtain ⟨q,hq⟩ : S.Nonempty := by
    by_contra h
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hmass
  obtain ⟨r,hr,hqr⟩ : ∃ r ∈ S, q ≠ r := by
    by_contra h
    have he : S = {q} := by
      ext r
      simp only [Finset.mem_singleton]
      constructor
      · intro hr
        by_contra hne
        exact h ⟨r,hr,Ne.symm hne⟩
      · rintro rfl
        exact hq
    rw [he,Finset.sum_singleton] at hsum
    exact (hmem q).mp hq hsum
  have he : S = {q,r} := by
    have hsub : ({q,r} : Finset _) ⊆ S := by simp [Finset.insert_subset_iff,hq,hr]
    exact (Finset.eq_of_subset_of_card_le hsub (by simpa [hqr] using hcard)).symm
  rw [he,Finset.sum_pair hqr] at hsum hmass
  have hq0 := (hmem q).mp hq
  have hr0 := (hmem r).mp hr
  have hqabs : (f q).natAbs = 1 := by
    have := Int.natAbs_pos.mpr hq0
    have := Int.natAbs_pos.mpr hr0
    omega
  have hqpm : f q = 1 ∨ f q = -1 := by
    have ha := Int.natCast_natAbs (f q)
    rw [hqabs] at ha
    rcases le_total 0 (f q) with hp | hn
    · left
      rw [abs_of_nonneg hp] at ha
      exact ha.symm
    · right
      rw [abs_of_nonpos hn] at ha
      omega
  have hsupp (t) : f t ≠ 0 ↔ t = q ∨ t = r := by
    rw [← hmem,he]
    simp
  rcases hqpm with hp | hn
  · exact ⟨q,r,hqr,hsupp,hp,by change f r = -1; omega⟩
  · refine ⟨r,q,hqr.symm,?_,by change f r = 1; omega,hn⟩
    intro t
    rw [hsupp,or_comm]

end PottsDiscontinuity.TorusTopology
