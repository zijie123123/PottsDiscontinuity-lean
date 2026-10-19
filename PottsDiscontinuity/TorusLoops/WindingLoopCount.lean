module

public import PottsDiscontinuity.Torus.DiamondGraph
public import PottsDiscontinuity.TorusLoops.HorizontalHomology

/-!
# Bounds for loops with nonzero coordinate winding

For a directed smoothed loop, nonzero intersection with either coordinate seam
is its nonzero torus winding class. The source statistic `ell₀`, the number of loops that
are not retractable to a point on the torus, is formalized throughout as the number of loops
with nonzero homological winding, i.e. nonzero algebraic intersection with the vertical or the
horizontal seam. No homotopy classification is used.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- A nonzero sum on a loop has a nonzero dart contribution on that loop. -/
theorem exists_dart_of_loopSum_ne_zero (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (f : Dart N M → ℤ) (q : DirectedLoop ω s h)
    (hsum : loopSum ω s h f q ≠ 0) :
    ∃ d : DirectedDart ω, directedLoopOf ω s h d = q ∧ f d.val ≠ 0 := by
  classical
  unfold loopSum at hsum
  obtain ⟨d, hd, hfd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨d, ?_, hfd⟩
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hd

/-- Directed darts crossing the chosen horizontal seam. -/
noncomputable def verticalCutDarts (ω : ArrowConfig N M) (j : Fin M) :
    Finset (DirectedDart ω) :=
  Finset.univ.filter fun d => verticalCross j d.val ≠ 0

/-- Directed darts crossing the chosen vertical seam. -/
noncomputable def horizontalCutDarts (ω : ArrowConfig N M) (i : Fin N) :
    Finset (DirectedDart ω) :=
  Finset.univ.filter fun d => horizontalCross i d.val ≠ 0

private theorem dartEdge_eq_fixed_vertical {ω : ArrowConfig N M} {j : Fin M}
    (d : DirectedDart ω) (hd : verticalCross j d.val ≠ 0) :
    dartEdge d.val = ((d.val.1.1, j), true) := by
  rcases d with ⟨⟨⟨i, k⟩, p⟩, hout⟩
  cases p <;> simp [verticalCross, dartEdge] at hd ⊢ <;> assumption

private theorem dartEdge_eq_fixed_horizontal {ω : ArrowConfig N M} {i : Fin N}
    (d : DirectedDart ω) (hd : horizontalCross i d.val ≠ 0) :
    dartEdge d.val = ((i, d.val.1.2), false) := by
  rcases d with ⟨⟨⟨k, j⟩, p⟩, hout⟩
  cases p <;> simp [horizontalCross, dartEdge] at hd ⊢ <;> assumption

/-- A fixed horizontal seam has at most one directed dart per indexed edge. -/
theorem verticalCutDarts_card_le (ω : ArrowConfig N M) (j : Fin M) :
    (verticalCutDarts ω j).card ≤ N := by
  classical
  let C := verticalCutDarts ω j
  have hinj : (C : Set (DirectedDart ω)).InjOn
      (fun d => d.val.1.1) := by
    intro d hd e he hcoord
    change d.val.1.1 = e.val.1.1 at hcoord
    have hd' : verticalCross j d.val ≠ 0 := (Finset.mem_filter.mp hd).2
    have he' : verticalCross j e.val ≠ 0 := (Finset.mem_filter.mp he).2
    have hEdge : dartEdge d.val = dartEdge e.val := by
      rw [dartEdge_eq_fixed_vertical d hd', dartEdge_eq_fixed_vertical e he', hcoord]
    have htransport := congrArg (edgeDirectedEquiv ω) hEdge
    have hdInv : edgeDirectedEquiv ω (dartEdge d.val) = d := by
      apply Subtype.ext
      exact arrowDart_dartEdge ω d
    have heInv : edgeDirectedEquiv ω (dartEdge e.val) = e := by
      apply Subtype.ext
      exact arrowDart_dartEdge ω e
    rw [hdInv, heInv] at htransport
    exact htransport
  calc
    C.card ≤ (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card_of_injOn (s := C) (t := Finset.univ)
        (fun d => d.val.1.1) (by intro d hd; simp) hinj
    _ = N := by simp

/-- A fixed vertical seam has at most one directed dart per indexed edge. -/
theorem horizontalCutDarts_card_le (ω : ArrowConfig N M) (i : Fin N) :
    (horizontalCutDarts ω i).card ≤ M := by
  classical
  let C := horizontalCutDarts ω i
  have hinj : (C : Set (DirectedDart ω)).InjOn
      (fun d => d.val.1.2) := by
    intro d hd e he hcoord
    change d.val.1.2 = e.val.1.2 at hcoord
    have hd' : horizontalCross i d.val ≠ 0 := (Finset.mem_filter.mp hd).2
    have he' : horizontalCross i e.val ≠ 0 := (Finset.mem_filter.mp he).2
    have hEdge : dartEdge d.val = dartEdge e.val := by
      rw [dartEdge_eq_fixed_horizontal d hd', dartEdge_eq_fixed_horizontal e he', hcoord]
    have htransport := congrArg (edgeDirectedEquiv ω) hEdge
    have hdInv : edgeDirectedEquiv ω (dartEdge d.val) = d := by
      apply Subtype.ext
      exact arrowDart_dartEdge ω d
    have heInv : edgeDirectedEquiv ω (dartEdge e.val) = e := by
      apply Subtype.ext
      exact arrowDart_dartEdge ω e
    rw [hdInv, heInv] at htransport
    exact htransport
  calc
    C.card ≤ (Finset.univ : Finset (Fin M)).card :=
      Finset.card_le_card_of_injOn (s := C) (t := Finset.univ)
        (fun d => d.val.1.2) (by intro d hd; simp) hinj
    _ = M := by simp

/-- Loops with nonzero winding in either coordinate, measured at reference seams. -/
noncomputable def windingLoopSet (hN : Even N) (hM : Even M)
    (i : Fin N) (j : Fin M) (A : RCConfig N M) :
    Finset (Loop hN hM (rcSmoothing A)) := by
  classical
  exact Finset.univ.filter fun q =>
      loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0 ∨
      loopSum (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) (horizontalCross i) q ≠ 0

/-- Cardinality of the explicitly defined nonzero-winding loop set. -/
noncomputable def windingLoopCount (hN : Even N) (hM : Even M)
    (i : Fin N) (j : Fin M) (A : RCConfig N M) : ℕ :=
  (windingLoopSet hN hM i j A).card

/-- Images of the two finite seam-crossing dart sets in the loop quotient. -/
noncomputable def loopCutImages (hN : Even N) (hM : Even M)
    (i : Fin N) (j : Fin M) (A : RCConfig N M) :
    Finset (Loop hN hM (rcSmoothing A)) := by
  classical
  exact Finset.image (directedLoopOf (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)))
      (verticalCutDarts (checkerArrows N M) j) ∪
    Finset.image (directedLoopOf (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)))
      (horizontalCutDarts (checkerArrows N M) i)

/-- A nonzero winding loop contains a dart crossing one of the two reference seams. -/
theorem windingLoopSet_subset_cutImages (hN : Even N) (hM : Even M)
    (i : Fin N) (j : Fin M) (A : RCConfig N M) :
    windingLoopSet hN hM i j A ⊆ loopCutImages hN hM i j A := by
  classical
  intro q hq
  have hq' := (Finset.mem_filter.mp hq).2
  rcases hq' with hv | hh
  · obtain ⟨d, hloop, hcross⟩ := exists_dart_of_loopSum_ne_zero
      (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A))
      (verticalCross j) q (by simpa [loopVertical] using hv)
    have hdmem : d ∈ verticalCutDarts (checkerArrows N M) j := by
      simp [verticalCutDarts, hcross]
    change _ ∈
      Finset.image (directedLoopOf (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)))
        (verticalCutDarts (checkerArrows N M) j) ∪ _
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨d, hdmem, hloop⟩))
  · obtain ⟨d, hloop, hcross⟩ := exists_dart_of_loopSum_ne_zero
      (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A))
      (horizontalCross i) q hh
    have hdmem : d ∈ horizontalCutDarts (checkerArrows N M) i := by
      simp [horizontalCutDarts, hcross]
    change _ ∈
      _ ∪ Finset.image (directedLoopOf (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)))
        (horizontalCutDarts (checkerArrows N M) i)
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨d, hdmem, hloop⟩))

/-- The number of loops with nonzero coordinate winding is at most `N + M`.

This finite counting bound is independent of the still separate identification
between nonzero winding and the source's topological terminology.
-/
theorem windingLoopCount_le (hN : Even N) (hM : Even M)
    (i : Fin N) (j : Fin M) (A : RCConfig N M) :
    windingLoopCount hN hM i j A ≤ N + M := by
  classical
  unfold windingLoopCount
  calc
    (windingLoopSet hN hM i j A).card ≤
        (loopCutImages hN hM i j A).card := by
      exact Finset.card_le_card (windingLoopSet_subset_cutImages hN hM i j A)
    _ ≤ (verticalCutDarts (checkerArrows N M) j).card +
        (horizontalCutDarts (checkerArrows N M) i).card := by
      calc
        (loopCutImages hN hM i j A).card ≤
            (Finset.image (directedLoopOf (checkerArrows N M) (rcSmoothing A)
              (checkerArrows_compatible hN hM (rcSmoothing A)))
              (verticalCutDarts (checkerArrows N M) j)).card +
            (Finset.image (directedLoopOf (checkerArrows N M) (rcSmoothing A)
              (checkerArrows_compatible hN hM (rcSmoothing A)))
              (horizontalCutDarts (checkerArrows N M) i)).card := by
          simp only [loopCutImages]
          exact Finset.card_union_le _ _
        _ ≤ (verticalCutDarts (checkerArrows N M) j).card +
            (horizontalCutDarts (checkerArrows N M) i).card :=
          Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ N + M := Nat.add_le_add
      (verticalCutDarts_card_le _ _) (horizontalCutDarts_card_le _ _)

end PottsDiscontinuity.TorusLoops
