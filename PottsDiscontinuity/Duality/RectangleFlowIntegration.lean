/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleCurl
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

abbrev RectanglePrimalFlow (a : LatticeVertex) (w h : ℕ) :=
  RectanglePrimalBond a w h → ℝ

def rectangleExtendedPrimalFlow (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (b : LatticeBond) : ℝ :=
  if hb : b.source ∈ latticeRectangle a w h ∧ b.target ∈ latticeRectangle a w h
  then F ⟨b, hb⟩ else 0

noncomputable def rectanglePrimalFlowDivergence (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (v : LatticeVertex) : ℝ :=
  ∑ b : rectangleActualIncidentBonds a w h v,
    if b.1.1.source = v then F b.1 else -F b.1

def rectangleFlowH (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (x y : ℤ) : ℝ :=
  rectangleExtendedPrimalFlow a w h F ⟨(x,y), .horizontal⟩

def rectangleFlowV (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (x y : ℤ) : ℝ :=
  rectangleExtendedPrimalFlow a w h F ⟨(x,y), .vertical⟩

def rectangleFlowX (a : LatticeVertex) (n : ℤ) : ℤ := a.1 + n
def rectangleFlowY (a : LatticeVertex) (m : ℤ) : ℤ := a.2 + m

def rectangleFlowVertex (a : LatticeVertex) (n m : ℤ) : LatticeVertex :=
  (rectangleFlowX a n, rectangleFlowY a m)

def rectangleFlowDivergenceStencil (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (v : LatticeVertex) : ℝ :=
  rectangleExtendedPrimalFlow a w h F ⟨v, .horizontal⟩ -
    rectangleExtendedPrimalFlow a w h F ⟨(v.1 - 1, v.2), .horizontal⟩ +
    rectangleExtendedPrimalFlow a w h F ⟨v, .vertical⟩ -
    rectangleExtendedPrimalFlow a w h F ⟨(v.1, v.2 - 1), .vertical⟩

/-- A flow with genuine zero incidence divergence at every primal vertex. -/
def RectangleDivergenceFreeFlow (a : LatticeVertex) (w h : ℕ) :=
  {F : RectanglePrimalFlow a w h //
    ∀ v, v ∈ latticeRectangle a w h → rectanglePrimalFlowDivergence a w h F v = 0}

def rectangleFlowSignedCandidate (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (v : LatticeVertex) (i : Fin 4) : ℝ :=
  if (rectangleCurlIncidentCandidate v i).source = v then
    rectangleExtendedPrimalFlow a w h F (rectangleCurlIncidentCandidate v i)
  else -rectangleExtendedPrimalFlow a w h F (rectangleCurlIncidentCandidate v i)

private theorem rectangleFlowCandidate_outside_zero
    (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
    (v : LatticeVertex) (i : Fin 4)
    (hout : ¬ rectangleCurlCandidateInside a w h v i) :
    rectangleExtendedPrimalFlow a w h F (rectangleCurlIncidentCandidate v i) = 0 := by
  simp only [rectangleExtendedPrimalFlow]
  split_ifs with hb
  · have hin : rectangleCurlCandidateInside a w h v i := by
      change (rectangleCurlIncidentCandidate v i).source ∈ latticeRectangle a w h ∧
        (rectangleCurlIncidentCandidate v i).target ∈ latticeRectangle a w h
      exact hb
    exact (hout hin).elim
  · rfl

private theorem rectangleFlowSignedCandidate_eq_term
    (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
    (v : LatticeVertex) (i : Fin 4)
    (hi : rectangleCurlCandidateInside a w h v i) :
    rectangleFlowSignedCandidate a w h F v i =
      match i.val with
      | 0 => rectangleFlowH a w h F v.1 v.2
      | 1 => -rectangleFlowH a w h F (v.1 - 1) v.2
      | 2 => rectangleFlowV a w h F v.1 v.2
      | _ => -rectangleFlowV a w h F v.1 (v.2 - 1) := by
  rcases v with ⟨x, y⟩
  fin_cases i
  · (simp [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
      rectangleExtendedPrimalFlow, rectangleFlowH, LatticeBond.source];
      split_ifs) <;> rfl
  · have hn : (x - 1, y) ≠ (x, y) := by
      intro hh
      have hx := congrArg Prod.fst hh
      omega
    (simp [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
      rectangleExtendedPrimalFlow, rectangleFlowH, LatticeBond.source, hn];
      split_ifs) <;> rfl
  · (simp [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
      rectangleExtendedPrimalFlow, rectangleFlowV, LatticeBond.source];
      split_ifs) <;> rfl
  · have hn : (x, y - 1) ≠ (x, y) := by
      intro hh
      have hy := congrArg Prod.snd hh
      omega
    (simp [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
      rectangleExtendedPrimalFlow, rectangleFlowV, LatticeBond.source, hn];
      split_ifs) <;> rfl

theorem rectanglePrimalFlowDivergence_eq_stencil
    (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
    (v : LatticeVertex) :
    rectanglePrimalFlowDivergence a w h F v = rectangleFlowDivergenceStencil a w h F v := by
  classical
  let e := rectangleActualIncidentCandidateEquiv a w h v
  let p : Fin 4 → Prop := rectangleCurlCandidateInside a w h v
  let : DecidablePred p := Classical.decPred p
  have hsub :
      (∑ i ∈ Finset.univ.filter p, rectangleFlowSignedCandidate a w h F v i) =
        (∑ i : {i : Fin 4 // p i}, rectangleFlowSignedCandidate a w h F v i.1) :=
    Finset.sum_subtype (p := p) (Finset.univ.filter p)
      (by intro i; simp [p])
      (fun i => rectangleFlowSignedCandidate a w h F v i)
  calc
    rectanglePrimalFlowDivergence a w h F v =
        ∑ b : rectangleActualIncidentBonds a w h v,
          rectangleFlowSignedCandidate a w h F v (e b).1 := by
      change (∑ b : rectangleActualIncidentBonds a w h v,
        if b.1.1.source = v then F b.1 else -F b.1) = _
      apply Finset.sum_congr rfl
      intro b hb
      have hmap : rectangleCurlIncidentCandidate v (e b).1 = b.1.1 :=
        congrArg (fun z : rectangleActualIncidentBonds a w h v => z.1.1) (e.left_inv b)
      have hflow : rectangleExtendedPrimalFlow a w h F
          (rectangleCurlIncidentCandidate v (e b).1) = F b.1 := by
        simp [rectangleExtendedPrimalFlow, hmap, b.1.2]
      simp [rectangleFlowSignedCandidate, hmap,
        rectangleExtendedPrimalFlow, b.1.2]
    _ = ∑ i : {i : Fin 4 // p i}, rectangleFlowSignedCandidate a w h F v i.1 :=
      Equiv.sum_comp e (fun i => rectangleFlowSignedCandidate a w h F v i.1)
    _ = rectangleFlowDivergenceStencil a w h F v := by
      rw [← hsub]
      rw [Finset.sum_filter]
      change (∑ i : Fin 4,
        if p i then rectangleFlowSignedCandidate a w h F v i else 0) = _
      have hterm (i : Fin 4) :
          (if p i then rectangleFlowSignedCandidate a w h F v i else 0) =
            match i.val with
            | 0 => rectangleFlowH a w h F v.1 v.2
            | 1 => -rectangleFlowH a w h F (v.1 - 1) v.2
            | 2 => rectangleFlowV a w h F v.1 v.2
            | _ => -rectangleFlowV a w h F v.1 (v.2 - 1) := by
        fin_cases i
        · by_cases hp : p 0
          · simpa [hp, rectangleFlowH, rectangleFlowV] using
              rectangleFlowSignedCandidate_eq_term a w h F v 0 hp
          · have hz := rectangleFlowCandidate_outside_zero a w h F v 0 hp
            simpa [hp, rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
              rectangleFlowH, rectangleFlowV] using hz.symm
        · by_cases hp : p 1
          · simpa [hp, rectangleFlowH, rectangleFlowV] using
              rectangleFlowSignedCandidate_eq_term a w h F v 1 hp
          · have hz := rectangleFlowCandidate_outside_zero a w h F v 1 hp
            simpa [hp, rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
              rectangleFlowH, rectangleFlowV] using hz
        · by_cases hp : p 2
          · simpa [hp, rectangleFlowH, rectangleFlowV] using
              rectangleFlowSignedCandidate_eq_term a w h F v 2 hp
          · have hz := rectangleFlowCandidate_outside_zero a w h F v 2 hp
            simpa [hp, rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
              rectangleFlowH, rectangleFlowV] using hz.symm
        · by_cases hp : p 3
          · simpa [hp, rectangleFlowH, rectangleFlowV] using
              rectangleFlowSignedCandidate_eq_term a w h F v 3 hp
          · have hz := rectangleFlowCandidate_outside_zero a w h F v 3 hp
            have hn := congrArg Neg.neg hz
            simpa [hp, rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
              rectangleFlowH, rectangleFlowV] using hn
      simp_rw [hterm]
      simp [Fin.sum_univ_succ, rectangleFlowDivergenceStencil,
        rectangleFlowH, rectangleFlowV]
      ring_nf

private theorem rectangleFlowDivergenceStencil_offset
    (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
    (n m : ℤ) :
    rectangleFlowDivergenceStencil a w h F (rectangleFlowVertex a n m) =
      rectangleFlowH a w h F (rectangleFlowX a n) (rectangleFlowY a m) -
        rectangleFlowH a w h F (rectangleFlowX a (n - 1)) (rectangleFlowY a m) +
      rectangleFlowV a w h F (rectangleFlowX a n) (rectangleFlowY a m) -
        rectangleFlowV a w h F (rectangleFlowX a n) (rectangleFlowY a (m - 1)) := by
  simp [rectangleFlowDivergenceStencil, rectangleFlowH, rectangleFlowV,
    rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
  have hx : a.1 + n - 1 = a.1 + (n - 1) := by ring
  have hy : a.2 + m - 1 = a.2 + (m - 1) := by ring
  rw [hx, hy]

private theorem rectangleFlowVertex_mem
    (a : LatticeVertex) (w h : ℕ) (n m : ℕ)
    (hn : n ≤ w) (hm : m ≤ h) :
    rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ latticeRectangle a w h := by
  rw [mem_latticeRectangle]
  simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
  omega

def rectangleFlowRowSumV (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    rectangleFlowV a w h F (rectangleFlowX a (k : ℤ)) (rectangleFlowY a (m : ℤ))

private theorem rectangleFlowOffsetDiv_zero
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (n m : ℕ) (hn : n ≤ w) (hm : m ≤ h) :
    rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a (m : ℤ)) -
      rectangleFlowH a w h F.1 (rectangleFlowX a ((n : ℤ) - 1)) (rectangleFlowY a (m : ℤ)) +
      rectangleFlowV a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a (m : ℤ)) -
      rectangleFlowV a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a ((m : ℤ) - 1)) = 0 := by
  have hv := rectangleFlowVertex_mem a w h n m hn hm
  have hz := F.2 _ hv
  rw [rectanglePrimalFlowDivergence_eq_stencil a w h F.1 _] at hz
  rw [rectangleFlowDivergenceStencil_offset] at hz
  exact hz

private theorem rectangleFlowRowDiff_sum
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (n m : ℕ) (hn : n ≤ w) (hm : m ≤ h) :
    (∑ k ∈ Finset.range (n + 1),
      (rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ)) (rectangleFlowY a (m : ℤ)) -
        rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ))
          (rectangleFlowY a ((m : ℤ) - 1)))) =
      rectangleFlowH a w h F.1 (rectangleFlowX a ((0 : ℤ) - 1)) (rectangleFlowY a (m : ℤ)) -
        rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a (m : ℤ)) := by
  induction n with
  | zero =>
      have hd := rectangleFlowOffsetDiv_zero a w h F 0 m (by omega) hm
      simp [rectangleFlowX] at hd ⊢
      linarith
  | succ n ih =>
      have hn' : n ≤ w := by omega
      have hd := rectangleFlowOffsetDiv_zero a w h F (n + 1) m (by omega) hm
      rw [Finset.sum_range_succ]
      rw [ih hn']
      simp only [Nat.cast_add, Nat.cast_one, rectangleFlowX] at hd ⊢
      ring_nf at hd ⊢
      linarith

private theorem rectangleFlowSideHorizontal_zero
    (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
    (m : ℕ) :
    rectangleFlowH a w h F (rectangleFlowX a ((0 : ℤ) - 1))
        (rectangleFlowY a (m : ℤ)) = 0 ∧
    rectangleFlowH a w h F (rectangleFlowX a (w : ℤ))
        (rectangleFlowY a (m : ℤ)) = 0 := by
  constructor
  · simp [rectangleFlowH, rectangleFlowX, rectangleFlowY,
      rectangleExtendedPrimalFlow, LatticeBond.source, LatticeBond.target,
      mem_latticeRectangle]
  · simp [rectangleFlowH, rectangleFlowX, rectangleFlowY,
      rectangleExtendedPrimalFlow, LatticeBond.source, LatticeBond.target,
      mem_latticeRectangle]

private theorem rectangleFlowBottomVertical_zero
    (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
    (k : ℕ) :
    rectangleFlowV a w h F (rectangleFlowX a (k : ℤ))
      (rectangleFlowY a ((0 : ℤ) - 1)) = 0 := by
  simp [rectangleFlowV, rectangleFlowX, rectangleFlowY,
    rectangleExtendedPrimalFlow, LatticeBond.source, LatticeBond.target,
    mem_latticeRectangle]

theorem rectangleFlow_rowCutSum_zero
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (m : ℕ) (hm : m < h) :
    rectangleFlowRowSumV a w h F.1 w m = 0 := by
  have hrow (j : ℕ) (hj : j ≤ h) : rectangleFlowRowSumV a w h F.1 w j = 0 := by
    induction j with
    | zero =>
        have hd := rectangleFlowRowDiff_sum a w h F w 0 (by omega) (by omega)
        have hs := rectangleFlowSideHorizontal_zero a w h F.1 0
        have hb := rectangleFlowBottomVertical_zero a w h F.1
        have hlower : (∑ k ∈ Finset.range (w + 1),
            rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ))
              (rectangleFlowY a ((0 : ℤ) - 1))) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          simpa using hb k
        have hdiff : rectangleFlowRowSumV a w h F.1 w 0 = 0 := by
          rw [hs.1, hs.2] at hd
          have heq := hd
          rw [Finset.sum_sub_distrib] at heq
          simp only [Nat.cast_zero] at heq hlower
          rw [hlower] at heq
          simpa [rectangleFlowRowSumV] using heq
        exact hdiff
    | succ j ih =>
        have hd := rectangleFlowRowDiff_sum a w h F w (j + 1) (by omega) hj
        have hs := rectangleFlowSideHorizontal_zero a w h F.1 (j + 1)
        have hdiff :
            rectangleFlowRowSumV a w h F.1 w (j + 1) -
              rectangleFlowRowSumV a w h F.1 w j = 0 := by
          have hh := hd
          rw [hs.1, hs.2] at hh
          rw [Finset.sum_sub_distrib] at hh
          simpa [rectangleFlowRowSumV] using hh
        have hnext := ih (by omega)
        linarith
  exact hrow m (Nat.le_of_lt hm)

private theorem rectangleFlowVerticalTop_zero
    (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
    (n : ℕ) :
    rectangleFlowV a w h F (rectangleFlowX a (n : ℤ))
      (rectangleFlowY a (h : ℤ)) = 0 := by
  simp [rectangleFlowV, rectangleFlowX, rectangleFlowY,
    rectangleExtendedPrimalFlow, LatticeBond.source, LatticeBond.target,
    mem_latticeRectangle]

private theorem rectangleFlowRowSumV_top_zero
    (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
    (n : ℕ) : rectangleFlowRowSumV a w h F n h = 0 := by
  unfold rectangleFlowRowSumV
  apply Finset.sum_eq_zero
  intro k hk
  exact rectangleFlowVerticalTop_zero a w h F k

def rectangleFlowPotentialValue (a : LatticeVertex) (w h : ℕ)
    (F : RectangleDivergenceFreeFlow a w h) (z : LatticeVertex) : ℝ :=
  if _hz : z ∈ rectangleDualInterior a w h then
    -(∑ k ∈ Finset.range ((z.1 - a.1).toNat + 1),
      rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ)) z.2)
  else 0

noncomputable def rectangleFlowExteriorPotential
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h) :
    RectangleExteriorPotential a w h := by
  refine ⟨fun z => rectangleFlowPotentialValue a w h F z.1, ?_⟩
  intro z hz
  simp only [rectangleDualBoundary, Finset.mem_filter] at hz
  simp [rectangleFlowPotentialValue, hz.2]

private theorem rectangleFlowExtendedPotential_eq_value
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (z : LatticeVertex) (hz : z ∈ rectangleDualExpanded a w h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F) z =
      rectangleFlowPotentialValue a w h F z := by
  rw [rectangleExtendedPotential_of_mem _ _ _ _ _ hz]
  rfl

private theorem rectangleFlowPotentialLeftBoundary
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (m : ℕ) (hm : m ≤ h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (-1) (m : ℤ)) = 0 := by
  have hex : rectangleFlowVertex a (-1) (m : ℤ) ∈ rectangleDualExpanded a w h := by
    rw [rectangleDualExpanded, mem_latticeRectangle]
    simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
    omega
  rw [rectangleFlowExtendedPotential_eq_value a w h F _ hex]
  have hout : rectangleFlowVertex a (-1) (m : ℤ) ∉ rectangleDualInterior a w h := by
    intro hz
    have hx := (Finset.mem_filter.mp hz).2.1
    simp [rectangleFlowVertex, rectangleFlowX] at hx
  simp [rectangleFlowPotentialValue, hout]

private theorem rectangleFlowPotentialBottomBoundary
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (n : ℕ) (hn : n ≤ w) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) (-1)) = 0 := by
  have hex : rectangleFlowVertex a (n : ℤ) (-1) ∈ rectangleDualExpanded a w h := by
    rw [rectangleDualExpanded, mem_latticeRectangle]
    simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
    omega
  rw [rectangleFlowExtendedPotential_eq_value a w h F _ hex]
  have hout : rectangleFlowVertex a (n : ℤ) (-1) ∉ rectangleDualInterior a w h := by
    intro hz
    have hy := (Finset.mem_filter.mp hz).2.2.2.1
    simp [rectangleFlowVertex, rectangleFlowY] at hy
  simp [rectangleFlowPotentialValue, hout]

private theorem rectangleFlowPotentialValue_interior
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (n m : ℕ) (hn : n < w) (hm : m < h) :
    rectangleFlowPotentialValue a w h F
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
        -rectangleFlowRowSumV a w h F.1 n m := by
  have hex : rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ rectangleDualExpanded a w h := by
    rw [rectangleDualExpanded, mem_latticeRectangle]
    simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
    omega
  have hi : rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ rectangleDualInterior a w h := by
    apply Finset.mem_filter.mpr
    refine ⟨hex, ?_⟩
    simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
    omega
  have hx :
      ((rectangleFlowVertex a (n : ℤ) (m : ℤ)).1 - a.1).toNat = n := by
    change (a.1 + (n : ℤ) - a.1).toNat = n
    have heq : a.1 + (n : ℤ) - a.1 = (n : ℤ) := by ring
    rw [heq]
    simp
  rw [rectangleFlowPotentialValue, dite_eq_left hi, hx]
  simp [rectangleFlowRowSumV, rectangleFlowY, rectangleFlowVertex]

private theorem rectangleFlowVertex_mem_interior_iff
    (a : LatticeVertex) (w h : ℕ) (n m : ℕ) :
    rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ rectangleDualInterior a w h ↔
      n < w ∧ m < h := by
  simp [rectangleDualInterior, rectangleDualExpanded, latticeRectangle,
    rectangleFlowVertex, rectangleFlowX, rectangleFlowY, Finset.mem_filter,
    Finset.mem_product, Finset.mem_Icc]
  omega

private theorem rectangleFlowPotentialValue_face
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (n m : ℕ) :
    rectangleFlowPotentialValue a w h F
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
      if n < w ∧ m < h then -rectangleFlowRowSumV a w h F.1 n m else 0 := by
  have hi := rectangleFlowVertex_mem_interior_iff a w h n m
  by_cases hnm : n < w ∧ m < h
  · rw [ite_eq_left hnm]
    exact rectangleFlowPotentialValue_interior a w h F n m hnm.1 hnm.2
  · rw [ite_eq_right hnm]
    have hout : rectangleFlowVertex a (n : ℤ) (m : ℤ) ∉ rectangleDualInterior a w h :=
      fun hz => hnm (hi.mp hz)
    simp [rectangleFlowPotentialValue, hout]

private theorem rectangleFlowPotentialAtOffset
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (n m : ℕ) (hn : n ≤ w) (hm : m ≤ h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
        if n < w ∧ m < h then -rectangleFlowRowSumV a w h F.1 n m else 0 := by
  have hex : rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ rectangleDualExpanded a w h := by
    rw [rectangleDualExpanded, mem_latticeRectangle]
    simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
    omega
  rw [rectangleFlowExtendedPotential_eq_value a w h F _ hex]
  exact rectangleFlowPotentialValue_face a w h F n m

private theorem rectangleFlowPotentialAtOffset_eq_neg_rowSum
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (n m : ℕ) (hn : n < w) (hm : m ≤ h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
      -rectangleFlowRowSumV a w h F.1 n m := by
  rw [rectangleFlowPotentialAtOffset a w h F n m (Nat.le_of_lt hn) hm]
  by_cases hm' : m < h
  · simp [hn, hm']
  · have hmh : m = h := by omega
    subst m
    simp [hn, rectangleFlowRowSumV_top_zero]

private theorem rectangleFlowPotentialAtOffset_right_zero
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (m : ℕ) (hm : m < h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (w : ℤ) (m : ℤ)) = 0 := by
  rw [rectangleFlowPotentialAtOffset a w h F w m le_rfl (Nat.le_of_lt hm)]
  simp [hm]

private theorem rectangleFlowRowSumV_succ
    (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
    (n m : ℕ) :
    rectangleFlowRowSumV a w h F (n + 1) m =
      rectangleFlowRowSumV a w h F n m +
        rectangleFlowV a w h F (rectangleFlowX a ((n + 1 : ℕ) : ℤ))
          (rectangleFlowY a (m : ℤ)) := by
  simp [rectangleFlowRowSumV, Finset.sum_range_succ]

private theorem rectangleFlowHorizontalOffset_recovery
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (n m : ℕ) (hn : n < w) (hm : m ≤ h) :
    rectangleCurlFlow a w h (rectangleFlowExteriorPotential a w h F)
        ⟨rectangleFlowVertex a (n : ℤ) (m : ℤ), LatticeAxis.horizontal⟩ =
      rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ))
        (rectangleFlowY a (m : ℤ)) := by
  simp only [rectangleCurlFlow, LatticeBond.faceBase]
  have hface :
      ((rectangleFlowVertex a (n : ℤ) (m : ℤ)).1,
        (rectangleFlowVertex a (n : ℤ) (m : ℤ)).2 - 1) =
      rectangleFlowVertex a (n : ℤ) ((m : ℤ) - 1) := by
    ext <;> simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]; ring
  rw [hface]
  change rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) -
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) ((m : ℤ) - 1)) = _
  by_cases hm0 : m = 0
  · subst m
    rw [rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n 0 hn (by omega)]
    have hbot := rectangleFlowPotentialBottomBoundary a w h F n (by omega)
    have hbot' : rectangleExtendedPotential a w h
        (rectangleFlowExteriorPotential a w h F)
        (rectangleFlowVertex a (n : ℤ) ((0 : ℤ) - 1)) = 0 := by
      simpa using hbot
    simp only [Nat.cast_zero]
    rw [hbot']
    have hd := rectangleFlowRowDiff_sum a w h F n 0 (by omega) (by omega)
    have hs := rectangleFlowSideHorizontal_zero a w h F.1 0
    rw [hs.1] at hd
    change (∑ k ∈ Finset.range (n + 1),
      (rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ)) (rectangleFlowY a 0) -
        rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ)) (rectangleFlowY a (-1)))) =
      0 - rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a 0) at hd
    have hbot : (∑ k ∈ Finset.range (n + 1),
        rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ))
          (rectangleFlowY a ((0 : ℤ) - 1))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact rectangleFlowBottomVertical_zero a w h F.1 k
    have hbot' : (∑ k ∈ Finset.range (n + 1),
        rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ))
          (rectangleFlowY a (-1 : ℤ))) = 0 := by
      simpa [rectangleFlowY] using hbot
    rw [Finset.sum_sub_distrib] at hd
    rw [hbot'] at hd
    have hrec : rectangleFlowRowSumV a w h F.1 n 0 =
        -rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ))
          (rectangleFlowY a (0 : ℤ)) := by
      simpa [rectangleFlowRowSumV] using hd
    change -rectangleFlowRowSumV a w h F.1 n 0 - 0 =
      rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ))
        (rectangleFlowY a (0 : ℤ))
    linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    rw [rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n (m + 1) hn hm]
    have hlow := rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n m hn (by omega)
    have hpred : ((m.succ : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
    have hlow' : rectangleExtendedPotential a w h
        (rectangleFlowExteriorPotential a w h F)
        (rectangleFlowVertex a (n : ℤ) (((m.succ : ℕ) : ℤ) - 1)) =
          -rectangleFlowRowSumV a w h F.1 n m := by
      simpa [hpred] using hlow
    rw [hlow']
    have hd := rectangleFlowRowDiff_sum a w h F n (m + 1) (by omega) hm
    have hs := rectangleFlowSideHorizontal_zero a w h F.1 (m + 1)
    rw [hs.1] at hd
    rw [hpred] at hd
    change (∑ k ∈ Finset.range (n + 1),
      (rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ))
          (rectangleFlowY a ((m + 1 : ℕ) : ℤ)) -
        rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ))
          (rectangleFlowY a (m : ℤ)))) =
      0 - rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ))
        (rectangleFlowY a ((m + 1 : ℕ) : ℤ)) at hd
    simp only [Nat.cast_add, Nat.cast_one] at hd
    have hrec : rectangleFlowRowSumV a w h F.1 n (m + 1) -
        rectangleFlowRowSumV a w h F.1 n m =
        -rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ))
          (rectangleFlowY a ((m + 1 : ℕ) : ℤ)) := by
      simpa [rectangleFlowRowSumV, Finset.sum_sub_distrib, rectangleFlowY] using hd
    change -rectangleFlowRowSumV a w h F.1 n (m + 1) -
        -rectangleFlowRowSumV a w h F.1 n m =
        rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ))
          (rectangleFlowY a (m.succ : ℤ))
    linarith

private theorem rectangleFlowVerticalOffset_recovery
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (n m : ℕ) (hn : n ≤ w) (hm : m < h) :
    rectangleCurlFlow a w h (rectangleFlowExteriorPotential a w h F)
        ⟨rectangleFlowVertex a (n : ℤ) (m : ℤ), LatticeAxis.vertical⟩ =
      rectangleFlowV a w h F.1 (rectangleFlowX a (n : ℤ))
        (rectangleFlowY a (m : ℤ)) := by
  simp only [rectangleCurlFlow, LatticeBond.faceBase]
  have hface :
      ((rectangleFlowVertex a (n : ℤ) (m : ℤ)).1 - 1,
        (rectangleFlowVertex a (n : ℤ) (m : ℤ)).2) =
      rectangleFlowVertex a ((n : ℤ) - 1) (m : ℤ) := by
    ext <;> simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]; ring
  rw [hface]
  change rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a ((n : ℤ) - 1) (m : ℤ)) -
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) = _
  by_cases hn0 : n = 0
  · subst n
    have hleftcoord : rectangleFlowVertex a (((0 : ℕ) : ℤ) - 1) (m : ℤ) =
        rectangleFlowVertex a (-1) (m : ℤ) := by
      simp [rectangleFlowVertex, rectangleFlowX]
    rw [hleftcoord]
    rw [rectangleFlowPotentialLeftBoundary a w h F m (by omega)]
    by_cases hw0 : w = 0
    · subst w
      rw [rectangleFlowPotentialAtOffset_right_zero a 0 h F m hm]
      have hrow := rectangleFlow_rowCutSum_zero a 0 h F m hm
      have hval : rectangleFlowV a 0 h F.1 (rectangleFlowX a 0)
          (rectangleFlowY a (m : ℤ)) = 0 := by
        simpa [rectangleFlowRowSumV, rectangleFlowX, rectangleFlowY] using hrow
      change 0 - 0 = rectangleFlowV a 0 h F.1 (rectangleFlowX a 0)
          (rectangleFlowY a (m : ℤ))
      rw [hval]
      ring_nf
    · have hpot := rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F 0 m
        (by omega) (by omega)
      rw [hpot]
      have hrow : rectangleFlowRowSumV a w h F.1 0 m =
          rectangleFlowV a w h F.1 (rectangleFlowX a 0) (rectangleFlowY a (m : ℤ)) := by
        simp [rectangleFlowRowSumV]
      rw [hrow]
      ring
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hleftcoord : rectangleFlowVertex a (((n' + 1 : ℕ) : ℤ) - 1) (m : ℤ) =
        rectangleFlowVertex a (n' : ℤ) (m : ℤ) := by
      congr 1; simp
    rw [hleftcoord]
    have hleft := rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n' m
      (by omega) (by omega)
    have hrightPot : rectangleExtendedPotential a w h
        (rectangleFlowExteriorPotential a w h F)
        (rectangleFlowVertex a (n'.succ : ℤ) (m : ℤ)) =
          -rectangleFlowRowSumV a w h F.1 n'.succ m := by
      by_cases hright : n'.succ < w
      · simpa [Nat.succ_eq_add_one] using
          rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n'.succ m hright (by omega)
      · have hrightEq : n'.succ = w := by omega
        have hrowzero := rectangleFlow_rowCutSum_zero a w h F m hm
        have hrowzero' : rectangleFlowRowSumV a w h F.1 n'.succ m = 0 := by
          rw [hrightEq]
          exact hrowzero
        rw [hrightEq]
        rw [rectangleFlowPotentialAtOffset_right_zero a w h F m hm]
        simp [hrowzero]
    rw [hleft, hrightPot]
    have hrec := rectangleFlowRowSumV_succ a w h F.1 n' m
    have hrec' : rectangleFlowRowSumV a w h F.1 n'.succ m =
        rectangleFlowRowSumV a w h F.1 n' m +
          rectangleFlowV a w h F.1 (rectangleFlowX a (n'.succ : ℤ))
            (rectangleFlowY a (m : ℤ)) := by
      simpa [Nat.succ_eq_add_one] using hrec
    linarith

/-- Every genuinely divergence-free rectangle flow is the curl of its normalized
zero-exterior dual potential on each actual rectangle edge. -/
theorem rectangleFlowExteriorPotential_curl_eq_flow
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (b : RectanglePrimalBond a w h) :
    rectangleCurlFlow a w h (rectangleFlowExteriorPotential a w h F) b.1 = F.1 b := by
  rcases b with ⟨⟨⟨x, y⟩, axis⟩, hb⟩
  cases axis
  · have hs := (mem_latticeRectangle a (x,y) w h).mp hb.1
    have ht := (mem_latticeRectangle a (x+1,y) w h).mp hb.2
    let n : ℕ := (x - a.1).toNat
    let m : ℕ := (y - a.2).toNat
    have hxnonneg : 0 ≤ x - a.1 := by omega
    have hynonneg : 0 ≤ y - a.2 := by omega
    have hx : x = a.1 + (n : ℤ) := by
      dsimp [n]
      rw [Int.toNat_of_nonneg hxnonneg]
      omega
    have hy : y = a.2 + (m : ℤ) := by
      dsimp [m]
      rw [Int.toNat_of_nonneg hynonneg]
      omega
    have hn : n < w := by omega
    have hm : m ≤ h := by omega
    have hcoords : (x,y) = rectangleFlowVertex a (n : ℤ) (m : ℤ) := by
      ext <;> simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY, hx, hy]
    have hinside :
        (⟨(a.1 + (n : ℤ), a.2 + (m : ℤ)), LatticeAxis.horizontal⟩ : LatticeBond).source ∈
            latticeRectangle a w h ∧
          (⟨(a.1 + (n : ℤ), a.2 + (m : ℤ)), LatticeAxis.horizontal⟩ : LatticeBond).target ∈
            latticeRectangle a w h := by
      simpa [hx, hy, LatticeBond.source, LatticeBond.target] using hb
    have hrec := rectangleFlowHorizontalOffset_recovery a w h F n m hn hm
    rw [← hcoords] at hrec
    simpa [rectangleFlowH, rectangleExtendedPrimalFlow, rectangleFlowX,
      rectangleFlowY, hx, hy, hinside] using hrec
  · have hs := (mem_latticeRectangle a (x,y) w h).mp hb.1
    have ht := (mem_latticeRectangle a (x,y+1) w h).mp hb.2
    let n : ℕ := (x - a.1).toNat
    let m : ℕ := (y - a.2).toNat
    have hxnonneg : 0 ≤ x - a.1 := by omega
    have hynonneg : 0 ≤ y - a.2 := by omega
    have hx : x = a.1 + (n : ℤ) := by
      dsimp [n]
      rw [Int.toNat_of_nonneg hxnonneg]
      omega
    have hy : y = a.2 + (m : ℤ) := by
      dsimp [m]
      rw [Int.toNat_of_nonneg hynonneg]
      omega
    have hn : n ≤ w := by omega
    have hm : m < h := by omega
    have hcoords : (x,y) = rectangleFlowVertex a (n : ℤ) (m : ℤ) := by
      ext <;> simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY, hx, hy]
    have hinside :
        (⟨(a.1 + (n : ℤ), a.2 + (m : ℤ)), LatticeAxis.vertical⟩ : LatticeBond).source ∈
            latticeRectangle a w h ∧
          (⟨(a.1 + (n : ℤ), a.2 + (m : ℤ)), LatticeAxis.vertical⟩ : LatticeBond).target ∈
            latticeRectangle a w h := by
      simpa [hx, hy, LatticeBond.source, LatticeBond.target] using hb
    have hrec := rectangleFlowVerticalOffset_recovery a w h F n m hn hm
    rw [← hcoords] at hrec
    simpa [rectangleFlowV, rectangleExtendedPrimalFlow, rectangleFlowX,
      rectangleFlowY, hx, hy, hinside] using hrec

end PottsDiscontinuity.FK
