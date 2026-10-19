module

public import PottsDiscontinuity.Torus.DiamondDualTranslation
public import PottsDiscontinuity.TorusCrossing.TorusEvents

/-!
# Failure of a barrier gives a vertical crossing of the translated dual configuration

A dual-open path of a board, joining the two port rows of a sub-board, becomes (after the
unit horizontal translation exchanging face colours) an open primal path of the translated
complementary configuration.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open PottsDiscontinuity.TorusRC Torus CorrLength PottsDiscontinuity.SixVertex
open scoped Classical

variable {N M : ℕ}

theorem periodicCoordinate_succ (hp : 0 < N) (z : ℤ) :
    periodicCoordinate hp (z + 1) = nxt (periodicCoordinate hp z) := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  apply Fin.ext
  apply Int.ofNat.inj
  change ((periodicCoordinate hp (z + 1)).val : ℤ) =
    ((finRotate (N' + 1) (periodicCoordinate hp z)).val : ℤ)
  rw [finRotate_apply, periodicCoordinate_val, Fin.val_add]
  push_cast
  rw [periodicCoordinate_val]
  rw [Int.add_emod z 1]
  push_cast
  rfl

theorem translatedDual_at (A : RCConfig N M) (hNp : 0 < N) (hMp : 0 < M) (i j : ℤ) :
    translatedDualConfig A (periodicCoordinate hNp (i + 1), periodicCoordinate hMp j) =
      !(A (periodicCoordinate hNp i, periodicCoordinate hMp j)) := by
  rw [periodicCoordinate_succ]
  have := shiftRCConfig_nxt (dualConfig A) (periodicCoordinate hNp i, periodicCoordinate hMp j)
  exact this

theorem dualEnds_fst_row (m : Cell) : (dualEnds m).1.2 = m.2 := by
  unfold dualEnds; split_ifs <;> rfl

theorem dualEnds_snd_row (m : Cell) : (dualEnds m).2.2 = m.2 - 1 := by
  unfold dualEnds; split_ifs <;> rfl

/-- The primal-coloured vertex obtained from a dual cell by the unit horizontal translation. -/
def toRVd (z : Cell) (hz : ¬ IsPrimal z) : RotatedVertex :=
  ⟨(z.1 + 1, z.2), by
    unfold IsPrimal at hz
    exact Int.even_iff.2 (by dsimp only; omega)⟩

theorem rotAdj_dualEnds (m : Cell) :
    rotatedLattice.Adj (toRVd (dualEnds m).1 (dualEnds_fst_not_primal m))
      (toRVd (dualEnds m).2 (dualEnds_snd_not_primal m)) := by
  unfold toRVd dualEnds
  change |_| = 1 ∧ |_| = 1
  by_cases h : (m.1 + m.2) % 2 = 0
  · simp only [h, ite_true]
    constructor <;> rw [abs_eq (by norm_num)] <;> omega
  · simp only [h, ite_false]
    constructor <;> rw [abs_eq (by norm_num)] <;> omega

theorem liftedEdgeIndex_dualEnds (hNp : 0 < N) (hMp : 0 < M) (m : Cell) :
    liftedEdgeIndex hNp hMp (toRVd (dualEnds m).1 (dualEnds_fst_not_primal m))
      (toRVd (dualEnds m).2 (dualEnds_snd_not_primal m)) =
      (periodicCoordinate hNp (m.1 + 1), periodicCoordinate hMp m.2) := by
  unfold liftedEdgeIndex toRVd dualEnds
  by_cases h : (m.1 + m.2) % 2 = 0
  · simp only [h, ite_true]
    rw [max_eq_right (by omega), max_eq_left (by omega)]
  · simp only [h, ite_false]
    rw [max_eq_left (by omega), max_eq_left (by omega)]

theorem dual_adj_oriented (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) (a b : ℤ)
    (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ b) {m : Cell} (hmin : m ∈ Q.inner)
    (hmA : m ∉ boardOf Q hNp hMp A) :
    (liftedStripGraph hNp hMp (translatedDualConfig A) a b).Adj
      (toRVd (dualEnds m).1 (dualEnds_fst_not_primal m))
      (toRVd (dualEnds m).2 (dualEnds_snd_not_primal m)) := by
  have hd := Q.dData.mem m hmin
  have h1 := Rect.mem_cells.1 (Rect.mem_dcells.1 hd.1).1
  have h2 := Rect.mem_cells.1 (Rect.mem_dcells.1 hd.2).1
  have hAm : A (periodicCoordinate hNp m.1, periodicCoordinate hMp m.2) = false := by
    by_contra hne
    apply hmA
    exact Finset.mem_filter.2 ⟨hmin, by simpa [toFin] using hne⟩
  refine ⟨rotAdj_dualEnds m, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [liftedEdgeIndex_dualEnds, translatedDual_at, hAm]; rfl
  · change a ≤ (dualEnds m).1.1 + 1; omega
  · change (dualEnds m).1.1 + 1 ≤ b; omega
  · change a ≤ (dualEnds m).2.1 + 1; omega
  · change (dualEnds m).2.1 + 1 ≤ b; omega

theorem rtg_to_walk_map {α β : Type*} (G : SimpleGraph β) (φ : α → β) (P : β → Prop)
    (S : α → α → Prop) (hS : ∀ p q, S p q → G.Adj (φ p) (φ q) ∧ P (φ p) ∧ P (φ q)) {x y : α}
    (h : Relation.ReflTransGen S x y) (hx : P (φ x)) :
    ∃ w : G.Walk (φ x) (φ y), ∀ z ∈ w.support, P z := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, by simpa using hx⟩
  | @tail b c _ hbc ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨hadj, hPb, hPc⟩ := hS b c hbc
    refine ⟨w.concat hadj, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_concat] at hz
    rcases List.mem_append.1 hz with h | h
    · exact hw z h
    · rw [List.mem_singleton.1 h]; exact hPc

theorem dual_step_row {S : Finset Cell} {p q : Cell} (h : StepRel dualEnds S p q) :
    q.2 ≤ p.2 + 1 ∧ p.2 ≤ q.2 + 1 := by
  obtain ⟨m, _, h⟩ := h
  rcases h with h | h
  · have h1 := congrArg (fun z : Cell × Cell => z.1.2) h
    have h2 := congrArg (fun z : Cell × Cell => z.2.2) h
    simp only [dualEnds_fst_row, dualEnds_snd_row] at h1 h2
    omega
  · have h1 := congrArg (fun z : Cell × Cell => z.1.2) h
    have h2 := congrArg (fun z : Cell × Cell => z.2.2) h
    simp only [dualEnds_fst_row, dualEnds_snd_row] at h1 h2
    omega

theorem notPrimal_of_dstep {S : Finset Cell} {x c : Cell} (h : StepRel dualEnds S x c) :
    ¬ IsPrimal x := by
  obtain ⟨m, _, h⟩ := h
  rcases h with h | h
  · have h2 : x = (dualEnds m).1 := (congrArg Prod.fst h).symm
    rw [h2]; exact dualEnds_fst_not_primal m
  · have h2 : x = (dualEnds m).2 := (congrArg Prod.snd h).symm
    rw [h2]; exact dualEnds_snd_not_primal m

theorem rtg_lift_dual {S : Finset Cell} (Φ : Cell → Prop) {x y : Cell}
    (h : Relation.ReflTransGen (fun p q => StepRel dualEnds S p q ∧ Φ p ∧ Φ q) x y)
    (hx : ¬ IsPrimal x) :
    ∃ hy : ¬ IsPrimal y, Relation.ReflTransGen
      (fun u v : {z : Cell // ¬ IsPrimal z} => StepRel dualEnds S u.1 v.1 ∧ Φ u.1 ∧ Φ v.1)
      ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hr⟩ := ih
    obtain ⟨hstep, hΦb, hΦc⟩ := hbc
    obtain ⟨m, hm, hmeq⟩ := hstep
    have hc : ¬ IsPrimal c := by
      rcases hmeq with h | h
      · have h2 : c = (dualEnds m).2 := (congrArg Prod.snd h).symm
        rw [h2]; exact dualEnds_snd_not_primal m
      · have h2 : c = (dualEnds m).1 := (congrArg Prod.fst h).symm
        rw [h2]; exact dualEnds_fst_not_primal m
    exact ⟨hc, hr.tail ⟨⟨m, hm, hmeq⟩, hΦb, hΦc⟩⟩

theorem dual_lifted_adj_of_step (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M)
    (a b : ℤ) (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ b) {S : Finset Cell}
    (hS : S ⊆ Q.inner) (hSA : ∀ m ∈ S, m ∉ boardOf Q hNp hMp A)
    {u v : {z : Cell // ¬ IsPrimal z}} (h : StepRel dualEnds S u.1 v.1) :
    (liftedStripGraph hNp hMp (translatedDualConfig A) a b).Adj (toRVd u.1 u.2) (toRVd v.1 v.2) := by
  obtain ⟨m, hm, hmeq⟩ := h
  rcases hmeq with h | h
  · have hu : toRVd u.1 u.2 = toRVd (dualEnds m).1 (dualEnds_fst_not_primal m) := by
      congr 1
      exact (congrArg Prod.fst h).symm
    have hv : toRVd v.1 v.2 = toRVd (dualEnds m).2 (dualEnds_snd_not_primal m) := by
      congr 1
      exact (congrArg Prod.snd h).symm
    rw [hu, hv]
    exact dual_adj_oriented hNp hMp Q A a b hcol (hS hm) (hSA m hm)
  · have hu : toRVd u.1 u.2 = toRVd (dualEnds m).2 (dualEnds_snd_not_primal m) := by
      congr 1
      exact (congrArg Prod.snd h).symm
    have hv : toRVd v.1 v.2 = toRVd (dualEnds m).1 (dualEnds_fst_not_primal m) := by
      congr 1
      exact (congrArg Prod.fst h).symm
    rw [hu, hv]
    exact (dual_adj_oriented hNp hMp Q A a b hcol (hS hm) (hSA m hm)).symm

/-- A dual-open path (avoiding the open edges of the board) joining a low face to a high face
gives a lifted vertical crossing of the translated complementary configuration. -/
theorem dual_to_vCross (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) (n : ℕ)
    (hn : 0 < n) (a ρ : ℤ) (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ a + 3 * (n : ℤ))
    {S : Finset Cell} (hS : S ⊆ Q.inner) (hSA : ∀ m ∈ S, m ∉ boardOf Q hNp hMp A) {p t : Cell}
    (hpath : Relation.ReflTransGen (StepRel dualEnds S) p t) (hp : p.2 ≤ ρ) (ht : ρ + n ≤ t.2) :
    vCross hNp hMp n a ρ (translatedDualConfig A) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ivt_path (StepRel dualEnds S) (fun c : Cell => c.2)
    (fun p q h => dual_step_row h) ρ n hpath hp ht
  have hxy' : Relation.ReflTransGen
      (fun p q => StepRel dualEnds S p q ∧ (ρ ≤ p.2 ∧ p.2 ≤ ρ + n) ∧ (ρ ≤ q.2 ∧ q.2 ≤ ρ + n)) x y :=
    Relation.ReflTransGen.mono (fun p q h => ⟨h.1, ⟨h.2.1, h.2.2.1⟩, ⟨h.2.2.2.1, h.2.2.2.2⟩⟩) x y hxy
  have hxp : ¬ IsPrimal x := by
    rcases Relation.ReflTransGen.cases_head hxy' with h | ⟨c, hc, _⟩
    · exfalso
      subst h
      omega
    · exact notPrimal_of_dstep hc.1
  obtain ⟨hyp, hlift⟩ := rtg_lift_dual (S := S) (fun c : Cell => ρ ≤ c.2 ∧ c.2 ≤ ρ + n) hxy' hxp
  obtain ⟨w, hw⟩ := rtg_to_walk_map (liftedStripGraph hNp hMp (translatedDualConfig A) a
      (a + 3 * (n : ℤ)))
    (fun u : {z : Cell // ¬ IsPrimal z} => toRVd u.1 u.2)
    (fun z : RotatedVertex => ρ ≤ z.val.2 ∧ z.val.2 ≤ ρ + n)
    (fun u v : {z : Cell // ¬ IsPrimal z} => StepRel dualEnds S u.1 v.1 ∧
      (ρ ≤ u.1.2 ∧ u.1.2 ≤ ρ + n) ∧ (ρ ≤ v.1.2 ∧ v.1.2 ≤ ρ + n))
    (fun p q h => ⟨dual_lifted_adj_of_step hNp hMp Q A a (a + 3 * (n : ℤ)) hcol hS hSA h.1,
      h.2.1, h.2.2⟩) hlift ⟨by simp only [toRVd]; omega, by simp only [toRVd]; omega⟩
  exact ⟨toRVd x hxp, toRVd y hyp, by simpa [toRVd] using hx, by simpa [toRVd] using hy, w, hw⟩

theorem rtg_stepRel_symm {ends : Cell → Cell × Cell} {S : Finset Cell} {x y : Cell}
    (h : Relation.ReflTransGen (StepRel ends S) x y) :
    Relation.ReflTransGen (StepRel ends S) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact Relation.ReflTransGen.head (stepRel_symm hbc) ih

theorem notBarB_to_vCross (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) {bB bT : ℕ}
    (hg : Q.Geo bB bT) (n : ℕ) (hn : 0 < n) (a ρ : ℤ)
    (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ a + 3 * (n : ℤ))
    (hρ1 : Q.y0 ≤ ρ) (hρ2 : ρ + n ≤ Q.y0 + bB)
    (hbar : ¬ Q.barB bB (boardOf Q hNp hMp A)) : vCross hNp hMp n a ρ (translatedDualConfig A) := by
  unfold Rect.barB at hbar
  push Not at hbar
  obtain ⟨t, ht, htD⟩ := hbar
  obtain ⟨_, p, hp, hpath⟩ := (Q.botB bB).mem_expD.1 htD
  have hp2 : p.2 = Q.y0 := ((Q.botB bB).faceRow_mem.1 hp).2
  have ht2 : t.2 = Q.y0 + bB := ((Q.botB bB).faceRow_mem.1 ht).2
  refine dual_to_vCross hNp hMp Q A n hn a ρ hcol (S := (Q.botB bB).inner \ boardOf Q hNp hMp A)
    ?_ ?_ hpath (by omega) (by omega)
  · exact Finset.sdiff_subset.trans (Rect.botB_inner_subset Q bB (by have := hg.hgap; omega))
  · intro m hm; exact (Finset.mem_sdiff.1 hm).2

theorem notBarT_to_vCross (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) {bB bT : ℕ}
    (hg : Q.Geo bB bT) (n : ℕ) (hn : 0 < n) (a ρ : ℤ)
    (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ a + 3 * (n : ℤ))
    (hρ1 : Q.y0 + Q.h - bT ≤ ρ) (hρ2 : ρ + n ≤ Q.y0 + Q.h)
    (hbar : ¬ Q.barT bT (boardOf Q hNp hMp A)) : vCross hNp hMp n a ρ (translatedDualConfig A) := by
  unfold Rect.barT at hbar
  push Not at hbar
  obtain ⟨t, ht, htD⟩ := hbar
  obtain ⟨_, p, hp, hpath⟩ := (Q.topT bT).mem_expD.1 htD
  have hp2 : p.2 = Q.y0 + Q.h := ((Q.topT bT).faceRow_mem.1 hp).2
  have ht2 : t.2 = Q.y0 + Q.h - bT := ((Q.topT bT).faceRow_mem.1 ht).2
  refine dual_to_vCross hNp hMp Q A n hn a ρ hcol (S := (Q.topT bT).inner \ boardOf Q hNp hMp A)
    ?_ ?_ (rtg_stepRel_symm hpath) (by omega) (by omega)
  · exact Finset.sdiff_subset.trans (Rect.topT_inner_subset Q bT (by have := hg.hgap; omega))
  · intro m hm; exact (Finset.mem_sdiff.1 hm).2

end PottsDiscontinuity.TorusCrossing
