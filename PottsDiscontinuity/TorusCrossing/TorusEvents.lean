module

public import PottsDiscontinuity.TorusCrossing.Fiber
public import PottsDiscontinuity.TorusCrossing.Ivt
public import PottsDiscontinuity.TorusCrossing.TorusDict
public import PottsDiscontinuity.TorusRC.CrossingContracts

/-!
# Torus crossing events seen from a board

Conversion of cell-level open paths of a board (for the primal configuration, and for the
complementary translated configuration) into walks of the lifted strip graph of the torus.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open PottsDiscontinuity.TorusRC Torus CorrLength
open scoped Classical

variable {N M : ℕ}

/-- Vertical lifted crossing of the rows `[b, b + n]` inside the columns `[a, a + 3n]`. -/
def vCross (hNp : 0 < N) (hMp : 0 < M) (n : ℕ) (a b : ℤ) (A : RCConfig N M) : Prop :=
  ∃ u v : RotatedVertex, u.val.2 = b ∧ v.val.2 = b + n ∧
    ∃ w : (liftedStripGraph hNp hMp A a (a + 3 * (n : ℤ))).Walk u v,
      ∀ z ∈ w.support, b ≤ z.val.2 ∧ z.val.2 ≤ b + n

theorem vCross_zero_iff (hNp : 0 < N) (hMp : 0 < M) (n : ℕ) (A : RCConfig N M) :
    vCross hNp hMp n 0 0 A ↔ torusRCVerticalRectangleCrossing hNp hMp n A := by
  have h3 : (0 : ℤ) + 3 * (n : ℤ) = 3 * (n : ℤ) := zero_add _
  unfold vCross torusRCVerticalRectangleCrossing
  rw [h3]
  simp only [zero_add]

theorem rtg_to_walk {α : Type*} (G : SimpleGraph α) (P : α → Prop) (S : α → α → Prop)
    (hS : ∀ p q, S p q → G.Adj p q ∧ P p ∧ P q) {x y : α}
    (h : Relation.ReflTransGen S x y) (hx : P x) :
    ∃ w : G.Walk x y, ∀ z ∈ w.support, P z := by
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

theorem rtg_lift_primal {S : Finset Cell} (Φ : Cell → Prop) {x y : Cell}
    (h : Relation.ReflTransGen (fun p q => StepRel primalEnds S p q ∧ Φ p ∧ Φ q) x y)
    (hx : IsPrimal x) :
    ∃ hy : IsPrimal y, Relation.ReflTransGen
      (fun u v : RotatedVertex => StepRel primalEnds S u.1 v.1 ∧ Φ u.1 ∧ Φ v.1)
      (toRV x hx) (toRV y hy) := by
  induction h with
  | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hr⟩ := ih
    obtain ⟨hstep, hΦb, hΦc⟩ := hbc
    obtain ⟨m, hm, hmeq⟩ := hstep
    have hc : IsPrimal c := by
      rcases hmeq with h | h
      · have h2 : c = (primalEnds m).2 := (congrArg Prod.snd h).symm
        rw [h2]; exact primalEnds_snd_primal m
      · have h2 : c = (primalEnds m).1 := (congrArg Prod.fst h).symm
        rw [h2]; exact primalEnds_fst_primal m
    exact ⟨hc, hr.tail ⟨⟨m, hm, hmeq⟩, hΦb, hΦc⟩⟩

theorem primal_step_row {S : Finset Cell} {p q : Cell} (h : StepRel primalEnds S p q) :
    q.2 ≤ p.2 + 1 ∧ p.2 ≤ q.2 + 1 := by
  obtain ⟨m, _, h⟩ := h
  rcases h with h | h
  · have h1 := congrArg (fun z : Cell × Cell => z.1.2) h
    have h2 := congrArg (fun z : Cell × Cell => z.2.2) h
    simp only [Rect.primalEnds_fst_row, Rect.primalEnds_snd_row] at h1 h2
    omega
  · have h1 := congrArg (fun z : Cell × Cell => z.1.2) h
    have h2 := congrArg (fun z : Cell × Cell => z.2.2) h
    simp only [Rect.primalEnds_fst_row, Rect.primalEnds_snd_row] at h1 h2
    omega

theorem adj_oriented (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) (a b : ℤ)
    (hcol : a ≤ Q.x0 ∧ Q.x0 + Q.w ≤ b) {m : Cell} (hm : m ∈ boardOf Q hNp hMp A) :
    (liftedStripGraph hNp hMp A a b).Adj (toRV (primalEnds m).1 (primalEnds_fst_primal m))
      (toRV (primalEnds m).2 (primalEnds_snd_primal m)) := by
  obtain ⟨hmin, hmA⟩ := Finset.mem_filter.1 hm
  have hd := Q.pData.mem m hmin
  have h1 := Rect.mem_cells.1 (Rect.mem_pcells.1 hd.1).1
  have h2 := Rect.mem_cells.1 (Rect.mem_pcells.1 hd.2).1
  refine ⟨rotAdj_primalEnds m, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [liftedEdgeIndex_primalEnds]; exact hmA
  · change a ≤ (primalEnds m).1.1; omega
  · change (primalEnds m).1.1 ≤ b; omega
  · change a ≤ (primalEnds m).2.1; omega
  · change (primalEnds m).2.1 ≤ b; omega

theorem lifted_adj_of_step (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) (a b : ℤ)
    (hcol : a ≤ Q.x0 ∧ Q.x0 + Q.w ≤ b) {S : Finset Cell} (hS : S ⊆ boardOf Q hNp hMp A)
    {u v : RotatedVertex} (h : StepRel primalEnds S u.1 v.1) :
    (liftedStripGraph hNp hMp A a b).Adj u v := by
  obtain ⟨m, hm, hmeq⟩ := h
  have hu1 : u.1 = (primalEnds m).1 ∨ u.1 = (primalEnds m).2 := by
    rcases hmeq with h | h
    · exact Or.inl (congrArg Prod.fst h).symm
    · exact Or.inr (congrArg Prod.snd h).symm
  rcases hmeq with h | h
  · have hu : u = toRV (primalEnds m).1 (primalEnds_fst_primal m) :=
      Subtype.ext (congrArg Prod.fst h).symm
    have hv : v = toRV (primalEnds m).2 (primalEnds_snd_primal m) :=
      Subtype.ext (congrArg Prod.snd h).symm
    rw [hu, hv]
    exact adj_oriented hNp hMp Q A a b hcol (hS hm)
  · have hu : u = toRV (primalEnds m).2 (primalEnds_snd_primal m) :=
      Subtype.ext (congrArg Prod.snd h).symm
    have hv : v = toRV (primalEnds m).1 (primalEnds_fst_primal m) :=
      Subtype.ext (congrArg Prod.fst h).symm
    rw [hu, hv]
    exact (adj_oriented hNp hMp Q A a b hcol (hS hm)).symm

theorem isPrimal_of_step {S : Finset Cell} {x c : Cell} (h : StepRel primalEnds S x c) :
    IsPrimal x := by
  obtain ⟨m, _, h⟩ := h
  rcases h with h | h
  · have h2 : x = (primalEnds m).1 := (congrArg Prod.fst h).symm
    rw [h2]; exact primalEnds_fst_primal m
  · have h2 : x = (primalEnds m).2 := (congrArg Prod.snd h).symm
    rw [h2]; exact primalEnds_snd_primal m

/-- A crossing of the board between the two exploration zones gives a lifted vertical crossing of
rows `[ρ, ρ + n]` in the columns `[a, a + 3n]` containing the board. -/
theorem cross_to_vCross (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) {bB bT : ℕ}
    (n : ℕ) (hn : 0 < n) (a ρ : ℤ) (hcol : a ≤ Q.x0 ∧ Q.x0 + Q.w ≤ a + 3 * (n : ℤ))
    (hρ1 : Q.y0 + bB - 1 ≤ ρ) (hρ2 : ρ + n ≤ Q.y0 + Q.h - bT + 1)
    (hc : Q.crossEv bB bT (boardOf Q hNp hMp A)) : vCross hNp hMp n a ρ A := by
  obtain ⟨u, v, hu, hv, hpath⟩ := hc
  obtain ⟨x, y, hx, hy, hxy⟩ := ivt_path (StepRel primalEnds (boardOf Q hNp hMp A))
    (fun c : Cell => c.2) (fun p q h => primal_step_row h) ρ n hpath (by omega) (by omega)
  have hxy' : Relation.ReflTransGen
      (fun p q => StepRel primalEnds (boardOf Q hNp hMp A) p q ∧
        (ρ ≤ p.2 ∧ p.2 ≤ ρ + n) ∧ (ρ ≤ q.2 ∧ q.2 ≤ ρ + n)) x y :=
    Relation.ReflTransGen.mono (fun p q h => ⟨h.1, ⟨h.2.1, h.2.2.1⟩, ⟨h.2.2.2.1, h.2.2.2.2⟩⟩) x y hxy
  have hxp : IsPrimal x := by
    rcases Relation.ReflTransGen.cases_head hxy' with h | ⟨c, hc, _⟩
    · exfalso
      subst h
      omega
    · exact isPrimal_of_step hc.1
  obtain ⟨hyp, hlift⟩ := rtg_lift_primal (S := boardOf Q hNp hMp A)
    (fun c : Cell => ρ ≤ c.2 ∧ c.2 ≤ ρ + n) hxy' hxp
  obtain ⟨w, hw⟩ := rtg_to_walk (liftedStripGraph hNp hMp A a (a + 3 * (n : ℤ)))
    (fun z : RotatedVertex => ρ ≤ z.val.2 ∧ z.val.2 ≤ ρ + n)
    (fun u v : RotatedVertex => StepRel primalEnds (boardOf Q hNp hMp A) u.1 v.1 ∧
      (ρ ≤ u.1.2 ∧ u.1.2 ≤ ρ + n) ∧ (ρ ≤ v.1.2 ∧ v.1.2 ≤ ρ + n))
    (fun p q h => ⟨lifted_adj_of_step hNp hMp Q A a (a + 3 * (n : ℤ)) hcol (subset_refl _) h.1,
      h.2.1, h.2.2⟩) hlift ⟨by simp only [toRV]; omega, by simp only [toRV]; omega⟩
  exact ⟨toRV x hxp, toRV y hyp, by simpa [toRV] using hx, by simpa [toRV] using hy, w, hw⟩

end PottsDiscontinuity.TorusCrossing
