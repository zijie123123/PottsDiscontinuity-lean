module

public import PottsDiscontinuity.Duality.RectanglePathIntersection
public import PottsDiscontinuity.TorusRC.CylinderEvents
public import PottsDiscontinuity.TorusRC.DualPathSeparation
public import PottsDiscontinuity.TorusRC.WindingClosure
public import PottsDiscontinuity.TorusRC.WindingPeriods

/-! # A genuine dual vertical winding blocks primal strip crossings -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength TorusTopology SixVertex

variable {N M : ℕ}

private theorem stripWalk_horizontal (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b : ℤ) {u v : RotatedVertex}
    (p : (liftedStripGraph hNp hMp A a b).Walk u v) :
    (a ≤ u.val.1 ∧ u.val.1 ≤ b) → ∀ z ∈ p.support, a ≤ z.val.1 ∧ z.val.1 ≤ b := by
  induction p with
  | nil =>
    intro hu z hz
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hz
    subst z
    exact hu
  | @cons u v z hadj p ih =>
    intro hu w hw
    simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hu
    · exact ih hadj.2.2.2 w hw

/-- A vertical primal period in A, shifted into the odd cells of its
complementary translated dual, blocks every left-to-right crossing. The
one-unit horizontal margin accounts for the exact dual translation. -/
theorem winding_blocks_dual_strip_crossing (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M)
    (K n : ℕ) (hmargin : K+1 ≤ 3*n) (x : ℤ) (hx : Even x)
    (hx0 : 0 ≤ x) (hxK : x ≤ K)
    (hpath : liftedBoundedConnection hNp hMp A 0 K 0 M
      (liftedColumnSite x 0 hx ⟨0,rfl⟩)
      (liftedColumnSite x M hx (by exact_mod_cast hM))) :
    ¬ torusRCLeftStripCrossing hNp hMp (translatedDualConfig A) n := by
  rintro ⟨u,v,hu,hv,⟨p⟩⟩
  obtain ⟨L,hL⟩ := walk_between_periods hMp p
  have hrepeat := winding_path_repeat hM hNp hMp A 0 K x hx hpath (-(L:ℤ)) (2*L)
  have hupper : -(L:ℤ)+((2*L:ℕ):ℤ) = L := by push_cast; ring
  have hlower : (M:ℤ)*(-(L:ℤ)) = -(M:ℤ)*L := by ring
  rw [hupper,hlower] at hrepeat
  obtain ⟨q,hq⟩ := hrepeat
  let f : RotatedVertex → ℝ × ℝ := fun z => cellEmbed z.val
  let g : RotatedVertex → ℝ × ℝ := fun z => cellEmbed (dualShiftCell z)
  let P := polygonWalkPath f p
  let Q := polygonWalkPath g q
  let a : ℝ × ℝ := (0,(-(M:ℤ)*L:ℤ))
  let b : ℝ × ℝ := (((3*n:ℕ):ℝ), (((M:ℤ)*(L:ℤ):ℤ):ℝ))
  have hpX := stripWalk_horizontal hNp hMp (translatedDualConfig A) 0 ((3*n:ℕ):ℤ) p
    ⟨by omega,by omega⟩
  have hqX := stripWalk_horizontal hNp hMp A 0 K q ⟨hx0,hxK⟩
  have hPbox : ∀ t, a.1 ≤ (P t).1 ∧ (P t).1 ≤ b.1 ∧
      a.2 ≤ (P t).2 ∧ (P t).2 ≤ b.2 := by
    intro t
    have h := polygonWalkPath_mem_Icc f p a b (fun z hz => by
      have hX := hpX z hz
      have hY := hL z hz
      dsimp only [f,g,cellEmbed,dualShiftCell,a,b,Prod.fst,Prod.snd]
      constructor <;> constructor <;> simp only
      · exact_mod_cast hX.1
      · exact_mod_cast hY.1
      · exact_mod_cast hX.2
      · exact_mod_cast hY.2) t
    exact ⟨h.1.1,h.2.1,h.1.2,h.2.2⟩
  have hQbox : ∀ t, a.1 ≤ (Q t).1 ∧ (Q t).1 ≤ b.1 ∧
      a.2 ≤ (Q t).2 ∧ (Q t).2 ≤ b.2 := by
    intro t
    have h := polygonWalkPath_mem_Icc g q a b (fun z hz => by
      have hX := hqX z hz
      have hY := hq z hz
      dsimp only [f,g,cellEmbed,dualShiftCell,a,b,Prod.fst,Prod.snd]
      constructor <;> constructor <;> simp only
      · exact_mod_cast (show (0:ℤ) ≤ z.val.1+1 by omega)
      · exact_mod_cast hY.1
      · exact_mod_cast (show z.val.1+1 ≤ ((3*n:ℕ):ℤ) by omega)
      · exact_mod_cast hY.2) t
    exact ⟨h.1.1,h.2.1,h.1.2,h.2.2⟩
  have hPleft : (P 0).1 = a.1 := by
    calc
      (P 0).1 = (f u).1 := congrArg Prod.fst P.source'
      _ = a.1 := ?_
    change (u.val.1:ℝ) = 0
    exact_mod_cast hu
  have hPright : (P 1).1 = b.1 := by
    calc
      (P 1).1 = (f v).1 := congrArg Prod.fst P.target'
      _ = b.1 := ?_
    change (v.val.1:ℝ) = ((3*n:ℕ):ℝ)
    exact_mod_cast hv
  have hQbottom : (Q 0).2 = a.2 := by
    calc
      (Q 0).2 = (g (periodColumnSite hM x hx (-(L:ℤ)))).2 := congrArg Prod.snd Q.source'
      _ = a.2 := ?_
    change (((M:ℤ)*(-(L:ℤ)):ℤ):ℝ) = ((-(M:ℤ)*L:ℤ):ℝ)
    congr 1
  have hQtop : (Q 1).2 = b.2 := by
    calc
      (Q 1).2 = (g (periodColumnSite hM x hx (L:ℤ))).2 := congrArg Prod.snd Q.target'
      _ = b.2 := rfl
  have hheight : a.2 ≤ b.2 := by
    change ((-(M:ℤ)*L:ℤ):ℝ) ≤ (((M:ℤ)*L:ℤ):ℝ)
    have h : (0:ℤ) ≤ (M:ℤ)*L := by positivity
    have hh : -((M:ℤ)*L) ≤ (M:ℤ)*L := neg_le_self h
    rw [← neg_mul] at hh
    exact_mod_cast hh
  obtain ⟨s,t,hst⟩ := FK.Curves.pathRectangle_crossing_intersection P Q hPbox hQbox
    hPleft hPright hQbottom hQtop
  exact Set.disjoint_left.mp (opposite_open_walks_disjoint hNp hMp A 0 ((3*n:ℕ):ℤ) 0 K p q)
    ⟨s,rfl⟩ ⟨t,hst.symm⟩

/-- The actual winding-and-single-open-seam event transfers into the source
barrier B under translated complementary duality. -/
theorem primalWinding_translatedDual_mem_barrier (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (K n : ℕ) (hmargin : K+1 ≤ 3*n)
    (A : RCConfig N M) (hA : A ∈ primalWindingSingleSeam hNp hMp hM K) :
    translatedDualConfig A ∈ torusRCBarrier hNp hMp n := by
  obtain ⟨x,hx,hx0,hxK,hpath,i₀,hopen,hclosed⟩ := hA
  refine ⟨winding_blocks_dual_strip_crossing hM hNp hMp A K n hmargin x hx hx0 hxK hpath,
    nxt i₀,?_,?_⟩
  · change shiftRCConfig (dualConfig A) (nxt i₀,⟨0,hMp⟩) = false
    rw [shiftRCConfig_nxt (dualConfig A) (i₀,(⟨0,hMp⟩ : Fin M))]
    change Bool.not (A (i₀,⟨0,hMp⟩)) = false
    rw [hopen]
    rfl
  · intro i hi
    have hprv : prv i ≠ i₀ := by
      intro heq
      apply hi
      have hh := congrArg nxt heq
      simpa only [nxt,prv,Equiv.apply_symm_apply] using hh
    change Bool.not (A (prv i,⟨0,hMp⟩)) = true
    rw [hclosed (prv i) hprv]
    rfl

end PottsDiscontinuity.TorusRC
