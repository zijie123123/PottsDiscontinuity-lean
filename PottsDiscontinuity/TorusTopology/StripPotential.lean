module

public import PottsDiscontinuity.TorusTopology.StripCover
public import PottsDiscontinuity.Torus.DiamondSeamWinding

/-! A missing annular strip crossing makes the horizontal winding cocycle an
actual vertex coboundary. This proves the horizontal obstruction without an
assumed torus Jordan-curve theorem. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC CorrLength
variable {N M : ℕ}
noncomputable section

/-- Connection to the strip's right boundary, within the vertical annulus. -/
def stripReachesRight (hN : Even N) (hM : Even M) (A : RCConfig N M) (K : ℕ)
    (u : FaceVertex N M true) : Prop :=
  ∃ v, v.val.1.val = K ∧ (finiteStripGraph hN hM A K).Reachable u v

/-- The side of the barrier facing the right boundary, extended constantly
through the complementary horizontal interval. -/
def stripRightSide (hN : Even N) (hM : Even M) (A : RCConfig N M) (K : ℕ)
    (u : FaceVertex N M true) : Prop :=
  K ≤ u.val.1.val ∨ stripReachesRight hN hM A K u

lemma stripRightSide_iff_of_le (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (K : ℕ) (u : FaceVertex N M true) (hu : u.val.1.val ≤ K) :
    stripRightSide hN hM A K u ↔ stripReachesRight hN hM A K u := by
  constructor
  · rintro (h | h)
    · exact ⟨u,by omega,SimpleGraph.Reachable.refl _⟩
    · exact h
  · exact Or.inr

lemma stripRightSide_congr_of_reachable (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (K : ℕ) {u v : FaceVertex N M true}
    (hu : u.val.1.val ≤ K) (hv : v.val.1.val ≤ K)
    (h : (finiteStripGraph hN hM A K).Reachable u v) :
    stripRightSide hN hM A K u ↔ stripRightSide hN hM A K v := by
  rw [stripRightSide_iff_of_le hN hM A K u hu,stripRightSide_iff_of_le hN hM A K v hv]
  constructor
  · rintro ⟨w,hw,huw⟩
    exact ⟨w,hw,h.symm.trans huw⟩
  · rintro ⟨w,hw,hvw⟩
    exact ⟨w,hw,h.trans hvw⟩

lemma strip_endpoints_reachable (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (K : ℕ) (e : OpenDiamondEdge A) (hx : e.val.1.val ≠ 0)
    (hf : (faceEndpoint hN hM true e.val false).val.1.val ≤ K)
    (ht : (faceEndpoint hN hM true e.val true).val.1.val ≤ K) :
    (finiteStripGraph hN hM A K).Reachable (faceEndpoint hN hM true e.val false)
      (faceEndpoint hN hM true e.val true) := by
  by_cases he : faceEndpoint hN hM true e.val false = faceEndpoint hN hM true e.val true
  · rw [he]
  · apply SimpleGraph.Adj.reachable
    rw [finiteStripGraph,SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨e.val,e.property,hx,hf,ht,rfl⟩,he⟩

/-- The endpoint x coordinates are the index x and its predecessor, in the
checkerboard-dependent order. -/
lemma endpoint_x_coordinates (hN : Even N) (hM : Even M) (e : Fin N × Fin M) :
    (faceEndpoint hN hM true e false).val.1 = (if checker e then e.1 else prv e.1) ∧
    (faceEndpoint hN hM true e true).val.1 = (if checker e then prv e.1 else e.1) := by
  cases hc : checker e <;> simp [faceEndpoint,faceEndpointRaw,hc]

/-- No left-to-right annular crossing gives a vertex potential for horizontal
seam intersection on every actual open indexed edge. -/
theorem exists_horizontal_seam_potential_of_no_strip_crossing
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (n : ℕ) (hn : 0 < n) (hwidth : 3*n < N)
    (hno : ¬ torusRCLeftStripCrossing hNp hMp A n) :
    ∃ g : FaceVertex N M true → ℚ,
      ∀ e : OpenDiamondEdge A, diamondCoboundary hN hM A g e = diamondSeamCrossX e.val := by
  classical
  let K := 3*n
  let g : FaceVertex N M true → ℚ := fun u => if stripRightSide hN hM A K u then -1 else 0
  have hleft (u : FaceVertex N M true) (hu : u.val.1.val = 0) : g u = 0 := by
    have hr : ¬ stripReachesRight hN hM A K u := by
      rintro ⟨v,hv,hr⟩
      exact hno (finiteStrip_crossing_implies_lifted hN hM hNp hMp A n u v hu hv hr)
    simp [g,stripRightSide,hu,K,show ¬ 3*n ≤ 0 by omega,hr]
  have hright (u : FaceVertex N M true) (hu : K ≤ u.val.1.val) : g u = -1 := by
    simp [g,stripRightSide,hu]
  refine ⟨g,fun e => ?_⟩
  obtain ⟨hxf,hxt⟩ := endpoint_x_coordinates hN hM e.val
  rw [diamondCoboundary_apply]
  by_cases hx : e.val.1.val = 0
  · have hxe : e.val.1 = ⟨0,hNp⟩ := Fin.ext hx
    have hprv : (prv e.val.1).val + 1 = N := by
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNp.ne'
      have hz : e.val.1 = 0 := Fin.ext hx
      rw [hz,prv_zero]
      simp
    cases hc : checker e.val
    · simp only [hc,Bool.false_eq_true,ite_false] at hxf hxt
      have hf : K ≤ (faceEndpoint hN hM true e.val false).val.1.val := by rw [hxf]; dsimp [K]; omega
      have ht : (faceEndpoint hN hM true e.val true).val.1.val = 0 := by rw [hxt]; exact hx
      rw [hright _ hf,hleft _ ht]
      simp [diamondSeamCrossX,hx,hc]
    · simp only [hc,ite_true] at hxf hxt
      have hf : (faceEndpoint hN hM true e.val false).val.1.val = 0 := by rw [hxf]; exact hx
      have ht : K ≤ (faceEndpoint hN hM true e.val true).val.1.val := by rw [hxt]; dsimp [K]; omega
      rw [hright _ ht,hleft _ hf]
      simp [diamondSeamCrossX,hx,hc]
  · have hp := prv_val_of_pos e.val.1 (Nat.pos_of_ne_zero hx)
    by_cases heK : e.val.1.val ≤ K
    · have hf : (faceEndpoint hN hM true e.val false).val.1.val ≤ K := by
        cases hc : checker e.val <;> simp only [hc,Bool.false_eq_true,ite_true,ite_false] at hxf <;> rw [hxf] <;> omega
      have ht : (faceEndpoint hN hM true e.val true).val.1.val ≤ K := by
        cases hc : checker e.val <;> simp only [hc,Bool.false_eq_true,ite_true,ite_false] at hxt <;> rw [hxt] <;> omega
      have hr := stripRightSide_congr_of_reachable hN hM A K hf ht
        (strip_endpoints_reachable hN hM A K e hx hf ht)
      have hg : g (faceEndpoint hN hM true e.val false) = g (faceEndpoint hN hM true e.val true) := by
        dsimp [g]
        rw [propext hr]
      rw [hg,sub_self]
      simp [diamondSeamCrossX,hx]
    · have hf : K ≤ (faceEndpoint hN hM true e.val false).val.1.val := by
        cases hc : checker e.val <;> simp only [hc,Bool.false_eq_true,ite_true,ite_false] at hxf <;> rw [hxf] <;> omega
      have ht : K ≤ (faceEndpoint hN hM true e.val true).val.1.val := by
        cases hc : checker e.val <;> simp only [hc,Bool.false_eq_true,ite_true,ite_false] at hxt <;> rw [hxt] <;> omega
      rw [hright _ hf,hright _ ht,sub_self]
      simp [diamondSeamCrossX,hx]

/-- B's missing left-strip crossing kills every primal horizontal winding. -/
theorem horizontal_displacement_zero_of_no_strip_crossing
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (n : ℕ) (hn : 0 < n) (hwidth : 3*n < N)
    (hno : ¬ torusRCLeftStripCrossing hNp hMp A n)
    (f : diamondCycleSpace hN hM A) : diamondHorizontalDisplacement A f.val = 0 := by
  obtain ⟨g,hg⟩ := exists_horizontal_seam_potential_of_no_strip_crossing
    hN hM hNp hMp A n hn hwidth hno
  have he := diamondBoundary_pairing hN hM A g f.val
  rw [f.property] at he
  simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] at he
  have hw : diamondWindingX A f.val = 0 := by
    unfold diamondWindingX
    simp_rw [← hg]
    exact he.symm
  rw [← diamondWindingX_mul_period hN hM A f,hw,mul_zero]

end
end PottsDiscontinuity.TorusTopology
