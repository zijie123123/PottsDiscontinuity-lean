module

public import PottsDiscontinuity.Torus.DiamondDisplacement
public import PottsDiscontinuity.TorusRC.LiftedPaths

/-! Potentials on the finite torus telescope along the specified integer lifts.
These lemmas preserve lifted displacements instead of substituting finite torus
connectivity for a winding path. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC CorrLength
variable {N M : ℕ}

lemma periodicCoordinate_ne_of_unit_difference (hM : 2 ≤ M)
    (hMp : 0 < M) (a b : ℤ) (hab : |a-b| = 1) :
    periodicCoordinate hMp a ≠ periodicCoordinate hMp b := by
  intro he
  have he' := congrArg (fun i : Fin M => (i.val : ℤ)) he
  rw [periodicCoordinate_val,periodicCoordinate_val] at he'
  have hd : (M : ℤ) ∣ b-a := Int.modEq_iff_dvd.1 he'
  have hunit : b-a = 1 ∨ b-a = -1 := by
    have h := abs_sub_comm a b
    rw [hab] at h
    rcases le_total 0 (b-a) with hp | hn
    · rw [abs_of_nonneg hp] at h
      exact Or.inl h.symm
    · rw [abs_of_nonpos hn] at h
      right
      omega
  have hd1 : (M : ℤ) ∣ 1 := by
    rcases hunit with h | h
    · rwa [h] at hd
    · simpa only [h, dvd_neg] using hd
  have hn : M ∣ 1 := by exact_mod_cast hd1
  have hb := Nat.le_of_dvd (by decide : 0 < 1) hn
  omega

lemma faceEndpoint_false_y (hN : Even N) (hM : Even M) (e : Fin N × Fin M) :
    (faceEndpoint hN hM true e false).val.2 = e.2 := by
  cases hc : checker e <;> simp [faceEndpoint,faceEndpointRaw,hc]

/-- A potential having vertical edge difference -1 acquires exactly the
integer vertical displacement along any lifted open edge. -/
theorem potential_vertical_difference_of_lifted_adj
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (g : FaceVertex N M true → ℚ)
    (hg : ∀ e : OpenDiamondEdge A, diamondCoboundary hN hM A g e = -1)
    (a b : ℤ) {u v : RotatedVertex}
    (huv : (liftedStripGraph hNp hMp A a b).Adj u v) :
    g (liftedFaceVertex hN hM hNp hMp v) -
      g (liftedFaceVertex hN hM hNp hMp u) = (v.val.2-u.val.2 : ℤ) := by
  have hM2 : 2 ≤ M := by rcases hM with ⟨k,hk⟩; omega
  have hyunit := huv.1.2
  have hy : u.val.2-v.val.2 = 1 ∨ u.val.2-v.val.2 = -1 := by
    rcases le_total 0 (u.val.2-v.val.2) with hp | hn
    · rw [abs_of_nonneg hp] at hyunit
      exact Or.inl hyunit
    · rw [abs_of_nonpos hn] at hyunit
      right
      omega
  let e : OpenDiamondEdge A := ⟨liftedEdgeIndex hNp hMp u v,huv.2.1⟩
  have hge := hg e
  rw [diamondCoboundary_apply] at hge
  have hep := liftedFaceEndpoints_eq hN hM hNp hMp u v huv.1
  have hne := periodicCoordinate_ne_of_unit_difference hM2 hMp u.val.2 v.val.2 huv.1.2
  have hef := faceEndpoint_false_y hN hM e.val
  change (faceEndpoint hN hM true e.val false).val.2 =
    periodicCoordinate hMp (max u.val.2 v.val.2) at hef
  rcases Sym2.eq_iff.1 hep with h | h
  · have hypos : v.val.2 ≤ u.val.2 := by
      by_contra hn
      have hl : u.val.2 < v.val.2 := by omega
      rw [max_eq_right_of_lt hl, ← h.1] at hef
      exact hne hef
    have hdiff : v.val.2-u.val.2 = -1 := by omega
    rw [h.1,h.2,hdiff]
    simpa only [Int.cast_neg, Int.cast_one] using hge
  · have hypos : u.val.2 ≤ v.val.2 := by
      by_contra hn
      have hl : v.val.2 < u.val.2 := by omega
      rw [max_eq_left_of_lt hl, ← h.2] at hef
      exact hne hef.symm
    have hdiff : v.val.2-u.val.2 = 1 := by omega
    rw [h.1,h.2,hdiff]
    push_cast
    linarith

/-- Telescope along the actual specified lift, retaining its endpoint heights. -/
theorem potential_vertical_difference_of_lifted_walk
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (g : FaceVertex N M true → ℚ)
    (hg : ∀ e : OpenDiamondEdge A, diamondCoboundary hN hM A g e = -1)
    (a b : ℤ) {u v : RotatedVertex}
    (p : (liftedStripGraph hNp hMp A a b).Walk u v) :
    g (liftedFaceVertex hN hM hNp hMp v) -
      g (liftedFaceVertex hN hM hNp hMp u) = (v.val.2-u.val.2 : ℤ) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have he := potential_vertical_difference_of_lifted_adj hN hM hNp hMp A g hg a b h
    push_cast at he ih ⊢
    linarith

/-- A genuine lifted vertical period forces a conserved primal chain with
nonzero vertical displacement. No loop/cluster topology is assumed. -/
theorem exists_vertical_cycle_of_lifted_period
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b x : ℤ) (hx : Even x)
    (hconn : (liftedStripGraph hNp hMp A a b).Reachable
      (liftedColumnSite x 0 hx ⟨0,rfl⟩)
      (liftedColumnSite x (M : ℤ) hx (by exact_mod_cast hM))) :
    ∃ f : diamondCycleSpace hN hM A, diamondVerticalDisplacement A f.val ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨g,hg⟩ := exists_diamondPotential_of_cycle_annihilator hN hM A
    (fun _ => -1) (fun f => by
      simpa only [neg_one_mul,Finset.sum_neg_distrib,diamondVerticalDisplacement] using hn f)
  have hg' : ∀ e : OpenDiamondEdge A, diamondCoboundary hN hM A g e = -1 :=
    fun e => congrFun hg e
  obtain ⟨p⟩ := hconn
  have he := potential_vertical_difference_of_lifted_walk hN hM hNp hMp A g hg' a b p
  rw [← liftedFaceVertex_vertical_period hN hM hNp hMp x hx,sub_self] at he
  have hm : (0 : ℚ) < M := by positivity
  dsimp [liftedColumnSite] at he
  push_cast at he
  linarith

end PottsDiscontinuity.TorusTopology
