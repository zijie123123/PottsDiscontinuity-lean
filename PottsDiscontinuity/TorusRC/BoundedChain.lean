module

public import PottsDiscontinuity.TorusRC.BlockChain
public import PottsDiscontinuity.TorusRC.BoundedPaths

/-! # Height-controlled chains for the seam-closing construction -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- The chain from the bottom lift to height 2nk, retaining its actual
vertical range. This event avoids the seam whenever 2nk<M. -/
def boundedRectangleChain (hNp : 0 < N) (hMp : 0 < M) (n : ℕ)
    (i : Fin (3 * n + 1)) (hi : Even (i.val : ℤ)) (k : ℕ) : Set (RCConfig N M) :=
  {A | liftedBoundedConnection hNp hMp A 0 (3 * (n : ℤ)) 0 (2 * (n : ℤ) * k)
    (liftedChainSite i.val hi n 0) (liftedChainSite i.val hi n k)}

theorem rectangleBlockEvent_bounded_connection (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (i : Fin (3 * n + 1)) (hi : Even (i.val : ℤ)) (j : ℕ)
    (A : RCConfig N M) (hA : A ∈ rectangleBlockEvent hNp hMp n i j) :
    liftedBoundedConnection hNp hMp A 0 (3 * (n : ℤ))
      (2 * (n : ℤ) * j) (2 * (n : ℤ) * ((j : ℤ) + 1))
      (liftedChainSite i.val hi n j) (liftedChainSite i.val hi n (j + 1)) := by
  obtain ⟨u,v,hu,hv,w,hw⟩ := hA
  let t : ℤ := 2 * (n : ℤ) * ((j : ℤ) + 1)
  let ht : Even t := ⟨(n : ℤ) * (j + 1),by dsimp [t]; ring⟩
  let F := liftedReflectionStripHom hNp hMp t ht A 0 (3 * (n : ℤ))
  have hstart : F v = liftedChainSite i.val hi n j := by
    apply Subtype.ext
    change (v.val.1,t-v.val.2) = _
    rw [hv]
    ext <;> dsimp [t,liftedChainSite,liftedColumnSite]; ring
  have hend : F u = liftedChainSite i.val hi n (j + 1) := by
    apply Subtype.ext
    change (u.val.1,t-u.val.2) = _
    rw [hu]
    ext <;> dsimp [t,liftedChainSite,liftedColumnSite]; ring
  have hconn : liftedBoundedConnection hNp hMp A 0 (3 * (n : ℤ))
      (2 * (n : ℤ) * j) t (F v) (F u) := by
    refine ⟨(w.map F).reverse,?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_reverse,List.mem_reverse,SimpleGraph.Walk.support_map] at hz
    obtain ⟨z',hzmem,heq⟩ := List.mem_map.mp hz
    subst z
    have h := hw z' hzmem
    change 2 * (n : ℤ) * j ≤ t - z'.val.2 ∧ t - z'.val.2 ≤ t
    have heq : t = 2 * (n : ℤ) * j + 2 * n := by dsimp [t]; ring
    constructor <;> omega
  simpa only [hstart,hend] using hconn

theorem rectangleBlocks_subset_boundedChain (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (i : Fin (3 * n + 1)) (hi : Even (i.val : ℤ)) (k : ℕ) :
    {A | ∀ j < k, A ∈ rectangleBlockEvent hNp hMp n i j} ⊆
      boundedRectangleChain hNp hMp n i hi k := by
  intro A hA
  have hchain (l : ℕ) (hl : l ≤ k) : A ∈ boundedRectangleChain hNp hMp n i hi l := by
    induction l with
    | zero =>
      refine ⟨.nil,?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hz
      subst z
      simp [liftedChainSite,liftedColumnSite]
    | succ l ih =>
      obtain ⟨w,hw⟩ := ih (by omega)
      obtain ⟨p,hp⟩ := rectangleBlockEvent_bounded_connection hNp hMp n i hi l A
        (hA l (by omega))
      refine ⟨w.append p,?_⟩
      intro z hz
      rw [SimpleGraph.Walk.support_append] at hz
      rcases List.mem_append.mp hz with hz | hz
      · have h := hw z hz
        have hmul : 2 * (n : ℤ) * l ≤ 2 * (n : ℤ) * (l + 1) := by
          have hn : 0 ≤ (n : ℤ) := by omega
          nlinarith
        constructor <;> push_cast <;> omega
      · have h := hp z (List.mem_of_mem_tail hz)
        have hlo : 0 ≤ 2 * (n : ℤ) * l := by positivity
        constructor <;> push_cast <;> omega
  exact hchain k le_rfl

theorem boundedRectangleChain_probability_ge (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ))
    (n : ℕ) (i : Fin (3 * n + 1)) (hi : Even (i.val : ℤ)) (k : ℕ) :
    torusRCProbability hN hM q (rectangleDoubleConnection hNp hMp n i) ^ k ≤
      torusRCProbability hN hM q (boundedRectangleChain hNp hMp n i hi k) :=
  (rectangleBlocks_probability_ge_power hN hM hNp hMp q n i k).trans
    (torusRCProbability_mono hN hM q (rectangleBlocks_subset_boundedChain hNp hMp n i hi k))

/-- The whole bounded chain is unchanged by any seam-edge toggle. -/
theorem boundedRectangleChain_toggle_seam (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (i : Fin (3 * n + 1)) (hi : Even (i.val : ℤ)) (k : ℕ)
    (hheight : 2 * n * k < M) (e : Fin N × Fin M) (he : e.2.val = 0)
    (A : RCConfig N M) :
    A ∈ boundedRectangleChain hNp hMp n i hi k ↔
      toggleEdge A e ∈ boundedRectangleChain hNp hMp n i hi k :=
  liftedBoundedConnection_toggle_seam hNp hMp A 0 (3 * (n : ℤ)) 0
    (2 * (n : ℤ) * k) le_rfl (by exact_mod_cast hheight) e he _ _

end PottsDiscontinuity.TorusRC
