module

public import PottsDiscontinuity.TorusLoops.LoopClusterProjection
public import PottsDiscontinuity.TorusLoops.DualTranslation

/-!
# Incidence of loops with their primal and dual clusters

Each medial loop has one incident cluster of each colour. The joint incidence
relation is connected: at every indexed edge its two ends are connected either
through the open primal edge or through the open dual edge.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The actual dual cluster incident to a loop, in translated primal coordinates. -/
def loopDualCluster (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A)) :
    (diamondOpenGraph hN hM true (translatedDual A)).ConnectedComponent :=
  loopPrimalCluster hN hM (translatedDual A) (translatedDualLoopEquiv hN hM A q)

@[simp] theorem loopDualCluster_loopOf (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (d : DirectedDart (checkerArrows N M)) :
    loopDualCluster hN hM A (directedLoopOf _ _
        (checkerArrows_compatible hN hM (rcSmoothing A)) d) =
      (diamondOpenGraph hN hM true (translatedDual A)).connectedComponentMk
        (ribbonFace hN hM (dualDartEquiv hN hM d)) := by
  unfold loopDualCluster
  rw [translatedDualLoopEquiv_loopOf, loopPrimalCluster_loopOf]

theorem loopDualCluster_ends_of_closed (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M) (hv : A v = false) :
    loopDualCluster hN hM A (directedLoopOf _ _
      (checkerArrows_compatible hN hM (rcSmoothing A)) (ribbonEndEquiv hN hM (v, false))) =
    loopDualCluster hN hM A (directedLoopOf _ _
      (checkerArrows_compatible hN hM (rcSmoothing A)) (ribbonEndEquiv hN hM (v, true))) := by
  rw [loopDualCluster_loopOf, loopDualCluster_loopOf,
    ribbonFace_dualDart_end, ribbonFace_dualDart_end]
  have ho : translatedDual A (columnShift v) = true := by rw [translatedDual_shift, hv]; rfl
  have hr := diamond_endpoints_reachable hN hM (translatedDual A) (columnShift v) ho
  apply SimpleGraph.ConnectedComponent.sound
  cases hc : checker v
  · simpa only [hc, Bool.false_xor] using hr
  · simpa only [hc, Bool.true_xor, Bool.not_false, Bool.not_true] using hr.symm

/-- Any labels agreeing across each loop agree between the two ends of every
indexed ribbon, using the primal edge when open and the dual edge when closed. -/
theorem compatible_cluster_labels_ends {β : Type*} (hN : Even N) (hM : Even M)
    (A : RCConfig N M)
    (f : (diamondOpenGraph hN hM true A).ConnectedComponent → β)
    (g : (diamondOpenGraph hN hM true (translatedDual A)).ConnectedComponent → β)
    (hfg : ∀ q, f (loopPrimalCluster hN hM A q) = g (loopDualCluster hN hM A q))
    (v : Fin N × Fin M) :
    f ((diamondOpenGraph hN hM true A).connectedComponentMk
      (faceEndpoint hN hM true v false)) =
    f ((diamondOpenGraph hN hM true A).connectedComponentMk
      (faceEndpoint hN hM true v true)) := by
  cases hv : A v
  · let q₀ := directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
      (ribbonEndEquiv hN hM (v, false))
    let q₁ := directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
      (ribbonEndEquiv hN hM (v, true))
    have h₀ := hfg q₀
    have h₁ := hfg q₁
    have hd : loopDualCluster hN hM A q₀ = loopDualCluster hN hM A q₁ :=
      loopDualCluster_ends_of_closed hN hM A v hv
    rw [← hd] at h₁
    have he := h₀.trans h₁.symm
    simpa only [q₀, q₁, loopPrimalCluster_loopOf, ribbonFace_end] using he
  · exact congrArg f (SimpleGraph.ConnectedComponent.sound
      (diamond_endpoints_reachable hN hM A v hv))

/-- The loop–cluster incidence relation is connected, expressed without
choosing representatives of either cluster quotient. -/
theorem compatible_cluster_labels_constant {β : Type*} (hN : Even N) (hM : Even M)
    (A : RCConfig N M)
    (f : (diamondOpenGraph hN hM true A).ConnectedComponent → β)
    (g : (diamondOpenGraph hN hM true (translatedDual A)).ConnectedComponent → β)
    (hfg : ∀ q, f (loopPrimalCluster hN hM A q) = g (loopDualCluster hN hM A q))
    (c c' : (diamondOpenGraph hN hM true A).ConnectedComponent) : f c = f c' := by
  induction c using Quot.inductionOn with
  | h u =>
    induction c' using Quot.inductionOn with
    | h v =>
      have hr := diamondOpenGraph_open_preconnected hN hM u v
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      induction hr with
      | refl => rfl
      | @tail w z hr hadj ih =>
        apply ih.trans
        rw [diamondOpenGraph, SimpleGraph.fromEdgeSet_adj] at hadj
        obtain ⟨⟨e, _, he⟩, _⟩ := hadj
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact compatible_cluster_labels_ends hN hM A f g hfg e
        · exact (compatible_cluster_labels_ends hN hM A f g hfg e).symm

theorem loopPrimalCluster_surjective (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Function.Surjective (loopPrimalCluster hN hM A) := by
  intro c
  induction c using Quot.inductionOn with
  | h v =>
    refine ⟨directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
      (ribbonVertexDart hN hM v), ?_⟩
    rw [loopPrimalCluster_loopOf, ribbonFace_vertexDart]
    rfl

theorem loopDualCluster_surjective (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Function.Surjective (loopDualCluster hN hM A) :=
  (loopPrimalCluster_surjective hN hM (translatedDual A)).comp
    (translatedDualLoopEquiv hN hM A).surjective

noncomputable section

local instance primalClusterFintype (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Fintype (diamondOpenGraph hN hM true A).ConnectedComponent := Fintype.ofFinite _

abbrev LoopIncidenceVertex (hN : Even N) (hM : Even M) (A : RCConfig N M) :=
  (diamondOpenGraph hN hM true A).ConnectedComponent ⊕
    (diamondOpenGraph hN hM true (translatedDual A)).ConnectedComponent

/-- The actual signed incidence matrix; loops remain distinct indexed edges. -/
def loopIncidenceMatrix (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Matrix (LoopIncidenceVertex hN hM A) (Loop hN hM (rcSmoothing A)) ℚ := by
  classical
  exact fun v q => (if v = Sum.inl (loopPrimalCluster hN hM A q) then 1 else 0) -
    (if v = Sum.inr (loopDualCluster hN hM A q) then 1 else 0)

def loopIncidenceBoundary (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    (Loop hN hM (rcSmoothing A) → ℚ) →ₗ[ℚ] (LoopIncidenceVertex hN hM A → ℚ) := by
  classical
  exact Matrix.toLin' (loopIncidenceMatrix hN hM A)

def loopIncidenceCoboundary (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    (LoopIncidenceVertex hN hM A → ℚ) →ₗ[ℚ] (Loop hN hM (rcSmoothing A) → ℚ) where
  toFun f q := f (.inl (loopPrimalCluster hN hM A q)) - f (.inr (loopDualCluster hN hM A q))
  map_add' _ _ := by ext; simp only [Pi.add_apply]; ring
  map_smul' _ _ := by ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem incidenceKernel_constant (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (f : LinearMap.ker (loopIncidenceCoboundary hN hM A))
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (v : LoopIncidenceVertex hN hM A) : f.val v = f.val (.inl c) := by
  have hfg (q : Loop hN hM (rcSmoothing A)) :
      f.val (.inl (loopPrimalCluster hN hM A q)) = f.val (.inr (loopDualCluster hN hM A q)) :=
    sub_eq_zero.mp (congrFun f.property q)
  cases v with
  | inl c' =>
      exact compatible_cluster_labels_constant hN hM A
        (fun c => f.val (.inl c)) (fun c => f.val (.inr c)) hfg c' c
  | inr d =>
      obtain ⟨q, rfl⟩ := loopDualCluster_surjective hN hM A d
      exact (hfg q).symm.trans (compatible_cluster_labels_constant hN hM A
        (fun c => f.val (.inl c)) (fun c => f.val (.inr c)) hfg _ c)

/-- The only potentials with zero incidence coboundary are constant potentials. -/
def incidenceKernelConstantEquiv (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) :
    LinearMap.ker (loopIncidenceCoboundary hN hM A) ≃ₗ[ℚ] ℚ where
  toFun f := f.val (.inl ((diamondOpenGraph hN hM true A).connectedComponentMk
    (originFace hNp hMp)))
  invFun a := ⟨fun _ => a, by ext; exact sub_self a⟩
  left_inv f := by
    apply Subtype.ext
    funext v
    exact (incidenceKernel_constant hN hM A f _ v).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
theorem loopIncidenceCoboundary_eq_transpose (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    loopIncidenceCoboundary hN hM A = Matrix.toLin' (loopIncidenceMatrix hN hM A).transpose := by
  classical
  apply LinearMap.ext
  intro f
  funext q
  change f (.inl (loopPrimalCluster hN hM A q)) - f (.inr (loopDualCluster hN hM A q)) =
    ∑ v, loopIncidenceMatrix hN hM A v q * f v
  simp only [loopIncidenceMatrix, sub_mul, Finset.sum_sub_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The incidence circulation space has dimension at most one. This is the
algebraic form of the torus incidence graph being a tree or a unicyclic graph. -/
theorem finrank_loopIncidenceCycleSpace_le_one (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) :
    Module.finrank ℚ (LinearMap.ker (loopIncidenceBoundary hN hM A)) ≤ 1 := by
  classical
  have hk : Module.finrank ℚ (LinearMap.ker (loopIncidenceCoboundary hN hM A)) = 1 := by
    rw [(incidenceKernelConstantEquiv hN hM hNp hMp A).finrank_eq, Module.finrank_self]
  have hr : Module.finrank ℚ (LinearMap.range (loopIncidenceBoundary hN hM A)) =
      Module.finrank ℚ (LinearMap.range (loopIncidenceCoboundary hN hM A)) := by
    rw [loopIncidenceCoboundary_eq_transpose]
    change (loopIncidenceMatrix hN hM A).rank = (loopIncidenceMatrix hN hM A).transpose.rank
    exact (Matrix.rank_transpose _).symm
  have hb := LinearMap.finrank_range_add_finrank_ker (loopIncidenceBoundary hN hM A)
  have hc := LinearMap.finrank_range_add_finrank_ker (loopIncidenceCoboundary hN hM A)
  have hv : Fintype.card (LoopIncidenceVertex hN hM A) =
      clusterCount hN hM true A + clusterCount hN hM true (translatedDual A) := by
    rw [Fintype.card_sum]
    simp only [clusterCount, Nat.card_eq_fintype_card]
  rw [Module.finrank_pi, hr] at hb
  rw [Module.finrank_pi, hk, hv] at hc
  have hl := rcLoopCount_le_primal_dual_clusters hN hM A
  change Fintype.card (Loop hN hM (rcSmoothing A)) ≤ _ at hl
  omega

end

end PottsDiscontinuity.TorusLoops
