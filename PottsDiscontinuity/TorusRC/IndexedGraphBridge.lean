module

public import PottsDiscontinuity.FK.PositiveAssociation
public import PottsDiscontinuity.SixVertex.InfinityEndpointOrder
public import PottsDiscontinuity.TorusLoops.FiniteEnergy
public import PottsDiscontinuity.TorusRC.IndexedFK

/-! # The large-period diamond torus is a simple graph -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus PottsDiscontinuity.SixVertex

variable {N M : ℕ}

private theorem prv_ne_self_of_two_le {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    prv i ≠ i := by
  intro h
  by_cases hi : i.val = 0
  · have hp := PottsDiscontinuity.SixVertex.prv_val_zero i hi
    have hv := congrArg Fin.val h
    rw [hi] at hv
    omega
  · have hp := PottsDiscontinuity.SixVertex.prv_val_of_pos i
      (Nat.pos_of_ne_zero hi)
    have hv := congrArg Fin.val h
    rw [hp] at hv
    omega

private theorem prv_prv_ne_self_of_three_le {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    prv (prv i) ≠ i := by
  intro h
  by_cases hi0 : i.val = 0
  · have hprev := PottsDiscontinuity.SixVertex.prv_val_zero i hi0
    have hprevpos : 0 < (prv i).val := by omega
    have hprevprev := PottsDiscontinuity.SixVertex.prv_val_of_pos
      (prv i) hprevpos
    have hv := congrArg Fin.val h
    rw [hprevprev] at hv
    omega
  · have hprev := PottsDiscontinuity.SixVertex.prv_val_of_pos i
      (Nat.pos_of_ne_zero hi0)
    by_cases hi1 : i.val = 1
    · have hprevzero : (prv i).val = 0 := by omega
      have hprevprev := PottsDiscontinuity.SixVertex.prv_val_zero
        (prv i) hprevzero
      have hv := congrArg Fin.val h
      omega
    · have hprevpos : 0 < (prv i).val := by rw [hprev]; omega
      have hprevprev := PottsDiscontinuity.SixVertex.prv_val_of_pos
        (prv i) hprevpos
      have hv := congrArg Fin.val h
      rw [hprevprev] at hv
      rw [hprev] at hv
      omega

private theorem prv_injective {n : ℕ} (i j : Fin n) (h : prv i = prv j) : i = j := by
  have hn := congrArg nxt h
  simpa only [nxt, prv, Equiv.apply_symm_apply] using hn

private theorem torusEndpointX0 (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v false).val.1 =
      if checker v then v.1 else prv v.1 := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem torusEndpointX1 (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v true).val.1 =
      if checker v then prv v.1 else v.1 := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem torusEndpointY0 (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v false).val.2 = v.2 := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem torusEndpointY1 (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v true).val.2 = prv v.2 := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem torusEndpoints_ne (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (v : Fin N × Fin M) :
    faceEndpoint hN hM true v false ≠ faceEndpoint hN hM true v true := by
  intro h
  have hx := congrArg (fun z : FaceVertex N M true => z.val.1) h
  rw [torusEndpointX0, torusEndpointX1] at hx
  cases hc : checker v <;> simp only [hc, Bool.false_eq_true, ite_true, ite_false] at hx
  · exact (prv_ne_self_of_two_le (by omega) v.1) hx
  · exact (prv_ne_self_of_two_le (by omega) v.1) hx.symm

private theorem torusEndpointPair_injective (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (v w : Fin N × Fin M)
    (he : Sym2.mk (faceEndpoint hN hM true v false)
          (faceEndpoint hN hM true v true) =
        Sym2.mk (faceEndpoint hN hM true w false)
          (faceEndpoint hN hM true w true)) : v = w := by
  rcases Sym2.eq_iff.mp he with ⟨h00, h11⟩ | ⟨h01, h10⟩
  · have h00x := congrArg (fun z : FaceVertex N M true => z.val.1) h00
    have h11x := congrArg (fun z : FaceVertex N M true => z.val.1) h11
    have h00y := congrArg (fun z : FaceVertex N M true => z.val.2) h00
    have h11y := congrArg (fun z : FaceVertex N M true => z.val.2) h11
    simp only [torusEndpointX0, torusEndpointX1, torusEndpointY0,
      torusEndpointY1] at h00x h11x h00y h11y
    cases hv : checker v <;> cases hw : checker w <;>
      simp only [hv, hw, Bool.false_eq_true, ite_true, ite_false] at h00x h11x h00y h11y
    · exact Prod.ext (prv_injective v.1 w.1 h00x) h00y
    · have hcycle : prv (prv v.1) = v.1 := by
        calc
          prv (prv v.1) = prv w.1 := congrArg prv h00x
          _ = v.1 := h11x.symm
      exact (prv_prv_ne_self_of_three_le (by omega) v.1 hcycle).elim
    · have hcycle : prv (prv v.1) = v.1 := by
        calc
          prv (prv v.1) = prv w.1 := congrArg prv h11x
          _ = v.1 := h00x.symm
      exact (prv_prv_ne_self_of_three_le (by omega) v.1 hcycle).elim
    · exact Prod.ext h00x h00y
  · have h01x := congrArg (fun z : FaceVertex N M true => z.val.1) h01
    have h10x := congrArg (fun z : FaceVertex N M true => z.val.1) h10
    have h01y := congrArg (fun z : FaceVertex N M true => z.val.2) h01
    have h10y := congrArg (fun z : FaceVertex N M true => z.val.2) h10
    simp only [torusEndpointX0, torusEndpointX1, torusEndpointY0,
      torusEndpointY1] at h01x h10x h01y h10y
    cases hv : checker v <;> cases hw : checker w <;>
      simp only [hv, hw, Bool.false_eq_true, ite_true, ite_false] at h01x h10x h01y h10y
    · have hcycle : prv (prv v.1) = v.1 := by
        calc
          prv (prv v.1) = prv w.1 := congrArg prv h01x
          _ = v.1 := h10x.symm
      exact (prv_prv_ne_self_of_three_le (by omega) v.1 hcycle).elim
    · have hcycle : prv (prv v.2) = v.2 := by
        calc
          prv (prv v.2) = prv w.2 := congrArg prv h10y
          _ = v.2 := h01y.symm
      exact (prv_prv_ne_self_of_three_le (by omega) v.2 hcycle).elim
    · have hcycle : prv (prv v.2) = v.2 := by
        calc
          prv (prv v.2) = prv w.2 := congrArg prv h10y
          _ = v.2 := h01y.symm
      exact (prv_prv_ne_self_of_three_le (by omega) v.2 hcycle).elim
    · have hcycle : prv (prv v.1) = v.1 := by
        calc
          prv (prv v.1) = prv w.1 := congrArg prv h10x
          _ = v.1 := h01x.symm
      exact (prv_prv_ne_self_of_three_le (by omega) v.1 hcycle).elim

/-- The indexed medial site embeds as a simple edge of the primal diamond graph. -/
def torusIndexedEdgeEmbedding (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) :
    (Fin N × Fin M) ↪ (fullDiamondGraph hN hM).edgeSet where
  toFun v := ⟨Sym2.mk (faceEndpoint hN hM true v false)
      (faceEndpoint hN hM true v true), by
    rw [fullDiamondGraph, diamondOpenGraph, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨⟨v, rfl, rfl⟩, ?_⟩
    intro hd
    simp only [Sym2.mem_diagSet, Sym2.mk_isDiag_iff] at hd
    exact torusEndpoints_ne hN hM hN4 v hd
  ⟩
  inj' := by
    intro v w hvw
    exact torusEndpointPair_injective hN hM hN4 hM4 v w
      (congrArg Subtype.val hvw)

/-- On periods at least four, every simple primal diamond edge has a unique
indexed medial site. -/
noncomputable def torusIndexedEdgeEquiv (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) :
    (Fin N × Fin M) ≃ (fullDiamondGraph hN hM).edgeSet :=
  Equiv.ofBijective (torusIndexedEdgeEmbedding hN hM hN4 hM4) ⟨
    (torusIndexedEdgeEmbedding hN hM hN4 hM4).injective,
    by
      intro e
      have he := e.property
      simp only [fullDiamondGraph, diamondOpenGraph,
        SimpleGraph.edgeSet_fromEdgeSet] at he
      rcases he.1 with ⟨v, hv, hpair⟩
      exact ⟨v, Subtype.ext hpair.symm⟩⟩

def indexOpenSet (A : RCConfig N M) : Finset (Fin N × Fin M) :=
  Finset.univ.filter fun v => A v = true

def indexConfigurationEquiv (N M : ℕ) :
    RCConfig N M ≃ Finset (Fin N × Fin M) where
  toFun := indexOpenSet
  invFun := fun s v => decide (v ∈ s)
  left_inv := by
    intro A
    funext v
    simp [indexOpenSet]
  right_inv := by
    intro s
    ext v
    simp [indexOpenSet]

def finsetEquivOfEquiv {α β : Type*} (e : α ≃ β) : Finset α ≃ Finset β where
  toFun := fun s => s.map e.toEmbedding
  invFun := fun s => s.map e.symm.toEmbedding
  left_inv := by
    intro s
    ext a
    simp
  right_inv := by
    intro s
    ext b
    simp

/-- The full indexed torus configuration is exactly a finite-graph edge set
once both periods are at least four. -/
noncomputable def torusRCConfigurationEquiv (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) :
    RCConfig N M ≃ FK.Configuration (fullDiamondGraph hN hM) :=
  (indexConfigurationEquiv N M).trans
    (finsetEquivOfEquiv (torusIndexedEdgeEquiv hN hM hN4 hM4))

@[simp] theorem mem_torusRCConfigurationEquiv (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (A : RCConfig N M)
    (v : Fin N × Fin M) :
    torusIndexedEdgeEmbedding hN hM hN4 hM4 v ∈
        torusRCConfigurationEquiv hN hM hN4 hM4 A ↔ A v = true := by
  classical
  change torusIndexedEdgeEquiv hN hM hN4 hM4 v ∈
      (indexOpenSet A).map (torusIndexedEdgeEquiv hN hM hN4 hM4).toEmbedding ↔
        A v = true
  rw [Finset.mem_map_equiv]
  simp [indexOpenSet]

theorem simpleConfiguration_eq_torusRCConfigurationEquiv
    (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (A : RCConfig N M) :
    simpleConfiguration hN hM A = torusRCConfigurationEquiv hN hM hN4 hM4 A := by
  classical
  ext e
  simp only [simpleConfiguration, Finset.mem_filter, Finset.mem_univ, true_and]
  let v := (torusIndexedEdgeEquiv hN hM hN4 hM4).symm e
  have hev : torusIndexedEdgeEmbedding hN hM hN4 hM4 v = e :=
    (torusIndexedEdgeEquiv hN hM hN4 hM4).apply_symm_apply e
  change (∃ w, A w = true ∧ e.val =
      Sym2.mk (faceEndpoint hN hM true w false) (faceEndpoint hN hM true w true)) ↔
    e ∈ torusRCConfigurationEquiv hN hM hN4 hM4 A
  rw [← hev]
  constructor
  · rintro ⟨w, hw, hpair⟩
    have hwe : torusIndexedEdgeEmbedding hN hM hN4 hM4 w =
        torusIndexedEdgeEmbedding hN hM hN4 hM4 v := by
      apply Subtype.ext
      exact hpair.symm
    have : w = v := (torusIndexedEdgeEmbedding hN hM hN4 hM4).injective hwe
    subst w
    exact (mem_torusRCConfigurationEquiv hN hM hN4 hM4 A v).2 hw
  · intro he
    have hv := (mem_torusRCConfigurationEquiv hN hM hN4 hM4 A v).1 he
    exact ⟨v, hv, rfl⟩

noncomputable def torusRCFKParameters (q : Set.Ici (1 : ℝ)) : FK.Parameters :=
  ⟨q.val, q.property,
    ⟨(rcCriticalParameter q).val, criticalParameter_pos q, criticalParameter_lt_one q⟩⟩

noncomputable local instance torusIndexedGraphFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _

private theorem torusIndexedEdge_card (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) :
    Fintype.card (fullDiamondGraph hN hM).edgeSet = N * M := by
  rw [← Fintype.card_congr (torusIndexedEdgeEquiv hN hM hN4 hM4)]
  simp [Fintype.card_prod]

private theorem torusRCConfigurationEquiv_card (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (A : RCConfig N M) :
    (torusRCConfigurationEquiv hN hM hN4 hM4 A).card = openCount A := by
  simp [torusRCConfigurationEquiv, indexConfigurationEquiv, indexOpenSet,
    finsetEquivOfEquiv, openCount]

/-- For large even periods, the indexed torus weight `torusRCWeight`
(`Torus/DiamondGraph.lean`) is exactly the free FK
weight on the simple diamond torus graph. -/
theorem torusRCWeight_eq_fk_weight (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (A : RCConfig N M) :
    torusRCWeight hN hM q A =
      FK.weight (fullDiamondGraph hN hM) (torusRCFKParameters q)
        (FK.BoundaryCondition.free ∅)
        (torusRCConfigurationEquiv hN hM hN4 hM4 A) := by
  rw [Torus.torusRCWeight, FK.weight]
  have hcomp : clusterCount hN hM true A =
      FK.componentCount (fullDiamondGraph hN hM) (FK.BoundaryCondition.free ∅)
        (torusRCConfigurationEquiv hN hM hN4 hM4 A) := by
    rw [clusterCount_eq_componentCount,
      simpleConfiguration_eq_torusRCConfigurationEquiv hN hM hN4 hM4 A]
  have hopen := torusRCConfigurationEquiv_card hN hM hN4 hM4 A
  have htotal := torusIndexedEdge_card hN hM hN4 hM4
  have hclosed :
      Nat.card (fullDiamondGraph hN hM).edgeSet -
          (torusRCConfigurationEquiv hN hM hN4 hM4 A).card = closedCount A := by
    rw [Nat.card_eq_fintype_card, htotal, hopen]
    have hsplit := openCount_add_closedCount A
    omega
  have hclosed' : Nat.card (fullDiamondGraph hN hM).edgeSet - openCount A =
      closedCount A := by
    rw [Nat.card_eq_fintype_card, htotal]
    have hsplit := openCount_add_closedCount A
    omega
  rw [hcomp, hopen, hclosed']
  simp [torusRCFKParameters, FK.edgeParameter]

end PottsDiscontinuity.TorusRC
