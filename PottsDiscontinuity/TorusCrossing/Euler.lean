module

public import PottsDiscontinuity.FK.ComponentMerge
public import PottsDiscontinuity.FK.Parameters
public import PottsDiscontinuity.Frozen.Defs.RCCriticalParameter
public import PottsDiscontinuity.TorusCrossing.Existence

/-!
# Euler's relation for the mixed board and exact weight duality

Flipping a closed edge `m` of a primal configuration `A` changes the number `kP` of wired
primal clusters by `-1` exactly when the ends of `m` are not connected, and changes the number
`kD` of wired dual clusters of the complementary dual configuration by `+1` exactly when the
dual ends of `m` are not connected after the flip.  By exclusion and existence exactly one of the
two happens, so `kD - kP - |A|` does not depend on `A`.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

theorem cfgOf_insert {ends : Cell → Cell × Cell} {P M : Finset Cell} (hD : EndData ends P M)
    (A : Finset Cell) (m : Cell) (hm : m ∈ M) :
    cfgOf hD (insert m A) = insert (endEdgeEquiv hD ⟨m, hm⟩) (cfgOf hD A) := by
  ext e
  obtain ⟨m', rfl⟩ := (endEdgeEquiv hD).surjective e
  rw [mem_cfgOf, Finset.mem_insert, Finset.mem_insert, mem_cfgOf]
  constructor
  · rintro (h | h)
    · left; exact congrArg _ (Subtype.ext h)
    · right; exact h
  · rintro (h | h)
    · left; have := (endEdgeEquiv hD).injective h; exact congrArg Subtype.val this
    · right; exact h


section CountLemmas

variable {ends : Cell → Cell × Cell} {P M : Finset Cell} (hD : EndData ends P M)
include hD

theorem endGraph_adj_of_mem (m : Cell) (hm : m ∈ M) (u v : P) (hu : u.1 = (ends m).1)
    (hv : v.1 = (ends m).2) : (endGraph ends P M).Adj u v := by
  rw [endGraph_adj]
  refine ⟨fun h => hD.ne m (by rw [← hu, ← hv, h]), Or.inl ⟨m, hm, ?_⟩⟩
  exact Prod.ext hu.symm hv.symm

theorem endEdgeEquiv_eq (m : Cell) (hm : m ∈ M) (u v : P) (hu : u.1 = (ends m).1)
    (hv : v.1 = (ends m).2) :
    endEdgeEquiv hD ⟨m, hm⟩ =
      ⟨s(u, v), (endGraph ends P M).mem_edgeSet.mpr (endGraph_adj_of_mem hD m hm u v hu hv)⟩ := by
  apply Subtype.ext
  rw [endEdgeEquiv_val]
  obtain ⟨c, hc⟩ := u
  obtain ⟨d, hd⟩ := v
  simp only at hu hv
  subst hu hv
  rfl

theorem count_cfgOf_insert_of_related (ξ : FK.BoundaryCondition P) (A : Finset Cell) (m : Cell)
    (hm : m ∈ M) (u v : P) (hu : u.1 = (ends m).1) (hv : v.1 = (ends m).2)
    (hrel : (FK.componentSetoid (endGraph ends P M) ξ (cfgOf hD A)).r u v) :
    FK.componentCount (endGraph ends P M) ξ (cfgOf hD (insert m A)) =
      FK.componentCount (endGraph ends P M) ξ (cfgOf hD A) := by
  rw [cfgOf_insert hD A m hm, endEdgeEquiv_eq hD m hm u v hu hv]
  exact FK.componentCount_insert_eq_of_related ξ _ (endGraph_adj_of_mem hD m hm u v hu hv) hrel

theorem count_cfgOf_insert_of_not_related (ξ : FK.BoundaryCondition P) (A : Finset Cell)
    (m : Cell) (hm : m ∈ M) (u v : P) (hu : u.1 = (ends m).1) (hv : v.1 = (ends m).2)
    (hrel : ¬ (FK.componentSetoid (endGraph ends P M) ξ (cfgOf hD A)).r u v) :
    FK.componentCount (endGraph ends P M) ξ (cfgOf hD (insert m A)) + 1 =
      FK.componentCount (endGraph ends P M) ξ (cfgOf hD A) := by
  rw [cfgOf_insert hD A m hm, endEdgeEquiv_eq hD m hm u v hu hv]
  exact FK.componentCount_insert_of_not_related ξ _ (endGraph_adj_of_mem hD m hm u v hu hv) hrel

end CountLemmas

namespace Rect

variable (R : Rect)

/-- Number of wired primal clusters. -/
noncomputable def kP (A : Finset Cell) : ℕ :=
  FK.componentCount R.pG R.sepBC (cfgOf R.pData A)

/-- Number of wired dual clusters of the complementary configuration. -/
noncomputable def kD (A : Finset Cell) : ℕ :=
  FK.componentCount R.dG R.dualBC (cfgOf R.dData (R.inner \ A))

theorem euler_step (hh : 0 < R.h) (A₀ : Finset Cell) (hA₀ : A₀ ⊆ R.inner) (m : Cell)
    (hm : m ∈ R.inner) (hmA : m ∉ A₀) :
    (R.kD (insert m A₀) : ℤ) - R.kP (insert m A₀) - (insert m A₀).card =
      R.kD A₀ - R.kP A₀ - A₀.card := by
  have hmem := R.pData.mem m hm
  have hmem' := R.dData.mem m hm
  let u : R.pcells := ⟨(primalEnds m).1, hmem.1⟩
  let v : R.pcells := ⟨(primalEnds m).2, hmem.2⟩
  let u' : R.dcells := ⟨(dualEnds m).1, hmem'.1⟩
  let v' : R.dcells := ⟨(dualEnds m).2, hmem'.2⟩
  have hcard : (insert m A₀).card = A₀.card + 1 := Finset.card_insert_of_notMem hmA
  have hD₁ : insert m (R.inner \ insert m A₀) = R.inner \ A₀ := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_sdiff, not_or]
    constructor
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨hm, hmA⟩
      · exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      by_cases hxm : x = m
      · exact Or.inl hxm
      · exact Or.inr ⟨h1, hxm, h2⟩
  have hmD : m ∈ R.inner \ insert m A₀ → False := by
    intro h; rw [Finset.mem_sdiff] at h; exact h.2 (Finset.mem_insert_self _ _)
  have hinsA : insert m A₀ ⊆ R.inner := Finset.insert_subset hm hA₀
  have hDsub : R.inner \ insert m A₀ ⊆ R.inner := Finset.sdiff_subset
  have hkD0 : R.kD A₀ = FK.componentCount R.dG R.dualBC
      (cfgOf R.dData (insert m (R.inner \ insert m A₀))) := by
    unfold kD; rw [hD₁]
  have hkD1 : R.kD (insert m A₀) = FK.componentCount R.dG R.dualBC
      (cfgOf R.dData (R.inner \ insert m A₀)) := rfl
  have hmem1 : m ∈ R.inner := hm
  by_cases hrelP : (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A₀)).r u v
  · have hP := count_cfgOf_insert_of_related R.pData R.sepBC A₀ m hm u v rfl rfl hrelP
    have hnD : ¬ (FK.componentSetoid R.dG R.dualBC
        (cfgOf R.dData (R.inner \ insert m A₀))).r u' v' :=
      R.exclusion A₀ hA₀ m hm hmA u v rfl rfl u' v' rfl rfl hrelP
    have hD := count_cfgOf_insert_of_not_related R.dData R.dualBC (R.inner \ insert m A₀) m hm
      u' v' rfl rfl hnD
    have e1 : R.kP (insert m A₀) = R.kP A₀ := hP
    have e2 : R.kD A₀ + 1 = R.kD (insert m A₀) := by rw [hkD0, hkD1]; exact hD
    rw [hcard]
    push_cast
    omega
  · have hP := count_cfgOf_insert_of_not_related R.pData R.sepBC A₀ m hm u v rfl rfl hrelP
    have hrelD : (FK.componentSetoid R.dG R.dualBC
        (cfgOf R.dData (R.inner \ insert m A₀))).r u' v' :=
      R.existence hh A₀ hA₀ m hm u v rfl rfl u' v' rfl rfl hrelP
    have hD := count_cfgOf_insert_of_related R.dData R.dualBC (R.inner \ insert m A₀) m hm
      u' v' rfl rfl hrelD
    have e1 : R.kP (insert m A₀) + 1 = R.kP A₀ := hP
    have e2 : R.kD A₀ = R.kD (insert m A₀) := by rw [hkD0, hkD1]; exact hD
    rw [hcard]
    push_cast
    omega


/-- **Euler's relation** for the mixed board: `kD - kP - |A|` is independent of `A ⊆ inner`. -/
theorem euler (hh : 0 < R.h) (A : Finset Cell) (hA : A ⊆ R.inner) :
    (R.kD A : ℤ) - R.kP A - A.card = (R.kD ∅ : ℤ) - R.kP ∅ := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert m A₀ hmA ih =>
    have hA₀ : A₀ ⊆ R.inner := fun x hx => hA (Finset.mem_insert_of_mem hx)
    have hm : m ∈ R.inner := hA (Finset.mem_insert_self _ _)
    rw [R.euler_step hh A₀ hA₀ m hm hmA]
    exact ih hA₀

end Rect

/-- The critical Fortuin-Kasteleyn parameters `(p_c(q), q)`. -/
noncomputable def critParams (q : Set.Ici (1 : ℝ)) : FK.Parameters where
  val := q.val
  property := q.property
  edgeProbability := ⟨(rcCriticalParameter q).val, by
    have hq : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
    exact div_pos (Real.sqrt_pos.2 hq) (by positivity), by
    change Real.sqrt q.val / (1 + Real.sqrt q.val) < 1
    have hq : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
    exact (div_lt_one (by positivity)).2 (by linarith)⟩

theorem critParams_edge (q : Set.Ici (1 : ℝ)) :
    FK.edgeParameter (critParams q) = Real.sqrt q.val / (1 + Real.sqrt q.val) := rfl

theorem critParams_val (q : Set.Ici (1 : ℝ)) : (critParams q).val = q.val := rfl

end PottsDiscontinuity.TorusCrossing
