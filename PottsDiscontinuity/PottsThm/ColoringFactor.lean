module

public import PottsDiscontinuity.PottsThm.LatticeColorNoise
public import PottsDiscontinuity.PottsThm.ProductErgodicity
public import PottsDiscontinuity.RCInfinite.ClusterEvents
public import Mathlib.Data.Prod.Lex

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Set
open PottsDiscontinuity.FK
open PottsDiscontinuity.RCInfinite

noncomputable section

abbrev Vertex := ℤ × ℤ

def vertexLex : Vertex → ℤ ×ₗ ℤ := toLex

private theorem vertexLex_translate_le_iff (a x y : Vertex) :
    vertexLex (latticeTranslate a x) ≤ vertexLex (latticeTranslate a y) ↔
      vertexLex x ≤ vertexLex y := by
  simp only [vertexLex, Prod.Lex.toLex_le_toLex, latticeTranslate]
  omega

/-- The distinguished representative records absence explicitly on infinite
clusters. Finite nonempty clusters are represented by their lexicographic
minimum. -/
def clusterRepresentative (ω : LatticeConfiguration) (x : Vertex) : Option Vertex := by
  classical
  exact if h : (cluster ω x).Finite then
    some (Classical.choose (Set.exists_min_image (cluster ω x) vertexLex h ⟨x, by
      change (rcInfiniteOpenGraph ω).Reachable x x
      exact SimpleGraph.Reachable.refl x⟩))
  else
    none

theorem clusterRepresentative_spec (ω : LatticeConfiguration) (x y : Vertex) :
    clusterRepresentative ω x = some y ↔
      (cluster ω x).Finite ∧ y ∈ cluster ω x ∧
        ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z := by
  classical
  unfold clusterRepresentative
  split_ifs with h
  · constructor
    · intro heq
      have hspec := Classical.choose_spec
        (Set.exists_min_image (cluster ω x) vertexLex h ⟨x, by
          change (rcInfiniteOpenGraph ω).Reachable x x
          exact SimpleGraph.Reachable.refl x⟩)
      cases heq
      exact ⟨h, hspec.1, hspec.2⟩
    · rintro ⟨_, hy, hmin⟩
      have hspec := Classical.choose_spec
        (Set.exists_min_image (cluster ω x) vertexLex h ⟨x, by
          change (rcInfiniteOpenGraph ω).Reachable x x
          exact SimpleGraph.Reachable.refl x⟩)
      have heq : Classical.choose
          (Set.exists_min_image (cluster ω x) vertexLex h ⟨x, by
            change (rcInfiniteOpenGraph ω).Reachable x x
            exact SimpleGraph.Reachable.refl x⟩) = y := by
        apply toLex_inj.mp
        apply le_antisymm
        · exact hspec.2 _ hy
        · exact hmin _ hspec.1
      exact congrArg some heq
  · constructor
    · simp
    · rintro ⟨hfinite, _, _⟩
      exact (h hfinite).elim

private theorem cluster_eq_of_reachable (ω : LatticeConfiguration) {x y : Vertex}
    (hxy : (rcInfiniteOpenGraph ω).Reachable x y) : cluster ω x = cluster ω y := by
  ext z
  constructor
  · intro hz
    change (rcInfiniteOpenGraph ω).Reachable x z at hz
    change (rcInfiniteOpenGraph ω).Reachable y z
    exact hxy.symm.trans hz
  · intro hz
    change (rcInfiniteOpenGraph ω).Reachable y z at hz
    change (rcInfiniteOpenGraph ω).Reachable x z
    exact hxy.trans hz

/-- Canonical finite-cluster representatives agree exactly on connected
vertices. -/
theorem clusterRepresentative_eq_iff_reachable (ω : LatticeConfiguration)
    (x y : Vertex) (hfiniteX : (cluster ω x).Finite)
    (hfiniteY : (cluster ω y).Finite) :
    clusterRepresentative ω x = clusterRepresentative ω y ↔
      (rcInfiniteOpenGraph ω).Reachable x y := by
  classical
  constructor
  · intro heq
    have hne : clusterRepresentative ω x ≠ none := by
      simp [clusterRepresentative, hfiniteX]
    have hsome : ∃ z, clusterRepresentative ω x = some z := by
      cases h : clusterRepresentative ω x with
      | none =>
        exact (hne h).elim
      | some z => exact ⟨z, rfl⟩
    obtain ⟨z, hz⟩ := hsome
    have hzy : clusterRepresentative ω y = some z := by rw [← heq, hz]
    have hxz : z ∈ cluster ω x := (clusterRepresentative_spec ω x z).mp hz |>.2.1
    have hyz : z ∈ cluster ω y := (clusterRepresentative_spec ω y z).mp hzy |>.2.1
    change (rcInfiniteOpenGraph ω).Reachable x z at hxz
    change (rcInfiniteOpenGraph ω).Reachable y z at hyz
    exact hxz.trans hyz.symm
  · intro hxy
    have hclusters := cluster_eq_of_reachable ω hxy
    obtain ⟨a, ha, hminA⟩ := Set.exists_min_image (cluster ω x) vertexLex hfiniteX
      ⟨x, by change (rcInfiniteOpenGraph ω).Reachable x x; exact SimpleGraph.Reachable.refl x⟩
    obtain ⟨b, hb, hminB⟩ := Set.exists_min_image (cluster ω y) vertexLex hfiniteY
      ⟨y, by change (rcInfiniteOpenGraph ω).Reachable y y; exact SimpleGraph.Reachable.refl y⟩
    have hba : b ∈ cluster ω x := by rw [hclusters]; exact hb
    have hab : a ∈ cluster ω y := by rw [← hclusters]; exact ha
    have hle₁ : vertexLex a ≤ vertexLex b := hminA b hba
    have hle₂ : vertexLex b ≤ vertexLex a := hminB a hab
    have hab' : a = b := toLex_inj.mp (le_antisymm hle₁ hle₂)
    have hrepA := (clusterRepresentative_spec ω x a).2 ⟨hfiniteX, ha, hminA⟩
    have hrepB := (clusterRepresentative_spec ω y b).2 ⟨hfiniteY, hb, hminB⟩
    rw [hrepA, hrepB, hab']

theorem clusterRepresentative_covariant (a : Vertex) (ω : LatticeConfiguration) (x : Vertex) :
    clusterRepresentative (edgeTranslate a ω) (latticeTranslate a x) =
      Option.map (latticeTranslate a) (clusterRepresentative ω x) := by
  classical
  by_cases hfin : (cluster ω x).Finite
  · obtain ⟨y, hy, hmin⟩ := Set.exists_min_image (cluster ω x) vertexLex hfin
      ⟨x, by change (rcInfiniteOpenGraph ω).Reachable x x; exact SimpleGraph.Reachable.refl x⟩
    have himage : (cluster (edgeTranslate a ω) (latticeTranslate a x)).Finite := by
      rw [cluster_translation]
      exact hfin.image _
    have hyspec : latticeTranslate a y ∈
        cluster (edgeTranslate a ω) (latticeTranslate a x) := by
      rw [cluster_translation]
      exact ⟨y, hy, rfl⟩
    have hminspec : ∀ z ∈ cluster (edgeTranslate a ω) (latticeTranslate a x),
        vertexLex (latticeTranslate a y) ≤ vertexLex z := by
      intro z hz
      rw [cluster_translation] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact (vertexLex_translate_le_iff a y w).2 (hmin w hw)
    have hold := (clusterRepresentative_spec ω x y).2 ⟨hfin, hy, hmin⟩
    have hnew := (clusterRepresentative_spec (edgeTranslate a ω)
      (latticeTranslate a x) (latticeTranslate a y)).2 ⟨himage, hyspec, hminspec⟩
    simp [hold, hnew]
  · have hnewInf : (cluster (edgeTranslate a ω) (latticeTranslate a x)).Infinite := by
      rw [cluster_translation]
      exact (Set.infinite_image_iff
        (show Set.InjOn (latticeTranslate a) (cluster ω x) from
          (latticeTranslationIso a).injective.injOn)).2 hfin
    have hleft : clusterRepresentative (edgeTranslate a ω) (latticeTranslate a x) = none := by
      simp [clusterRepresentative, hnewInf]
    have hright : Option.map (latticeTranslate a) (clusterRepresentative ω x) = none := by
      simp [clusterRepresentative, hfin]
    exact hleft.trans hright.symm

theorem clusterRepresentative_none_iff (ω : LatticeConfiguration) (x : Vertex) :
    clusterRepresentative ω x = none ↔ (cluster ω x).Infinite := by
  classical
  by_cases h : (cluster ω x).Finite
  · simp [clusterRepresentative, h]
  · constructor
    · intro _
      exact h
    · intro _
      simp [clusterRepresentative, h]

/-- Colour finite clusters from the iid coordinate of their canonical
representative and pin infinite clusters to `c₀`. -/
def clusterColoring {C : Type*} (c₀ : C)
    (z : LatticeConfiguration × (Vertex → C)) : Vertex → C :=
  fun x => (clusterRepresentative z.1 x).elim c₀ z.2

theorem measurableSet_clusterRepresentative (x y : Vertex) :
    MeasurableSet {ω : LatticeConfiguration | clusterRepresentative ω x = some y} := by
  have hfinite : MeasurableSet {ω : LatticeConfiguration | (cluster ω x).Finite} := by
    have heq : {ω : LatticeConfiguration | (cluster ω x).Finite} = (infiniteAt x)ᶜ := by
      ext ω
      change (cluster ω x).Finite ↔ ¬¬(cluster ω x).Finite
      classical
      tauto
    rw [heq]
    exact (measurableSet_infiniteAt x).compl
  have hmem : MeasurableSet {ω : LatticeConfiguration | y ∈ cluster ω x} :=
    measurableSet_open_reachable x y
  have hmin : MeasurableSet {ω : LatticeConfiguration |
      ∀ z, z ∈ cluster ω x → vertexLex y ≤ vertexLex z} := by
    have heq : {ω : LatticeConfiguration |
        ∀ z, z ∈ cluster ω x → vertexLex y ≤ vertexLex z} =
        ⋂ z : Vertex, {ω : LatticeConfiguration |
          z ∈ cluster ω x → vertexLex y ≤ vertexLex z} := by
      ext ω
      simp
    rw [heq]
    apply MeasurableSet.iInter
    intro z
    by_cases hle : vertexLex y ≤ vertexLex z
    · simp [hle]
    · have hreach : {ω : LatticeConfiguration | z ∈ cluster ω x} =
          {ω | (rcInfiniteOpenGraph ω).Reachable x z} := rfl
      rw [show {ω : LatticeConfiguration | z ∈ cluster ω x →
          vertexLex y ≤ vertexLex z} =
          {ω : LatticeConfiguration | z ∉ cluster ω x} by
            ext ω
            simp [hle]]
      have hnot : {ω : LatticeConfiguration | z ∉ cluster ω x} =
          {ω | ¬(rcInfiniteOpenGraph ω).Reachable x z} := by
        ext ω
        rfl
      rw [hnot]
      exact (measurableSet_open_reachable x z).compl
  rw [show {ω : LatticeConfiguration | clusterRepresentative ω x = some y} =
      {ω | (cluster ω x).Finite ∧ y ∈ cluster ω x ∧
        ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z} by
        ext ω
        change clusterRepresentative ω x = some y ↔ _
        exact clusterRepresentative_spec ω x y]
  exact hfinite.inter (hmem.inter hmin)

theorem measurable_clusterColoring {C : Type*} [MeasurableSpace C]
    [MeasurableSingletonClass C] [Fintype C] (c₀ : C) :
    Measurable (clusterColoring c₀ :
      LatticeConfiguration × (Vertex → C) → Vertex → C) := by
  classical
  apply measurable_pi_iff.mpr
  intro x
  change ∀ s : Set C, MeasurableSet s →
    MeasurableSet ((fun z : LatticeConfiguration × (Vertex → C) =>
      clusterColoring c₀ z x) ⁻¹' s)
  intro s hs
  have hdecomp : s = ⋃ c : {c : C // c ∈ s}, ({c.1} : Set C) := by
    ext c
    simp
  rw [hdecomp, Set.preimage_iUnion]
  apply MeasurableSet.iUnion
  intro c
  have hpre : {z : LatticeConfiguration × (Vertex → C) |
      clusterColoring c₀ z x = c.1} =
      (infiniteAt x ×ˢ {u : Vertex → C | c₀ = c.1}) ∪
        ⋃ y : Vertex,
          ({ω : LatticeConfiguration | clusterRepresentative ω x = some y} ×ˢ
            {u : Vertex → C | u y = c.1}) := by
    ext z
    rcases z with ⟨ω, u⟩
    rw [Set.mem_union, Set.mem_prod, Set.mem_iUnion]
    constructor
    · intro hz
      cases hr : clusterRepresentative ω x with
      | none =>
        have hinf := (clusterRepresentative_none_iff ω x).mp hr
        exact Or.inl ⟨hinf, by simpa [clusterColoring, hr] using hz⟩
      | some y =>
        apply Or.inr
        exact ⟨y, ⟨hr, by simpa [clusterColoring, hr] using hz⟩⟩
    · rintro (⟨hinf, hc⟩ | ⟨y, hr, hc⟩)
      · have hr := (clusterRepresentative_none_iff ω x).2 hinf
        simpa [clusterColoring, hr] using hc
      · change clusterRepresentative ω x = some y at hr
        simpa [clusterColoring, hr] using hc
  change MeasurableSet {z : LatticeConfiguration × (Vertex → C) |
    clusterColoring c₀ z x = c.1}
  rw [hpre]
  apply MeasurableSet.union
  · apply (measurableSet_infiniteAt x).prod
    by_cases h : c₀ = c.1 <;> simp [h]
  · exact MeasurableSet.iUnion fun y =>
      (measurableSet_clusterRepresentative x y).prod <| by
        have heval : Measurable (fun u : Vertex → C => u y) := measurable_pi_apply y
        have hset : {u : Vertex → C | u y = c.1} =
            (fun u : Vertex → C => u y) ⁻¹' {c.1} := by
          ext u
          simp
        rw [hset]
        exact heval (measurableSet_singleton c.1)

theorem clusterColoring_equivariant {C : Type*} (c₀ : C) (a : Vertex)
    (z : LatticeConfiguration × (Vertex → C)) (x : Vertex) :
    clusterColoring c₀
        (productShift (fun a ω => edgeTranslate a ω)
          (fun a u => iidFieldShift (latticeShiftEquiv a) u) a z) x =
      clusterColoring c₀ z (x - a) := by
  rcases z with ⟨ω, u⟩
  have hrep := clusterRepresentative_covariant a ω (latticeTranslate (-a) x)
  have hcancel : latticeTranslate a (latticeTranslate (-a) x) = x := by
    simpa using (latticeTranslate_neg_cancel (-a) x)
  rw [hcancel] at hrep
  have hcoord : latticeTranslate (-a) x = x - a := by
    ext <;> simp [latticeTranslate, sub_eq_add_neg]
  cases hr : clusterRepresentative ω (x - a) with
  | none =>
    rw [← hcoord] at hr
    have hnone : clusterRepresentative ω (latticeTranslate (-a) x) = none := by
      exact hr
    have hnone' : clusterRepresentative ω (x - a) = none := by
      rw [← hcoord]
      exact hnone
    simp [clusterColoring, productShift, latticeShiftEquiv, hrep, hnone,
      hnone']
  | some y =>
    rw [← hcoord] at hr
    have hsome : clusterRepresentative ω (latticeTranslate (-a) x) = some y := by
      exact hr
    have hsome' : clusterRepresentative ω (x - a) = some y := by
      rw [← hcoord]
      exact hsome
    have harg : (latticeTranslate a y) - a = y := by
      ext <;> dsimp [latticeTranslate] <;> omega
    have hshift : iidFieldShift (latticeShiftEquiv a) u (latticeTranslate a y) = u y := by
      rw [iidFieldShift]
      change u ((latticeTranslate a y) - a) = u y
      rw [harg]
    simp only [clusterColoring, productShift, hrep, hsome, hsome', Option.map_some,
      Option.elim_some]
    exact hshift

end
end PottsDiscontinuity.PottsThm
