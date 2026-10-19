/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.IsolatedExtension
public import Mathlib.Order.Setoid.Basic

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

/-- Pull back an arbitrary boundary partition along an injective vertex map. -/
def isolatedExtensionPullbackBoundary {V W : Type*} (f : V ↪ W)
    (ξ : BoundaryCondition W) : BoundaryCondition V where
  boundary := f ⁻¹' ξ.boundary
  partition := Setoid.comap f ξ.partition
  supported := by
    intro u v huv
    have h := (Setoid.comap_rel f ξ.partition u v).mp huv
    rcases ξ.supported h with heq | ⟨hu, hv⟩
    · exact Or.inl (f.injective heq)
    · exact Or.inr ⟨hu, hv⟩

def isolatedExtensionExteriorBoundaryClasses {V W : Type*} (f : V ↪ W)
    (ξ : BoundaryCondition W) :=
  {C : Quotient ξ.partition // ∀ v : V, Quotient.mk ξ.partition (f v) ≠ C}

def isolatedBoundaryComponentLabel {V W : Type*} (G : SimpleGraph V)
    (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G) (x : W) :
    Sum (Quotient (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A))
      (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  classical
  by_cases hx : ∃ u : V, ξ.partition.r (f u) x
  · exact Sum.inl (Quotient.mk _ (Classical.choose hx))
  · exact Sum.inr ⟨Quotient.mk ξ.partition x, by
      intro u heq
      apply hx
      exact ⟨u, Quotient.exact heq⟩⟩

private theorem isolatedBoundaryLabel_of_hit {V W : Type*} (G : SimpleGraph V)
    (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G)
    (u : V) (x : W) (hux : ξ.partition.r (f u) x) :
    isolatedBoundaryComponentLabel G f ξ A x =
      Sum.inl (Quotient.mk _ u) := by
  classical
  unfold isolatedBoundaryComponentLabel
  rw [dite_eq_left ⟨u, hux⟩]
  apply congrArg Sum.inl
  apply Quotient.sound
  apply boundary_component G (isolatedExtensionPullbackBoundary f ξ) A
  apply (Setoid.comap_rel f ξ.partition _ _).mpr
  let hhit : ∃ z : V, ξ.partition.r (f z) x := ⟨u, hux⟩
  have hchoose : ξ.partition.r (f (Classical.choose hhit)) x :=
    Classical.choose_spec hhit
  exact Setoid.trans' ξ.partition hchoose (Setoid.symm' ξ.partition hux)

private theorem isolatedBoundaryLabel_of_no_hit {V W : Type*} (G : SimpleGraph V)
    (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G)
    (x : W) (hx : ¬ ∃ u : V, ξ.partition.r (f u) x) :
    isolatedBoundaryComponentLabel G f ξ A x =
      Sum.inr ⟨Quotient.mk ξ.partition x, by
        intro u heq
        apply hx
        exact ⟨u, Quotient.exact heq⟩⟩ := by
  classical
  unfold isolatedBoundaryComponentLabel
  rw [dite_eq_right hx]

private theorem actualConnected_isolatedExtension_iff_explicit
    {V W : Type*} (G : SimpleGraph V) (f : V ↪ W) (A : Configuration G)
    (x y : W) :
    ActualConnected (G.map f) (isolatedExtensionConfigurationEquiv G f A) x y ↔
      x = y ∨ ∃ u v, ActualConnected G A u v ∧ f u = x ∧ f v = y := by
  simpa only [ActualConnected, openGraph_isolatedExtension] using
    (reachable_isolatedExtension (openGraph G A) f x y)

private theorem isolatedBoundaryInnerRel_maps {V W : Type*} (G : SimpleGraph V)
    (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G) {u v : V}
    (h : (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A).r u v) :
    (componentSetoid (G.map f) ξ (isolatedExtensionConfigurationEquiv G f A)).r (f u) (f v) := by
  rw [componentSetoid_rel_iff] at h ⊢
  induction h with
  | rel u v huv =>
      rcases huv with hconn | hξ
      · exact Relation.EqvGen.rel _ _ (Or.inl
          ((actualConnected_isolatedExtension G f A u v).mpr hconn))
      · exact Relation.EqvGen.rel _ _ (Or.inr
          ((Setoid.comap_rel f ξ.partition u v).mp hξ))
  | refl u => exact Relation.EqvGen.refl _
  | symm u v huv ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v z huv hvz ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def isolatedBoundaryComponentRelation {V W : Type*} (G : SimpleGraph V)
    (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G) (x y : W) : Prop :=
  ξ.partition.r x y ∨ ∃ u v : V,
    ξ.partition.r x (f u) ∧
    (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A).r u v ∧
    ξ.partition.r (f v) y

 theorem componentSetoid_isolatedExtension_iff_boundaryRelation
    {V W : Type*} (G : SimpleGraph V) (f : V ↪ W) (ξ : BoundaryCondition W)
    (A : Configuration G) (x y : W) :
    (componentSetoid (G.map f) ξ (isolatedExtensionConfigurationEquiv G f A)).r x y ↔
      isolatedBoundaryComponentRelation G f ξ A x y := by
  constructor
  · intro h
    rw [componentSetoid_rel_iff] at h
    induction h with
    | rel x y hxy =>
        rcases hxy with hconn | hξ
        · rcases (actualConnected_isolatedExtension_iff_explicit G f A x y).mp hconn with
            hEq | ⟨u, v, huv, rfl, rfl⟩
          · subst y
            exact Or.inl (Setoid.refl' ξ.partition _)
          · exact Or.inr ⟨u, v, Setoid.refl' ξ.partition _,
              actualConnected_component G (isolatedExtensionPullbackBoundary f ξ) A huv,
              Setoid.refl' ξ.partition _⟩
        · exact Or.inl hξ
    | refl x => exact Or.inl (Setoid.refl' ξ.partition _)
    | symm x y hxy ih =>
        rcases ih with hξ | ⟨u, v, hxu, huv, hvy⟩
        · exact Or.inl (Setoid.symm' ξ.partition hξ)
        · exact Or.inr ⟨v, u, Setoid.symm' ξ.partition hvy, Setoid.symm' (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A) huv, Setoid.symm' ξ.partition hxu⟩
    | trans x y z hxy hyz ih₁ ih₂ =>
        rcases ih₁ with hxy | ⟨u, v, hxu, huv, hvy⟩
        · rcases ih₂ with hyz | ⟨u', v', hyu', hu'v', hv'z⟩
          · exact Or.inl (Setoid.trans' ξ.partition hxy hyz)
          · exact Or.inr ⟨u', v', Setoid.trans' ξ.partition hxy hyu', hu'v', hv'z⟩
        · rcases ih₂ with hyz | ⟨u', v', hyu', hu'v', hv'z⟩
          · exact Or.inr ⟨u, v, hxu, huv, Setoid.trans' ξ.partition hvy hyz⟩
          · have hvu' : (isolatedExtensionPullbackBoundary f ξ).partition.r v u' :=
              (Setoid.comap_rel f ξ.partition v u').mpr
                (Setoid.trans' ξ.partition hvy hyu')
            have hcomp :
                (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A).r v u' :=
              boundary_component G (isolatedExtensionPullbackBoundary f ξ) A hvu'
            exact Or.inr ⟨u, v', hxu, Setoid.trans' (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A) huv (Setoid.trans' (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A) hcomp hu'v'), hv'z⟩
  · intro h
    rcases h with hξ | ⟨u, v, hxu, huv, hvy⟩
    · exact boundary_component (G.map f) ξ
        (isolatedExtensionConfigurationEquiv G f A) hξ
    · exact (componentSetoid (G.map f) ξ
        (isolatedExtensionConfigurationEquiv G f A)).trans
          (boundary_component (G.map f) ξ
            (isolatedExtensionConfigurationEquiv G f A) hxu)
          (Setoid.trans' (componentSetoid (G.map f) ξ
            (isolatedExtensionConfigurationEquiv G f A))
          (isolatedBoundaryInnerRel_maps G f ξ A huv)
            (boundary_component (G.map f) ξ
              (isolatedExtensionConfigurationEquiv G f A) hvy))

 theorem isolatedBoundaryRelation_iff_label_eq {V W : Type*}
    (G : SimpleGraph V) (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G)
    (x y : W) :
    isolatedBoundaryComponentRelation G f ξ A x y ↔
      isolatedBoundaryComponentLabel G f ξ A x =
        isolatedBoundaryComponentLabel G f ξ A y := by
  classical
  constructor
  · intro h
    rcases h with hξ | ⟨u, v, hxu, huv, hvy⟩
    · by_cases hx : ∃ z : V, ξ.partition.r (f z) x
      · have hy : ∃ z : V, ξ.partition.r (f z) y := by
          rcases hx with ⟨z, hzx⟩
          exact ⟨z, Setoid.trans' ξ.partition hzx hξ⟩
        rw [isolatedBoundaryLabel_of_hit G f ξ A (Classical.choose hx) x
              (Classical.choose_spec hx),
            isolatedBoundaryLabel_of_hit G f ξ A (Classical.choose hx) y
              (Setoid.trans' ξ.partition (Classical.choose_spec hx) hξ)]
      · have hy : ¬ ∃ z : V, ξ.partition.r (f z) y := by
          intro hy
          rcases hy with ⟨z, hzy⟩
          exact hx ⟨z, Setoid.trans' ξ.partition hzy (Setoid.symm' ξ.partition hξ)⟩
        rw [isolatedBoundaryLabel_of_no_hit G f ξ A x hx,
            isolatedBoundaryLabel_of_no_hit G f ξ A y hy]
        congr 1
        apply Subtype.ext
        exact Quotient.sound hξ
    · rw [isolatedBoundaryLabel_of_hit G f ξ A u x (Setoid.symm' ξ.partition hxu),
        isolatedBoundaryLabel_of_hit G f ξ A v y hvy]
      exact congrArg Sum.inl (Quotient.sound huv)
  · intro h
    by_cases hx : ∃ u : V, ξ.partition.r (f u) x
    · by_cases hy : ∃ v : V, ξ.partition.r (f v) y
      · rw [isolatedBoundaryLabel_of_hit G f ξ A (Classical.choose hx) x
              (Classical.choose_spec hx),
            isolatedBoundaryLabel_of_hit G f ξ A (Classical.choose hy) y
              (Classical.choose_spec hy)] at h
        have hq : Quotient.mk _ (Classical.choose hx) =
            Quotient.mk _ (Classical.choose hy) := Sum.inl.inj h
        have huv := Quotient.exact hq
        exact Or.inr ⟨Classical.choose hx, Classical.choose hy,
          Setoid.symm' ξ.partition (Classical.choose_spec hx), huv,
          Classical.choose_spec hy⟩
      · rw [isolatedBoundaryLabel_of_hit G f ξ A (Classical.choose hx) x
              (Classical.choose_spec hx),
            isolatedBoundaryLabel_of_no_hit G f ξ A y hy] at h
        exact False.elim (Sum.inl_ne_inr h)
    · by_cases hy : ∃ v : V, ξ.partition.r (f v) y
      · rw [isolatedBoundaryLabel_of_no_hit G f ξ A x hx,
            isolatedBoundaryLabel_of_hit G f ξ A (Classical.choose hy) y
              (Classical.choose_spec hy)] at h
        exact False.elim (Sum.inr_ne_inl h)
      · rw [isolatedBoundaryLabel_of_no_hit G f ξ A x hx,
            isolatedBoundaryLabel_of_no_hit G f ξ A y hy] at h
        have hsub := Sum.inr.inj h
        have hq : Quotient.mk ξ.partition x = Quotient.mk ξ.partition y :=
          congrArg Subtype.val hsub
        exact Or.inl (Quotient.exact hq)

 theorem isolatedBoundaryComponentLabel_surjective {V W : Type*}
    (G : SimpleGraph V) (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G) :
    Function.Surjective (isolatedBoundaryComponentLabel G f ξ A) := by
  classical
  intro z
  rcases z with q | c
  · obtain ⟨u, rfl⟩ := Quotient.mk_surjective q
    exact ⟨f u, isolatedBoundaryLabel_of_hit G f ξ A u (f u)
      (Setoid.refl' ξ.partition (f u))⟩
  · obtain ⟨x, hx⟩ := Quotient.mk_surjective c.1
    have hno : ¬ ∃ u : V, ξ.partition.r (f u) x := by
      rintro ⟨u, hrel⟩
      apply c.2 u
      exact (Quotient.sound hrel).trans hx
    refine ⟨x, ?_⟩
    rw [isolatedBoundaryLabel_of_no_hit G f ξ A x hno]
    congr 1
    apply Subtype.ext
    exact hx

/-- The component classes of an isolated vertex extension split into the
components represented by the original vertices and the exterior boundary
classes disjoint from the embedded vertex range. -/
noncomputable def isolatedExtensionComponentQuotientEquiv {V W : Type*}
    (G : SimpleGraph V) (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G) :
    Quotient (componentSetoid (G.map f) ξ (isolatedExtensionConfigurationEquiv G f A)) ≃
      Sum (Quotient (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A))
        (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  let F := isolatedBoundaryComponentLabel G f ξ A
  have hrel : componentSetoid (G.map f) ξ
      (isolatedExtensionConfigurationEquiv G f A) = Setoid.ker F := by
    apply Setoid.ext
    intro x y
    exact (componentSetoid_isolatedExtension_iff_boundaryRelation G f ξ A x y).trans
      (isolatedBoundaryRelation_iff_label_eq G f ξ A x y)
  exact (Quotient.congrRight (fun x y => hrel ▸ Iff.rfl)).trans
    (Setoid.quotientKerEquivOfSurjective F
      (isolatedBoundaryComponentLabel_surjective G f ξ A))

/-- The exact component count is the pullback-boundary component count plus
all boundary classes wholly outside the embedded vertex range. -/
theorem componentCount_isolatedExtension_boundary_pullback {V W : Type*}
    [Finite V] [Finite W] (G : SimpleGraph V) (f : V ↪ W)
    (ξ : BoundaryCondition W) (A : Configuration G) :
    componentCount (G.map f) ξ (isolatedExtensionConfigurationEquiv G f A) =
      componentCount G (isolatedExtensionPullbackBoundary f ξ) A +
        Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  let : Finite (Quotient ξ.partition) :=
    Finite.of_surjective (Quotient.mk ξ.partition) Quotient.mk_surjective
  let : Finite (isolatedExtensionExteriorBoundaryClasses f ξ) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  rw [componentCount, componentCount, ← Nat.card_sum]
  exact Nat.card_congr (isolatedExtensionComponentQuotientEquiv G f ξ A)

end
end PottsDiscontinuity.FK
