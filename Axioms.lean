module

public import PottsDiscontinuity

/-!
# Axiom audit

Run `lake env lean Axioms.lean` after `lake build`. Each of the three main declarations must
depend only on the three standard axioms `[propext, Classical.choice, Quot.sound]`; in particular
no `sorryAx` and no custom axiom.
-/

#print axioms PottsDiscontinuity.potts_theorem_1_1
#print axioms PottsDiscontinuity.rc_theorem_1_2
#print axioms PottsDiscontinuity.rc_theorem_1_2_positivity_eq_1_3
