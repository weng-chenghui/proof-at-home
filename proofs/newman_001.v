(** newman_001: Reflexive-transitive closure is transitive *)

From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Relations.Relation_Operators.

Lemma clos_rt_trans : forall (A : Type) (R : relation A) (x y z : A),
  clos_refl_trans A R x y -> clos_refl_trans A R y z -> clos_refl_trans A R x z.
Proof.
  intros A R x y z Hxy Hyz.
  induction Hxy as [x y Hstep | x | x w y Hxw IHxw Hwy IHwy].
  - (* rt_step: one step x -> y, then y ->* z *)
    apply rt_trans with y.
    + apply rt_step. exact Hstep.
    + exact Hyz.
  - (* rt_refl: x = y, so x ->* z is just Hyz *)
    exact Hyz.
  - (* rt_trans: x ->* w ->* y, IH gives w ->* z and x ->* z *)
    apply IHxw.
    apply IHwy.
    exact Hyz.
Qed.
