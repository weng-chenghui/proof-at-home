(** newman_002: Confluence implies Church-Rosser (joinability) *)

From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Relations.Relation_Operators.

Section Confluence.

Variable A : Type.
Variable R : relation A.

Definition joinable (x y : A) : Prop :=
  exists z, clos_refl_trans A R x z /\ clos_refl_trans A R y z.

Definition confluent : Prop :=
  forall a b c, clos_refl_trans A R a b -> clos_refl_trans A R a c -> joinable b c.

(** If R is confluent, then any two elements reachable from a common
    ancestor are joinable. This is essentially the definition unfolded,
    but we prove it via induction on the left derivation to illustrate
    the proof technique. *)

Lemma joinable_refl : forall x, joinable x x.
Proof.
  intro x. exists x. split; apply rt_refl.
Qed.

Lemma joinable_sym : forall x y, joinable x y -> joinable y x.
Proof.
  intros x y [z [Hz1 Hz2]].
  exists z. split; assumption.
Qed.

Lemma rt_joinable_confluent :
  confluent ->
  forall a b c,
    clos_refl_trans A R a b -> clos_refl_trans A R a c -> joinable b c.
Proof.
  intros Hconf a b c Hab Hac.
  exact (Hconf a b c Hab Hac).
Qed.

(** The more interesting direction: prove confluence implies that
    the reflexive-transitive closure has the Church-Rosser property,
    i.e., if a ->* b and a ->* c then b and c are joinable.
    We do this by induction on the derivation a ->* b. *)

Lemma confluence_joinable : confluent ->
  forall a b c, clos_refl_trans A R a b -> clos_refl_trans A R a c -> joinable b c.
Proof.
  intros Hconf a b c Hab Hac.
  generalize dependent c.
  induction Hab as [a b Hstep | a | a w b Haw IHaw Hwb IHwb].
  - (* rt_step: a -> b, a ->* c *)
    intros c Hac.
    apply Hconf with a.
    + apply rt_step. exact Hstep.
    + exact Hac.
  - (* rt_refl: a = b, a ->* c, so joinable a c *)
    intros c Hac.
    exists c. split.
    + exact Hac.
    + apply rt_refl.
  - (* rt_trans: a ->* w ->* b, a ->* c *)
    intros c Hac.
    (* By IH on a ->* w with a ->* c, get joinable w c,
       i.e., exists d, w ->* d /\ c ->* d *)
    destruct (IHaw c Hac) as [d [Hwd Hcd]].
    (* By IH on w ->* b with w ->* d, get joinable b d,
       i.e., exists e, b ->* e /\ d ->* e *)
    destruct (IHwb d Hwd) as [e [Hbe Hde]].
    (* Then c ->* d ->* e, so c ->* e, and b ->* e *)
    exists e. split.
    + exact Hbe.
    + apply rt_trans with d; assumption.
Qed.

End Confluence.
