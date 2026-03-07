(** newman_003: Newman's Lemma -- WCR + SN implies CR *)

From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.
From Stdlib Require Import Init.Wf.

Section Newman.

Variable A : Type.
Variable R : relation A.

(** Weak confluence (local confluence): one-step divergence can be rejoined *)
Definition WCR : Prop :=
  forall a b c, R a b -> R a c ->
  exists d, clos_refl_trans A R b d /\ clos_refl_trans A R c d.

(** Confluence (Church-Rosser): multi-step divergence can be rejoined *)
Definition CR : Prop :=
  forall a b c, clos_refl_trans A R a b -> clos_refl_trans A R a c ->
  exists d, clos_refl_trans A R b d /\ clos_refl_trans A R c d.

(** Helper: strip lemma — given a one-step a -> a1 and multi-step a ->* c,
    plus confluence from every one-step reduct of a,
    then a1 and c can be joined. *)
Lemma strip :
  WCR ->
  forall a,
  (forall a', R a a' -> forall b c,
    clos_refl_trans A R a' b -> clos_refl_trans A R a' c ->
    exists d, clos_refl_trans A R b d /\ clos_refl_trans A R c d) ->
  forall a1 c,
  R a a1 -> clos_refl_trans A R a c ->
  exists d, clos_refl_trans A R a1 d /\ clos_refl_trans A R c d.
Proof.
  intros Hwcr a IH a1 c Haa1 Hac.
  apply clos_rt_rt1n in Hac.
  revert a1 Haa1.
  induction Hac as [| x a2 c Hxa2 Ha2c IHa2c].
  - (* c = x (= a): a1 joins with a via a1 itself *)
    intros a1 Haa1.
    exists a1. split; [apply rt_refl | apply rt_step; exact Haa1].
  - (* x -> a2 ->*1n c *)
    intros a1 Hxa1.
    (* WCR: x -> a1, x -> a2 => a1 and a2 join at some d0 *)
    destruct (Hwcr x a1 a2 Hxa1 Hxa2) as [d0 [Ha1d0 Ha2d0]].
    (* a2 ->* c *)
    assert (Ha2c' : clos_refl_trans A R a2 c) by (apply clos_rt1n_rt; exact Ha2c).
    (* IH for a2: a2 is a one-step reduct of x (=a), so a2 is confluent *)
    (* Join d0 and c through a2's confluence *)
    destruct (IH a2 Hxa2 d0 c Ha2d0 Ha2c') as [d1 [Hd0d1 Hcd1]].
    (* Now: a1 ->* d0 ->* d1 and c ->* d1 *)
    (* Use IH for a1: a1 is a one-step reduct of x (=a), so a1 is confluent *)
    (* a1 ->* d0 and a1 ->* a1 (refl), so we can join via a1's confluence *)
    (* Actually we just need: a1 ->* d0 ->* d1 *)
    exists d1. split.
    + apply rt_trans with d0; assumption.
    + exact Hcd1.
Qed.

(** Core of Newman's lemma: proved by well-founded induction on Acc. *)
Lemma newman_acc :
  WCR ->
  forall a, Acc (transp A R) a ->
  forall b c, clos_refl_trans A R a b -> clos_refl_trans A R a c ->
  exists d, clos_refl_trans A R b d /\ clos_refl_trans A R c d.
Proof.
  intros Hwcr a Hacc.
  induction Hacc as [a _ IH].
  intros b c Hab Hac.
  apply clos_rt_rt1n in Hab.
  revert c Hac IH.
  induction Hab as [| x a1 b Hxa1 Ha1b IHa1b].
  - (* x = b *)
    intros c Hac IH. exists c. split; [exact Hac | apply rt_refl].
  - (* x -> a1 ->*1n b *)
    intros c Hac IH.
    (* Use strip to join a1 and c *)
    destruct (strip Hwcr x IH a1 c Hxa1 Hac) as [d [Ha1d Hcd]].
    (* IH(a1): from a1, b and d are joinable *)
    assert (Ha1b' : clos_refl_trans A R a1 b) by (apply clos_rt1n_rt; exact Ha1b).
    destruct (IH a1 Hxa1 b d Ha1b' Ha1d) as [e [Hbe Hde]].
    exists e. split.
    + exact Hbe.
    + apply rt_trans with d; assumption.
Qed.

(** Newman's Lemma: if R is well-founded (strongly normalizing) and
    weakly confluent, then R is confluent. *)
Lemma newman : well_founded (transp A R) -> WCR -> CR.
Proof.
  intros Hwf Hwcr a b c Hab Hac.
  exact (newman_acc Hwcr a (Hwf a) b c Hab Hac).
Qed.

End Newman.
