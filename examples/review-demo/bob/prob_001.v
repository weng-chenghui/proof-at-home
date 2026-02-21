Require Import Arith.
Require Import Lia.

(* Bob's proof: one-liner using the lia tactic *)
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m. lia.
Qed.
