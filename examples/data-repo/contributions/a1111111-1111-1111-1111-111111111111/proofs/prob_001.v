Require Import Arith.
Require Import Lia.

Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m. lia.
Qed.
