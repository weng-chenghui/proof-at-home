Require Import Arith.
Require Import Lia.

(* Bob's proof: direct appeal to lia *)
Lemma le_antisym : forall n m : nat, n <= m -> m <= n -> n = m.
Proof.
  intros n m Hnm Hmn. lia.
Qed.
