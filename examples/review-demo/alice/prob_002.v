Require Import Arith.
Require Import Lia.

(* Alice's proof: structural induction on both hypotheses *)
Lemma le_antisym : forall n m : nat, n <= m -> m <= n -> n = m.
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    intros m Hnm Hmn. inversion Hmn. reflexivity.
  - (* n = S n' *)
    intros m Hnm Hmn. destruct m as [| m'].
    + inversion Hnm.
    + f_equal. apply IHn'.
      * apply le_S_n. exact Hnm.
      * apply le_S_n. exact Hmn.
Qed.
