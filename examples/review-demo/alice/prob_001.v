Require Import Arith.
Require Import Lia.

(* Alice's proof: direct induction, manual base & step *)
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  induction n as [| n' IHn'].
  - (* Base case: 0 + m = m + 0 *)
    intro m. simpl. rewrite Nat.add_0_r. reflexivity.
  - (* Inductive step: S n' + m = m + S n' *)
    intro m. simpl. rewrite IHn'.
    rewrite Nat.add_succ_r. reflexivity.
Qed.
