Require Import Arith.
Require Import Lia.

(* Carol's proof: uses a helper lemma for clarity *)
Lemma le_antisym_helper : forall n m : nat,
  n <= m -> m <= n -> n = m.
Proof.
  intros n m H1 H2.
  apply Nat.le_antisymm; assumption.
Qed.

Lemma le_antisym : forall n m : nat, n <= m -> m <= n -> n = m.
Proof.
  exact le_antisym_helper.
Qed.
