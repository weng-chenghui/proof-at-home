Require Import Arith.
Require Import Lia.

Lemma le_antisym : forall n m : nat, n <= m -> m <= n -> n = m.
Proof.
  intros n m H1 H2. lia.
Qed.
