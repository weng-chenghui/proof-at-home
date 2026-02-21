Require Import Arith.
Require Import Lia.

(* Carol's proof: library reuse via Nat.add_comm *)
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  exact Nat.add_comm.
Qed.
