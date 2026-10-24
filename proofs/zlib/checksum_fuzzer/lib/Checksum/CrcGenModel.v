(** A mathematical model of crc32_combine_gen. The fuel is an explicit bound,
    and the machine theorem must separately show that it suffices. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Export CrcAlgebra.
Import ListNotations.
Open Scope Z_scope.
Fixpoint x2n_loop (fuel : nat) (n k p : Z) : Z :=
  match fuel with
  | O => p
  | S fuel' =>
      if n =? 0 then p else
      x2n_loop fuel' (Z.shiftr n 1) (k + 1)
        (if Z.land n 1 =? 0 then p
         else mm (tabz (Z.to_nat (Z.land k 31))) p)
  end.
Definition combine_gen_model (n : Z) := x2n_loop 21 n 3 (2^31).
Lemma table_index_range : forall k, (Z.to_nat (Z.land k 31) < 32)%nat.
Proof.
  intros k. change 31 with (Z.ones 5).
  rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound k (2^5) ltac:(lia)). lia.
Qed.
Lemma x2n_loop_positive : forall fuel n k p,
  0 < p < 2^32 -> 0 < x2n_loop fuel n k p < 2^32.
Proof.
  induction fuel as [|fuel IH]; intros n k p Hp; cbn [x2n_loop]; [exact Hp|].
  destruct (n =? 0); [exact Hp|].
  apply IH. destruct (Z.land n 1 =? 0); [exact Hp|].
  apply mm_tab_pos; [apply table_index_range|exact Hp].
Qed.
Lemma combine_gen_model_positive : forall n,
  0 < combine_gen_model n < 2^32.
Proof. intros n. apply x2n_loop_positive. lia. Qed.
