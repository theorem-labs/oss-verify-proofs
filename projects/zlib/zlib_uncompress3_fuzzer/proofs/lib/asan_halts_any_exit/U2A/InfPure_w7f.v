(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import InfPure_w7d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma term_lens : forall mb e, term_ok LENS mb e = true ->
  1 <= code_bits e <= mb /\
  ((code_op e = 0 /\ code_val e < 256)
   \/ (16 <= code_op e <= 21 /\ 3 <= code_val e /\ code_val e + 2 ^ (code_op e - 16) - 1 <= 258)
   \/ (Z.land (code_op e) 64 <> 0 /\ Z.land (code_op e) 16 = 0)).
Proof.
  intros mb e H. pose proof (term_ok_bits _ _ _ H) as HB. split; [exact HB|].
  unfold term_ok in H. apply andb_prop in H as [_ H]. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
  - left. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. lia.
  - right. left. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
    rewrite Z.shiftl_1_l in H4. lia.
  - right. right. apply andb_prop in H as [H1 H2]. apply negb_true_iff in H1. apply Z.eqb_neq in H1. apply Z.eqb_eq in H2. split; assumption.
Qed.

Lemma op_len_tests : forall op, 16 <= op <= 21 -> Z.land op 32 = 0 /\ Z.land op 64 = 0 /\ Z.land op 15 = op - 16.
Proof. intros op H. zcases op 16 21; repeat split; reflexivity. Qed.
Lemma op_m1_small : forall op, 1 <= op <= 15 -> 0 <= op - 1 <= 14.
Proof. intros; lia. Qed.
Lemma op_m1_taken : forall op, 0 <= op < 256 -> 14 < (op + -1) mod 18446744073709551616 -> op = 0 \/ 16 <= op.
Proof. intros op R H. destruct (Z.eq_dec op 0) as [E|E]; [left; exact E|]. right. rewrite Z.mod_small in H by lia. lia. Qed.
Lemma op_m1_not : forall op, 0 <= op < 256 -> (op + -1) mod 18446744073709551616 <= 14 -> 1 <= op <= 15.
Proof.
  intros op R H. destruct (Z.eq_dec op 0) as [E|E].
  - subst op. exfalso. revert H. vm_compute. intros H. apply H. reflexivity.
  - rewrite Z.mod_small in H by lia. lia.
Qed.
