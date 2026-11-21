(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac zcases x lo hi :=
  let rec go k :=
    lazymatch eval cbv in (Z.leb k hi) with
    | true => let E := fresh "E" in destruct (Z.eq_dec x k) as [E|E]; [subst x | let k' := eval cbv in (k + 1) in go k']
    | false => exfalso; lia
    end in go lo.

Lemma op_land64_0 : forall op, 16 <= op <= 29 -> Z.land op 64 = 0.
Proof. intros op H. zcases op 16 29; reflexivity. Qed.
Lemma op_land15 : forall op, 16 <= op <= 29 -> Z.land op 15 = op - 16.
Proof. intros op H. zcases op 16 29; reflexivity. Qed.
Lemma op_land15_len : forall op, 16 <= op <= 21 -> Z.land op 15 = op - 16.
Proof. intros op H. apply op_land15. lia. Qed.

Lemma term_dists : forall mb e, term_ok DISTS mb e = true ->
  1 <= code_bits e <= mb /\
  ((16 <= code_op e <= 29 /\ 1 <= code_val e /\ code_val e + 2 ^ (code_op e - 16) - 1 <= 32768) \/ Z.land (code_op e) 64 <> 0).
Proof.
  intros mb e H. pose proof (term_ok_bits _ _ _ H) as HB. split; [exact HB|].
  unfold term_ok in H. apply andb_prop in H as [_ H]. apply orb_prop in H as [H|H].
  - left. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
    rewrite Z.shiftl_1_l in H4. lia.
  - right. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply negb_true_iff in H. apply Z.eqb_neq in H. exact H.
Qed.

Lemma root_term_or_link : forall ty rd root ext e, 0 <= root -> root_ok ty rd root ext e = true ->
  (term_ok ty root e = true /\ ~ (1 <= code_op e <= 15))
  \/ (1 <= code_op e <= 15 /\ code_bits e = root /\ code_op e <= 15 - root /\ 2 ^ root <= code_val e /\ code_val e + 2 ^ code_op e <= ext
      /\ forall j, 0 <= j < 2 ^ code_op e -> term_ok ty (15 - root) (rd (code_val e + j)) = true /\ ~ (1 <= code_op (rd (code_val e + j)) <= 15)).
Proof.
  intros ty rd root ext e Hr H. destruct (root_ok_cases ty rd root ext e Hr H) as [[L T]|(L & B & O & V1 & V2 & SUB)].
  - left. split; [exact T|]. unfold is_linkop in L. intros C. assert (X : (1 <=? code_op e) && (code_op e <=? 15) = true) by (apply andb_true_intro; split; apply Z.leb_le; lia). congruence.
  - right. unfold is_linkop in L. apply andb_prop in L as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
    split; [lia|]. split; [exact B|]. split; [exact O|]. split; [exact V1|]. split; [exact V2|].
    intros j Hj. destruct (SUB j Hj) as [L' T']. split; [exact T'|]. unfold is_linkop in L'. intros C.
    assert (X : (1 <=? code_op (rd (code_val e + j))) && (code_op (rd (code_val e + j)) <=? 15) = true) by (apply andb_true_intro; split; apply Z.leb_le; lia). congruence.
Qed.
