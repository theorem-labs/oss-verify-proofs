(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import InflateInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Ltac enum_cases x lo hi :=
  let rec go k := (tryif (assert (x = k) by lia) then subst x else (assert (k + 1 <= x) by lia; go (k + 1))) in
  go lo.

Lemma op_base_tests : forall op, 16 <= op < 32 ->
  Z.land op 16 = 16 /\ Z.land op 64 = 0 /\ Z.land op 32 = 0 /\ Z.land op 240 = 16 /\ Z.land op 15 = op - 16 /\ op <> 0.
Proof.
  intros op H.
  assert (E : op = 16 \/ op = 17 \/ op = 18 \/ op = 19 \/ op = 20 \/ op = 21 \/ op = 22 \/ op = 23 \/ op = 24 \/ op = 25
              \/ op = 26 \/ op = 27 \/ op = 28 \/ op = 29 \/ op = 30 \/ op = 31) by lia.
  repeat (destruct E as [E|E]; [subst op; repeat split; reflexivity || discriminate|]). subst op; repeat split; reflexivity || discriminate.
Qed.

Lemma op_link_tests : forall op, 1 <= op <= 15 ->
  Z.land op 16 = 0 /\ Z.land op 64 = 0 /\ Z.land op 240 = 0 /\ op <> 0.
Proof.
  intros op H.
  assert (E : op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5 \/ op = 6 \/ op = 7 \/ op = 8 \/ op = 9 \/ op = 10
              \/ op = 11 \/ op = 12 \/ op = 13 \/ op = 14 \/ op = 15) by lia.
  repeat (destruct E as [E|E]; [subst op; repeat split; reflexivity || discriminate|]). subst op; repeat split; reflexivity || discriminate.
Qed.



Inductive eclass : Set := ELit | EBase | EInv.
Definition classify (op : Z) : eclass :=
  if op =? 0 then ELit else if (16 <=? op) && (op <? 32) then EBase else EInv.

Lemma term_ok_LENS : forall maxb e, term_ok LENS maxb e = true ->
  1 <= code_bits e <= maxb /\
  ((code_op e = 0 /\ code_val e < 256)
   \/ (16 <= code_op e < 32 /\ 3 <= code_val e /\ code_val e + Z.shiftl 1 (code_op e - 16) - 1 <= 258 /\ code_op e <= 21)
   \/ (Z.land (code_op e) 64 <> 0 /\ Z.land (code_op e) 16 = 0)).
Proof.
  intros maxb e H. unfold term_ok in H. cbv zeta in H.
  apply andb_prop in H as [H K]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [lia|].
  apply Bool.orb_prop in K as [K|K]; [apply Bool.orb_prop in K as [K|K]|].
  - left. apply andb_prop in K as [K1 K2]. apply Z.eqb_eq in K1. apply Z.ltb_lt in K2. lia.
  - right; left. apply andb_prop in K as [K K4]. apply andb_prop in K as [K K3]. apply andb_prop in K as [K1 K2].
    apply Z.leb_le in K1. apply Z.leb_le in K2. apply Z.leb_le in K3. apply Z.leb_le in K4. lia.
  - right; right. apply andb_prop in K as [K1 K2]. apply Bool.negb_true_iff in K1. apply Z.eqb_neq in K1. apply Z.eqb_eq in K2. lia.
Qed.

Lemma term_ok_DISTS : forall maxb e, term_ok DISTS maxb e = true ->
  1 <= code_bits e <= maxb /\
  ((16 <= code_op e < 32 /\ 1 <= code_val e /\ code_val e + Z.shiftl 1 (code_op e - 16) - 1 <= 32768 /\ code_op e <= 29)
   \/ (Z.land (code_op e) 64 <> 0 /\ Z.land (code_op e) 16 = 0 /\ Z.land (code_op e) 32 = 0)).
Proof.
  intros maxb e H. unfold term_ok in H. cbv zeta in H.
  apply andb_prop in H as [H K]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [lia|].
  apply Bool.orb_prop in K as [K|K].
  - left. apply andb_prop in K as [K K4]. apply andb_prop in K as [K K3]. apply andb_prop in K as [K1 K2].
    apply Z.leb_le in K1. apply Z.leb_le in K2. apply Z.leb_le in K3. apply Z.leb_le in K4. lia.
  - right. apply andb_prop in K as [K K3]. apply andb_prop in K as [K1 K2].
    apply Bool.negb_true_iff in K1. apply Z.eqb_neq in K1. apply Z.eqb_eq in K2. apply Z.eqb_eq in K3. lia.
Qed.


Lemma is_linkop_true : forall op, is_linkop op = true <-> 1 <= op <= 15.
Proof.
  intros op. unfold is_linkop. rewrite Bool.andb_true_iff, Z.leb_le, Z.leb_le. lia.
Qed.
Lemma is_linkop_false : forall op, is_linkop op = false <-> ~ (1 <= op <= 15).
Proof.
  intros op. rewrite <- is_linkop_true. destruct (is_linkop op); split; intros; congruence.
Qed.


Lemma tab_root_entry : forall ty rd root ext i, tab_ok ty rd root ext = true -> 0 <= i < 2 ^ root ->
  1 <= code_bits (rd i) <= root /\ 1 <= root <= 15 /\ 2 ^ root <= ext /\
  ((is_linkop (code_op (rd i)) = false /\ term_ok ty root (rd i) = true)
   \/ (1 <= code_op (rd i) <= 15 - root /\ code_bits (rd i) = root /\ 2 ^ root <= code_val (rd i)
       /\ code_val (rd i) + 2 ^ code_op (rd i) <= ext
       /\ forall j, 0 <= j < 2 ^ code_op (rd i) ->
            is_linkop (code_op (rd (code_val (rd i) + j))) = false /\ term_ok ty (15 - root) (rd (code_val (rd i) + j)) = true)).
Proof.
  intros ty rd root ext i T Hi. destruct (tab_ok_root _ _ _ _ T) as (R1 & R2 & R3).
  pose proof (root_ok_cases ty rd root ext (rd i) ltac:(lia) (R3 i Hi)) as C.
  destruct C as [[L TM] | (L & B & OP & V & X & SUB)].
  - split; [apply (term_ok_bits _ _ _ TM)|]. split; [exact R1|]. split; [exact R2|]. left. split; assumption.
  - apply is_linkop_true in L. split; [lia|]. split; [exact R1|]. split; [exact R2|]. right.
    split; [lia|]. split; [exact B|]. split; [exact V|]. split; [exact X|]. exact SUB.
Qed.





Lemma tab_ok_ext : forall ty rd rd' root ext,
  (forall i, 0 <= i < ext -> rd' i = rd i) -> tab_ok ty rd root ext = true -> tab_ok ty rd' root ext = true.
Proof.
  intros ty rd rd' root ext E T. pose proof (tab_ok_root _ _ _ _ T) as (R1 & R2 & R3).
  unfold tab_ok. apply andb_true_intro. split; [apply andb_true_intro; split; [apply andb_true_intro; split; apply Z.leb_le; lia | apply Z.leb_le; rewrite shiftl_1 by lia; lia]|].
  apply forallb_forall. intros i Hi. apply zupto_spec in Hi. rewrite shiftl_1 in Hi by lia.
  rewrite (E i) by lia.
  destruct (root_ok_cases ty rd root ext (rd i) ltac:(lia) (R3 i Hi)) as [[L TM] | (L & B & OP & V & X & SUB)]; unfold root_ok; rewrite L.
  - exact TM.
  - pose proof (proj1 (is_linkop_true _) L) as L'. apply andb_true_intro. split.
    + repeat (apply andb_true_intro; split); try (apply Z.leb_le; rewrite ?shiftl_1 by lia; lia). apply Z.eqb_eq. exact B.
    + apply forallb_forall. intros j Hj. apply zupto_spec in Hj. rewrite shiftl_1 in Hj by lia.
      cbv beta. rewrite (E (code_val (rd i) + j)) by lia. destruct (SUB j Hj) as [A1 A2]. rewrite A1, A2. reflexivity.
Qed.











