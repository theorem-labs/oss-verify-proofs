(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma gb1_model : forall s t FC DL HP HL HM DP BC OL SL MC f h ovf R n dlen bits ovf',
  R = gen_bitlen_loop1 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC (sd_extra_base t) (sd_max_length t) h ovf ->
  h < 573 -> n = arr_get HP h -> dlen = arr_get DL (arr_get DL n) ->
  bits = (if sd_max_length t <=? dlen then sd_max_length t else dlen + 1) ->
  ovf' = (if sd_max_length t <=? dlen then ovf + 1 else ovf) ->
  R = gen_bitlen_loop1 f
        (if MC <? n then bt_upd s t FC (arr_set DL n (wrap16 bits)) HP HL HM DP BC OL SL MC
         else bt_upd s t FC (arr_set DL n (wrap16 bits)) HP HL HM DP (arr_set BC bits (wrap16 (arr_get BC bits + 1)))
                (wrap64 (OL + arr_get FC n * (bits + xbits t n)))
                (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xbits t n)) else SL) MC)
        t MC (sd_extra_base t) (sd_max_length t) (h + 1) ovf'.
Proof.
  intros until ovf'. intros ER Hh En Ed Eb Eo.
  rewrite GL1_step in ER. change HEAP_SIZE with 573 in ER. rewrite (proj2 (Z.ltb_lt h 573) Hh) in ER.
  rewrite GB1_flat in ER. rewrite <- En, <- Ed in ER.
  assert (EQ : (sd_max_length t <? dlen + 1) = (sd_max_length t <=? dlen)).
  { destruct (Z.ltb_spec (sd_max_length t) (dlen + 1)); destruct (Z.leb_spec (sd_max_length t) dlen); try reflexivity; lia. }
  rewrite EQ in ER. rewrite <- Eb, <- Eo in ER.
  destruct (MC <? n); exact ER.
Qed.

Lemma gb1_ok_step : forall s t FC DL HP HL HM DP BC OL SL MC f h ovf n dlen bits ovf',
  gb1_ok t MC (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) h ovf ->
  h < 573 -> n = arr_get HP h -> dlen = arr_get DL (arr_get DL n) ->
  bits = (if sd_max_length t <=? dlen then sd_max_length t else dlen + 1) ->
  ovf' = (if sd_max_length t <=? dlen then ovf + 1 else ovf) ->
  0 <= arr_get DL n < tsize t
  /\ gb1_ok t MC f
        (if MC <? n then bt_upd s t FC (arr_set DL n (wrap16 bits)) HP HL HM DP BC OL SL MC
         else bt_upd s t FC (arr_set DL n (wrap16 bits)) HP HL HM DP (arr_set BC bits (wrap16 (arr_get BC bits + 1)))
                (wrap64 (OL + arr_get FC n * (bits + xbits t n)))
                (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xbits t n)) else SL) MC)
        (h + 1) ovf'.
Proof.
  intros until ovf'. intros OK Hh En Ed Eb Eo.
  cbn [gb1_ok] in OK. change HEAP_SIZE with 573 in OK. rewrite (proj2 (Z.ltb_lt h 573) Hh) in OK.
  destruct OK as [OK1 OK2]. rewrite bt_heap_get, bt_Dad in OK1. rewrite <- En in OK1. split; [exact OK1|].
  rewrite GB1_flat in OK2. rewrite <- En, <- Ed in OK2.
  assert (EQ : (sd_max_length t <? dlen + 1) = (sd_max_length t <=? dlen)).
  { destruct (Z.ltb_spec (sd_max_length t) (dlen + 1)); destruct (Z.leb_spec (sd_max_length t) dlen); try reflexivity; lia. }
  rewrite EQ in OK2. rewrite <- Eb, <- Eo in OK2.
  destruct (MC <? n); exact OK2.
Qed.

Lemma gb1_done : forall t MC f X h ovf, 573 <= h ->
  gen_bitlen_loop1 f X t MC (sd_extra_base t) (sd_max_length t) h ovf = (X, ovf).
Proof. intros. apply GL1_done. exact H. Qed.
