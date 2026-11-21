(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  AdlerModel DeflateInv DeflateInvKeep DeflInvTally RefDeflateRel RefDeflatePost RefDeflateHdr5 DeflInvFbo DeflInvCore DeflInvMain DeflInvTk
  BoundArith BoundInv BoundCore BoundRc.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition AofB (IN : Z) (s : deflate_state) : Z := IN - ds_lookahead s - (ds_strstart s - ds_block_start s).
Definition PhiB (IN : Z) (s : deflate_state) : Z :=
  AofB IN s + 5 * (AofB IN s / KBLK)
  + (if ds_status s =? INIT_STATE then 0 else 2)
  + (if ds_status s =? FINISH_STATE then 5 else 0)
  + (if ds_wrap s <=? 0 then 4 else 0).



Lemma bif_set_strm : forall s st, bif s (set_strm s st).
Proof.
  intros s st. constructor; try (destruct s; reflexivity).
  apply dsyms_iff; destruct s; reflexivity.
Qed.
Lemma BI_set_strm : forall s st, BI s -> BI (set_strm s st).
Proof. intros s st B. exact (BI_transfer _ _ (bif_set_strm s st) B). Qed.
Lemma CFGX_set_strm : forall s st, CFGX s -> CFGX (set_strm s st).
Proof. intros s st C. unfold CFGX in *. destruct s; exact C. Qed.


Definition SZX (s : deflate_state) : Prop := ds_w_size s = 32768 /\ ds_lit_bufsize s * 4 = 4 * 16384.

Definition zs_ok (z : zstrm) : Prop :=
  0 <= zs_total_in z < 2 ^ 64 /\ 0 <= zs_total_out z < 2 ^ 64 /\ 0 <= zs_adler z < 2 ^ 64 /\ - 2 ^ 31 <= zs_data_type z < 2 ^ 31.

Record DB (IN T : Z) (s : deflate_state) (z : zstrm) : Prop := MkDB {
  db_di : DI s;
  db_ad : DADLER2 (ds_wrap s) (zs_adler z);
  db_zs : zs_ok z;
  db_bi : BI s;
  db_cfg : CFGX s;
  db_sz : SZX s;
  db_T : 0 <= T;
  db_IN : 0 <= IN;
  db_tin : zs_total_in z = IN;
  db_tout : zs_total_out z = T;
  db_phi : T + ds_pending s + cdiv8 (ds_bi_valid s) <= PhiB IN s }.








Lemma DB_intro : forall s z,
  DI s -> zs_ok z -> zs_total_in z = 0 -> zs_total_out z = 0 -> 0 <= zs_adler z < 2 ^ 32 -> adler_canon (zs_adler z) ->
  SZX s -> 4 <= ds_level s <= 9 -> ds_strategy s = 0 -> ds_wrap s = 1 -> ds_status s = INIT_STATE ->
  ds_strstart s = 0 -> ds_block_start s = 0 -> ds_lookahead s = 0 -> ds_match_available s = 0 ->
  ds_match_length s = MIN_MATCH - 1 -> ds_pending s = 0 -> ds_bi_valid s = 0 -> dsyms [] s ->
  DB 0 0 s z.
Proof.
  intros s z DI0 ZS TI TO ADR ADC SZ LV SG W ST STR BS LK MA ML P BV D0.
  constructor; try assumption; try lia.
  - rewrite W. split; [exact ADR | intros _; exact ADC].
  - constructor.
    + intros syms Dy. rewrite (dsyms_unique _ _ _ Dy D0). rewrite MA, STR, BS. reflexivity.
    + intros syms Dy. rewrite (dsyms_unique _ _ _ Dy D0). constructor.
    + intros X. exfalso. rewrite ML in X. unfold MIN_MATCH in X. lia.
    + intros X. exfalso. rewrite ML in X. unfold MIN_MATCH in X. lia.
    + intros X. exfalso. rewrite BS in X. lia.
  - unfold CFGX. rewrite SG, W, ST, STR, LK, BS. split; [exact LV|]. split; [reflexivity|]. split; [left; reflexivity|].
    intros _. repeat split; reflexivity.
  - unfold PhiB, AofB. rewrite P, BV, LK, STR, BS, ST, W, cdiv8_0, Z.eqb_refl.
    replace (0 - 0 - (0 - 0)) with 0 by lia. change (0 / KBLK) with 0.
    change (INIT_STATE =? FINISH_STATE) with false. change (1 <=? 0) with false. lia.
Qed.


