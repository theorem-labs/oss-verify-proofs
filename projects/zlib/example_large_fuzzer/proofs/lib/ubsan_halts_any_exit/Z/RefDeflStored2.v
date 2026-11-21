(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 128).

Local Ltac nf := cbn [dfF].

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P19 := fresh "P19" in let P20 := fresh "P20" in
  let P21 := fresh "P21" in let P23 := fresh "P23" in let Hmb := fresh "Hmb" in
  pose proof HRG as (Hmb & P8 & P2 & P19 & P20 & P21 & P23).
Local Ltac open_tregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P23 := fresh "P23" in pose proof HRG as (P8 & P2 & P23).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].

Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].

Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.

Definition sb_hdr (X : deflate_state) : Z := Z.shiftr (ds_bi_valid X + 42) 3.
Definition sb_left (X : deflate_state) : Z := wrap32 (ds_strstart X - ds_block_start X).
Definition sb_len1 (X : deflate_state) : Z :=
  if sb_left X + cs_avail_in (ds_strm X) <? 65535 then wrap32 (sb_left X + cs_avail_in (ds_strm X)) else 65535.
Definition sb_len (X : deflate_state) : Z :=
  let have := cs_avail_out (ds_strm X) - sb_hdr X in
  if have <? sb_len1 X then have else sb_len1 X.

Lemma sb_hdr_eq : forall X, 0 <= ds_bi_valid X <= 16 -> sb_hdr X = (ds_bi_valid X + 42) / 2 ^ 3 /\ 5 <= (ds_bi_valid X + 42) / 2 ^ 3 <= 7.
Proof. intros X H. unfold sb_hdr. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; [reflexivity|]. Z.to_euclidean_division_equations; lia. Qed.





Lemma sb_left_range : forall X, 0 <= sb_left X < 2 ^ 32.
Proof. intros X. unfold sb_left. rewrite wrap32_mod. apply Z.mod_pos_bound. lia. Qed.

Lemma sb_len1_eq : forall X, 0 <= cs_avail_in (ds_strm X) ->
  sb_len1 X = (if sb_left X + cs_avail_in (ds_strm X) <? 65535 then sb_left X + cs_avail_in (ds_strm X) else 65535)
  /\ 0 <= sb_len1 X <= 65535 /\ sb_len1 X <= sb_left X + cs_avail_in (ds_strm X).
Proof.
  intros X Hai. pose proof (sb_left_range X). unfold sb_len1.
  destruct (Z.ltb_spec (sb_left X + cs_avail_in (ds_strm X)) 65535); [| lia].
  rewrite wrap32_mod, Z.mod_small by lia. lia.
Qed.

Lemma sb_len_range : forall X, 0 <= cs_avail_in (ds_strm X) -> sb_hdr X <= cs_avail_out (ds_strm X) ->
  0 <= sb_len X <= 65535 /\ sb_len X <= cs_avail_out (ds_strm X) - sb_hdr X /\ sb_len X <= sb_len1 X.
Proof.
  intros X Hai Hh. destruct (sb_len1_eq X Hai) as (_ & H1 & _). unfold sb_len.
  destruct (Z.ltb_spec (cs_avail_out (ds_strm X) - sb_hdr X) (sb_len1 X)); lia.
Qed.

Definition sb_brk (X : deflate_state) (flush mb : Z) : bool :=
  (sb_len X <? mb)
  && (((sb_len X =? 0) && negb (flush =? Z_FINISH)) || (flush =? Z_NO_FLUSH)
      || negb (sb_len X =? wrap32 (sb_left X + cs_avail_in (ds_strm X)))).


Definition sb_patch (X : deflate_state) (len : Z) : deflate_state :=
  let pb := ds_pending_buf X in
  let p := ds_pending X in
  let pb := arr_set pb (p - 4) (wrap8 len) in
  let pb := arr_set pb (p - 3) (wrap8 (Z.shiftr len 8)) in
  let pb := arr_set pb (p - 2) (wrap8 (Z.lnot len)) in
  let pb := arr_set pb (p - 1) (wrap8 (Z.shiftr (wrap32 (Z.lnot len)) 8)) in
  set_pending_buf X pb.

Lemma fp_len_eq : forall X, 0 <= ds_pending X < 2 ^ 31 -> 0 <= cs_avail_out (ds_strm X) ->
  fp_len X = (if cs_avail_out (ds_strm X) <? ds_pending X then cs_avail_out (ds_strm X) else ds_pending X)
  /\ 0 <= fp_len X <= ds_pending X /\ fp_len X <= cs_avail_out (ds_strm X).
Proof.
  intros X Hp Ha. unfold fp_len. rewrite wrap32_mod, Z.mod_small by lia.
  destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia.
Qed.

Definition lc_len (left len : Z) : Z := if len <? left then len else left.

Definition st_rbfin (X : deflate_state) (l : list Z) (len : Z) : deflate_state :=
  let st := ds_strm X in
  let st1 := cset_next_in st (cs_next_in st + len) in
  let st2 := cset_total_in st1 (wrap64 (cs_total_in st + len)) in
  let st3 := cset_avail_out (cs_emit st2 l) (cs_avail_out st - len) in
  let st4 := cset_total_out st3 (wrap64 (cs_total_out st + len)) in
  set_strm X st4.

End Walk.
