(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored2.
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

Definition sl_fix (X : deflate_state) : deflate_state :=
  let X1 := if ds_matches X <? 2 then set_matches X (ds_matches X + 1) else X in
  if ds_strstart X1 <? ds_insert X1 then set_insert X1 (ds_strstart X1) else X1.

Definition ins_add (ins used ws : Z) : Z := ins + MIN used (wrap32 (ws - ins)).

Lemma ins_add_eq : forall ins used ws, 0 <= ins <= ws -> ws < 2 ^ 32 -> 0 <= used ->
  ins_add ins used ws = ins + (if used <? ws - ins then used else ws - ins) /\ ins <= ins_add ins used ws <= ws.
Proof.
  intros ins used ws Hi Hws Hu. unfold ins_add, MIN. rewrite wrap32_mod, Z.mod_small by lia.
  destruct (Z.ltb_spec (ws - ins) used), (Z.ltb_spec used (ws - ins)); lia.
Qed.

Definition hw_st (X : deflate_state) : deflate_state :=
  if ds_high_water X <? ds_strstart X then set_high_water X (ds_strstart X) else X.

Definition fmin (have ai : Z) : Z := if ai <? have then ai else have.

Definition st_rbw (X : deflate_state) (n : Z) : deflate_state :=
  let st := ds_strm X in
  let st1 := cset_next_in st (cs_next_in st + n) in
  let st2 := cset_total_in st1 (wrap64 (cs_total_in st + n)) in
  set_insert (set_strstart (set_strm X st2) (ds_strstart X + n)) (ins_add (ds_insert X) n ws).

Definition t_have (X : deflate_state) : Z := MIN (ds_pending_buf_size X - Z.shiftr (ds_bi_valid X + 42) 3) MAX_STORED.
Definition t_mb (X : deflate_state) : Z := MIN (t_have X) (ds_w_size X).

Lemma t_have_eq : forall X, 0 <= ds_bi_valid X <= 16 -> 7 <= ds_pending_buf_size X ->
  t_have X = (if ds_pending_buf_size X - (ds_bi_valid X + 42) / 2 ^ 3 <? 65536 then ds_pending_buf_size X - (ds_bi_valid X + 42) / 2 ^ 3 else 65535)
  /\ 0 <= t_have X <= 65535 /\ 5 <= (ds_bi_valid X + 42) / 2 ^ 3 <= 7.
Proof.
  intros X Hbv Hpbs. unfold t_have, MIN, MAX_STORED. rewrite Z.shiftr_div_pow2 by lia.
  assert (H57 : 5 <= (ds_bi_valid X + 42) / 2 ^ 3 <= 7) by (change (2 ^ 3) with 8; Z.to_euclidean_division_equations; lia).
  destruct (Z.ltb_spec 65535 (ds_pending_buf_size X - (ds_bi_valid X + 42) / 2 ^ 3)), (Z.ltb_spec (ds_pending_buf_size X - (ds_bi_valid X + 42) / 2 ^ 3) 65536); lia.
Qed.

Lemma t_mb_eq : forall X, 0 <= t_have X -> t_mb X = (if t_have X <=? ds_w_size X then t_have X else ds_w_size X).
Proof.
  intros X H. unfold t_mb, MIN. destruct (Z.ltb_spec (ds_w_size X) (t_have X)), (Z.leb_spec (t_have X) (ds_w_size X)); lia.
Qed.

Definition f4v (fl : Z) : Z := if (fl + -4) mod 2 ^ 64 <? 1 then 1 else 0.
Definition orv (fl left : Z) : Z := Z.lor (f4v fl) (if 0 <? left then 1 else 0).
Definition lastv (ai have left : Z) : Z :=
  Z.land (if szwrap 32 ai mod 2 ^ 64 <? 1 then 1 else 0) (if (if have <? left then 1 else 0) <? 1 then 1 else 0).

Definition tlen (have left : Z) : Z := if left <? have then left else have.

Definition MBv : Z := MIN (ds_pending_buf_size ds - 5) (ds_w_size ds).

End Walk.
