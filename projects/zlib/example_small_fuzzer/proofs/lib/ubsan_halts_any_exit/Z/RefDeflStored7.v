(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflStored5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflStored5.RefDeflStored2.

Module RefDeflStored3.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflStored5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflStored5.RefDeflStored2.
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

Definition sb_last (X : deflate_state) : Z :=
  if sb_len X =? wrap32 (sb_left X + cs_avail_in (ds_strm X)) then 1 else 0.

Lemma last_flag : forall x l, 0 <= l < 2 ^ 31 ->
  (if (szwrap 32 x - l) mod 2 ^ 64 <? 1 then 1 else 0) = (if l =? wrap32 x then 1 else 0).
Proof.
  intros x l Hl. pose proof (szwrap_range 32 x ltac:(lia)) as Hr.
  change (2 ^ (32 - 1)) with 2147483648 in Hr.
  destruct (Z.eqb_spec l (wrap32 x)) as [E|E].
  - assert (E' : szwrap 32 x mod 2 ^ 64 = l) by (apply (proj2 (sx32_eq_small x l Hl)); symmetry; exact E).
    assert (E2 : szwrap 32 x = l) by (destruct (Z_lt_le_dec (szwrap 32 x) 0); [rewrite <- (Z.mod_add _ 1) in E' by lia; rewrite Z.mod_small in E' by lia; lia | rewrite Z.mod_small in E' by lia; lia]).
    rewrite E2, Z.sub_diag. reflexivity.
  - assert (szwrap 32 x <> l) by (intros E2; apply E; symmetry; apply (proj1 (sx32_eq_small x l Hl)); rewrite E2, Z.mod_small by lia; reflexivity).
    destruct (Z_lt_le_dec (szwrap 32 x - l) 0).
    + rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia.
      destruct (Z.ltb_spec (szwrap 32 x - l + 1 * 2 ^ 64) 1); [lia | reflexivity].
    + rewrite Z.mod_small by lia. destruct (Z.ltb_spec (szwrap 32 x - l) 1); [lia | reflexivity].
Qed.

End Walk.
End RefDeflStored3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflStored7.RefDeflStored3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored5.

Module RefDeflStored6.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflStored5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflStored5.RefDeflStored2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflStored7.RefDeflStored3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition sb_lastv (s : deflate_state) (flush : Z) : Z :=
  if (flush =? Z_FINISH) && (sb_len s =? wrap32 (sb_left s + cs_avail_in (ds_strm s))) then 1 else 0.

Definition st_emit1 (s : deflate_state) (flush : Z) : deflate_state :=
  flush_pending (sb_patch (tr_stored_block s None 0 (sb_lastv s flush)) (sb_len s)).

Definition st_copy (s3 : deflate_state) (left len : Z) : deflate_state * Z :=
  if negb (left =? 0) then (st_lcopy s3 (lc_len left len), len - lc_len left len) else (s3, len).

Definition st_rdo (s4 : deflate_state) (n : Z) : deflate_state :=
  if negb (n =? 0) then
    let '(s, _) := read_buf s4 RB_next_out n in
    let st := ds_strm s in
    let st := cset_avail_out st (cs_avail_out st - n) in
    let st := cset_total_out st (wrap64 (cs_total_out st + n)) in
    set_strm s st
  else s4.

Ltac synrefl := lazymatch goal with |- ?a = ?b => first [constr_eq a b; exact (@eq_refl _ a) | fail "synrefl: sides differ"] end.

Lemma deflate_stored_body_eq : forall s flush mb,
  deflate_stored_body s flush mb
  = (if cs_avail_out (ds_strm s) <? sb_hdr s then (s, 0, true)
     else if sb_brk s flush mb then (s, 0, true)
     else let s3 := st_emit1 s flush in
          let '(s4, len') := st_copy s3 (sb_left s) (sb_len s) in
          (st_rdo s4 len', sb_lastv s flush, false)).
Proof.
  intros s flush mb.
  unfold deflate_stored_body, sb_brk, st_emit1, st_copy, st_rdo, sb_lastv, sb_len, sb_len1, sb_left, sb_hdr, sb_patch, st_lcopy, lc_len, MAX_STORED.
  cbv zeta.
  destruct (cs_avail_out (ds_strm s) <? Z.shiftr (ds_bi_valid s + 42) 3); [reflexivity|].
  match goal with |- (if ?c then _ else _) = (if ?c' then _ else _) => change c' with c; destruct c; [reflexivity|] end.
  set (len := if cs_avail_out (ds_strm s) - Z.shiftr (ds_bi_valid s + 42) 3 <? _ then _ else _). clearbody len.
  set (last := if (flush =? Z_FINISH) && _ then 1 else 0). clearbody last.
  set (s3 := flush_pending _). clearbody s3.
  set (left0 := wrap32 (ds_strstart s - ds_block_start s)). clearbody left0.
  destruct (negb (left0 =? 0)).
  - set (left := if len <? left0 then len else left0). clearbody left. unfold cs_emit.
    destruct s3; dsred. synrefl.
  - cbn [negb]. dsred. synrefl.
Qed.

Lemma sloop_S : forall f s flush mb,
  deflate_stored_loop (S f) s flush mb
  = (let '(s1, last, broke) := deflate_stored_body s flush mb in
     if broke then (s1, last) else if last =? 0 then deflate_stored_loop f s1 flush mb else (s1, last)).
Proof. reflexivity. Qed.


Ltac krefl := lazymatch goal with |- ?a = _ => exact_no_check (@eq_refl _ a) end.

Definition st_wupd (s : deflate_state) (used : Z) : deflate_state :=
  if negb (Z.eqb used 0) then
    let s :=
      if Z.leb (ds_w_size s) used then
        let s := set_matches s 2 in
        let st := ds_strm s in
        let s := set_window s (arr_upd (ds_window s) 0
                   (arr_slice (cs_input st) (cs_next_in st - ds_w_size s) (ds_w_size s))) in
        let s := set_strstart s (ds_w_size s) in
        set_insert s (ds_strstart s)
      else
        let s :=
          if Z.leb (ds_window_size s - ds_strstart s) used then
            let s := set_strstart s (ds_strstart s - ds_w_size s) in
            let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s)) in
            let s := if Z.ltb (ds_matches s) 2 then set_matches s (ds_matches s + 1) else s in
            if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s
          else s in
        let st := ds_strm s in
        let s := set_window s (arr_upd (ds_window s) (ds_strstart s)
                   (arr_slice (cs_input st) (cs_next_in st - used) used)) in
        let s := set_strstart s (ds_strstart s + used) in
        set_insert s (ds_insert s + MIN used (wrap32 (ds_w_size s - ds_insert s))) in
    set_block_start s (ds_strstart s)
  else s.

Definition st_slide3 (s : deflate_state) (have : Z) : deflate_state * Z :=
  if Z.ltb have (cs_avail_in (ds_strm s)) && Z.leb (ds_w_size s) (ds_block_start s) then
    let s := set_block_start s (ds_block_start s - ds_w_size s) in
    let s := set_strstart s (ds_strstart s - ds_w_size s) in
    let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s)) in
    let s := if Z.ltb (ds_matches s) 2 then set_matches s (ds_matches s + 1) else s in
    let have := wrap32 (have + ds_w_size s) in
    let s := if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s in
    (s, have)
  else (s, have).

Definition st_fillw (s : deflate_state) (have : Z) : deflate_state :=
  if negb (Z.eqb have 0) then
    let '(s, _) := read_buf s (RB_window (ds_strstart s)) have in
    let s := set_strstart s (ds_strstart s + have) in
    set_insert s (ds_insert s + MIN have (wrap32 (ds_w_size s - ds_insert s)))
  else s.

Definition st_final (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  let have := t_have s in
  let min_block := t_mb s in
  let left := wrap32 (ds_strstart s - ds_block_start s) in
  if Z.leb min_block left
     || ((negb (Z.eqb left 0) || Z.eqb flush Z_FINISH) && negb (Z.eqb flush Z_NO_FLUSH)
         && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.leb left have)
  then
    let len := MIN left have in
    let last := if Z.eqb flush Z_FINISH && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.eqb len left
                then 1 else 0 in
    let s := tr_stored_block s (Some (ds_block_start s)) len last in
    let s := set_block_start s (ds_block_start s + len) in
    let s := flush_pending s in
    (s, if negb (Z.eqb last 0) then finish_started else need_more)
  else (s, need_more).

Definition post_slide (s : deflate_state) (have flush : Z) : deflate_state * block_state :=
    let have := if Z.ltb (cs_avail_in (ds_strm s)) have then cs_avail_in (ds_strm s) else have in
    let s :=
      if negb (Z.eqb have 0) then
        let '(s, _) := read_buf s (RB_window (ds_strstart s)) have in
        let s := set_strstart s (ds_strstart s + have) in
        set_insert s (ds_insert s + MIN have (wrap32 (ds_w_size s - ds_insert s)))
      else s in
    let s := if Z.ltb (ds_high_water s) (ds_strstart s) then set_high_water s (ds_strstart s) else s in
    let have := Z.shiftr (ds_bi_valid s + 42) 3 in
    let have := MIN (ds_pending_buf_size s - have) MAX_STORED in
    let min_block := MIN have (ds_w_size s) in
    let left := wrap32 (ds_strstart s - ds_block_start s) in
    if Z.leb min_block left
       || ((negb (Z.eqb left 0) || Z.eqb flush Z_FINISH) && negb (Z.eqb flush Z_NO_FLUSH)
           && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.leb left have)
    then
      let len := MIN left have in
      let last := if Z.eqb flush Z_FINISH && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.eqb len left
                  then 1 else 0 in
      let s := tr_stored_block s (Some (ds_block_start s)) len last in
      let s := set_block_start s (ds_block_start s + len) in
      let s := flush_pending s in
      (s, if negb (Z.eqb last 0) then finish_started else need_more)
    else (s, need_more).

Definition post_hw (s : deflate_state) (last flush : Z) : deflate_state * block_state :=
  if negb (Z.eqb last 0) then (s, finish_done)
  else if negb (Z.eqb flush Z_NO_FLUSH) && negb (Z.eqb flush Z_FINISH)
          && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.eqb (ds_strstart s) (ds_block_start s)
  then (s, block_done)
  else
    let have := wrap32 (ds_window_size s - ds_strstart s) in
    let '(s, have) :=
      if Z.ltb have (cs_avail_in (ds_strm s)) && Z.leb (ds_w_size s) (ds_block_start s) then
        let s := set_block_start s (ds_block_start s - ds_w_size s) in
        let s := set_strstart s (ds_strstart s - ds_w_size s) in
        let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s)) in
        let s := if Z.ltb (ds_matches s) 2 then set_matches s (ds_matches s + 1) else s in
        let have := wrap32 (have + ds_w_size s) in
        let s := if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s in
        (s, have)
      else (s, have) in
    post_slide s have flush.

Definition post_loop (s0 : deflate_state) (flush : Z) (p : deflate_state * Z) : deflate_state * block_state :=
  let used := cs_avail_in (ds_strm s0) in
  let '(s, last) := p in
  let used := wrap32 (used - cs_avail_in (ds_strm s)) in
  let s :=
    if negb (Z.eqb used 0) then
      let s :=
        if Z.leb (ds_w_size s) used then
          let s := set_matches s 2 in
          let st := ds_strm s in
          let s := set_window s (arr_upd (ds_window s) 0
                     (arr_slice (cs_input st) (cs_next_in st - ds_w_size s) (ds_w_size s))) in
          let s := set_strstart s (ds_w_size s) in
          set_insert s (ds_strstart s)
        else
          let s :=
            if Z.leb (ds_window_size s - ds_strstart s) used then
              let s := set_strstart s (ds_strstart s - ds_w_size s) in
              let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s)) in
              let s := if Z.ltb (ds_matches s) 2 then set_matches s (ds_matches s + 1) else s in
              if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s
            else s in
          let st := ds_strm s in
          let s := set_window s (arr_upd (ds_window s) (ds_strstart s)
                     (arr_slice (cs_input st) (cs_next_in st - used) used)) in
          let s := set_strstart s (ds_strstart s + used) in
          set_insert s (ds_insert s + MIN used (wrap32 (ds_w_size s - ds_insert s))) in
      set_block_start s (ds_strstart s)
    else s in
  let s := if Z.ltb (ds_high_water s) (ds_strstart s) then set_high_water s (ds_strstart s) else s in
  post_hw s last flush.

Lemma deflate_stored_eq1 : forall s flush,
  deflate_stored s flush
  = post_loop s flush (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm s) + 1)) s flush
                         (wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s)))).
Proof. intros. krefl. Qed.

Local Strategy 1000 [post_hw].

Lemma post_loop_eq : forall s0 flush s1 last,
  post_loop s0 flush (s1, last)
  = post_hw (hw_st (st_wupd s1 (wrap32 (cs_avail_in (ds_strm s0) - cs_avail_in (ds_strm s1))))) last flush.
Proof. intros. krefl. Qed.

Local Strategy transparent [post_hw].

Lemma post_hw_eq : forall s last flush,
  post_hw s last flush
  = (if negb (last =? 0) then (s, finish_done)
     else if negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH)
             && (cs_avail_in (ds_strm s) =? 0) && (ds_strstart s =? ds_block_start s) then (s, block_done)
     else let '(s4, have) := st_slide3 s (wrap32 (ds_window_size s - ds_strstart s)) in post_slide s4 have flush).
Proof. intros. krefl. Qed.

Lemma post_slide_eq : forall s4 have flush,
  post_slide s4 have flush = st_final (hw_st (st_fillw s4 (fmin have (cs_avail_in (ds_strm s4))))) flush.
Proof. intros. krefl. Qed.
End RefDeflStored6.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflStored7.RefDeflStored6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac synrefl := lazymatch goal with |- ?a = ?b => first [constr_eq a b; exact (@eq_refl _ a) | fail "synrefl: sides differ"] end.
Ltac krefl := lazymatch goal with |- ?a = _ => exact_no_check (@eq_refl _ a) end.


Definition st_trip (s : deflate_state) (flush : Z) : deflate_state :=
  let s3 := st_emit1 s flush in
  st_rdo (fst (st_copy s3 (sb_left s) (sb_len s))) (snd (st_copy s3 (sb_left s) (sb_len s))).

Definition sb_broke (s : deflate_state) (flush mb : Z) : bool :=
  (cs_avail_out (ds_strm s) <? sb_hdr s) || sb_brk s flush mb.

Lemma sb_broke_eq : forall s flush mb,
  sb_broke s flush mb = (if cs_avail_out (ds_strm s) <? sb_hdr s then true else sb_brk s flush mb).
Proof. intros. unfold sb_broke. destruct (_ <? _); reflexivity. Qed.

Lemma st_body_eq : forall s flush mb,
  deflate_stored_body s flush mb
  = (if sb_broke s flush mb then (s, 0, true) else (st_trip s flush, sb_lastv s flush, false)).
Proof.
  intros s flush mb. rewrite deflate_stored_body_eq. unfold sb_broke, st_trip.
  destruct (cs_avail_out (ds_strm s) <? sb_hdr s); [reflexivity|]. cbn [orb].
  destruct (sb_brk s flush mb); [reflexivity|]. cbv zeta.
  destruct (st_copy (st_emit1 s flush) (sb_left s) (sb_len s)) as [s4 len']. reflexivity.
Qed.

Lemma sloop_S' : forall f s flush mb,
  deflate_stored_loop (S f) s flush mb
  = (if sb_broke s flush mb then (s, 0)
     else if sb_lastv s flush =? 0 then deflate_stored_loop f (st_trip s flush) flush mb
     else (st_trip s flush, sb_lastv s flush)).
Proof.
  intros f s flush mb. rewrite sloop_S, st_body_eq. destruct (sb_broke s flush mb); reflexivity.
Qed.

Lemma sb_lastv_nf : forall s flush, flush <> Z_FINISH -> sb_lastv s flush = 0.
Proof.
  intros s flush Hf. unfold sb_lastv. destruct (Z.eqb_spec flush Z_FINISH); [lia|]. reflexivity.
Qed.

Lemma sb_lastv_f : forall s, sb_lastv s Z_FINISH = sb_last s.
Proof. intros s. unfold sb_lastv, sb_last. cbn [Z.eqb Z_FINISH Pos.eqb andb]. reflexivity. Qed.

Lemma sb_last_range : forall s, 0 <= sb_last s <= 1.
Proof. intros s. unfold sb_last. destruct (_ =? _); lia. Qed.

Lemma sb_lastv_range : forall s flush, 0 <= sb_lastv s flush <= 1.
Proof. intros s flush. unfold sb_lastv. destruct (_ && _); lia. Qed.


Definition rb_mid (s : deflate_state) (n : Z) : deflate_state :=
  let st1 := cset_avail_in (ds_strm s) (cs_avail_in (ds_strm s) - n) in
  let bytes := arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n in
  let s1 := set_strm s st1 in
  if ds_wrap s =? 1 then set_strm s1 (cset_adler st1 (adler32_upd (cs_adler (ds_strm s)) bytes))
  else if ds_wrap s =? 2 then set_strm s1 (cset_adler st1 (crc32_upd (cs_adler (ds_strm s)) bytes))
  else s1.

Definition rbw_mid (s : deflate_state) (off n : Z) : deflate_state :=
  let st1 := cset_avail_in (ds_strm s) (cs_avail_in (ds_strm s) - n) in
  let bytes := arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n in
  let s1 := set_window (set_strm s st1) (arr_upd (ds_window s) off bytes) in
  if ds_wrap s =? 1 then set_strm s1 (cset_adler st1 (adler32_upd (cs_adler (ds_strm s)) bytes))
  else if ds_wrap s =? 2 then set_strm s1 (cset_adler st1 (crc32_upd (cs_adler (ds_strm s)) bytes))
  else s1.

Lemma rb_len_eq : forall n ai, 0 < n <= ai -> (if n <? ai then n else ai) = n.
Proof. intros n ai H. destruct (Z.ltb_spec n ai); lia. Qed.

Lemma st_rdo_eq : forall s n, 0 < n <= cs_avail_in (ds_strm s) ->
  st_rdo s n = st_rbfin (rb_mid s n) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n) n.
Proof.
  intros s n Hn. unfold st_rdo, read_buf, rb_mid, st_rbfin.
  replace (negb (n =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
  cbv zeta. rewrite (rb_len_eq n (cs_avail_in (ds_strm s)) Hn).
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv iota beta.
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; unfold cs_emit; dsred; reflexivity.
Qed.

Lemma st_fillw_eq : forall ds s n, ds_w_size s = ds_w_size ds -> 0 < n <= cs_avail_in (ds_strm s) ->
  st_fillw s n = st_rbw ds (rbw_mid s (ds_strstart s) n) n.
Proof.
  intros ds s n Hws Hn. unfold st_fillw, read_buf, rbw_mid, st_rbw, ins_add.
  replace (negb (n =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
  cbv zeta. rewrite (rb_len_eq n (cs_avail_in (ds_strm s)) Hn).
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv iota beta. rewrite <- Hws. dsred.
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; dsred; reflexivity.
Qed.

Lemma st_fillw_0 : forall s, st_fillw s 0 = s.
Proof. intros s. unfold st_fillw. reflexivity. Qed.


Lemma st_wupd_0 : forall s, st_wupd s 0 = s.
Proof. intros s. reflexivity. Qed.

Lemma st_wupd_sup : forall s used, used <> 0 -> ds_w_size s <= used ->
  st_wupd s used
  = (let X1 := set_matches s 2 in
     let X2 := set_window X1 (arr_upd (ds_window X1) 0 (arr_slice (cs_input (ds_strm X1)) (cs_next_in (ds_strm X1) - ds_w_size s) (ds_w_size s))) in
     let X3 := set_strstart X2 (ds_w_size s) in
     set_block_start (set_insert X3 (ds_w_size s)) (ds_w_size s)).
Proof.
  intros s used Hu Hw. unfold st_wupd.
  replace (negb (used =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
  replace (ds_w_size s <=? used) with true by (symmetry; apply Z.leb_le; lia).
  cbv iota zeta. dsred. reflexivity.
Qed.

Lemma st_wupd_app : forall s used, used <> 0 -> used < ds_w_size s -> used < ds_window_size s - ds_strstart s ->
  st_wupd s used
  = (let X2 := set_window s (arr_upd (ds_window s) (ds_strstart s) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s) - used) used)) in
     let X3 := set_strstart X2 (ds_strstart X2 + used) in
     set_block_start (set_insert X3 (ins_add (ds_insert X2) used (ds_w_size s))) (ds_strstart X2 + used)).
Proof.
  intros s used Hu Hw Hsl. unfold st_wupd, ins_add.
  replace (negb (used =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
  replace (ds_w_size s <=? used) with false by (symmetry; apply Z.leb_gt; lia).
  replace (ds_window_size s - ds_strstart s <=? used) with false by (symmetry; apply Z.leb_gt; lia).
  cbv iota zeta. dsred. reflexivity.
Qed.

Lemma st_wupd_sla : forall s used, used <> 0 -> used < ds_w_size s -> ds_window_size s - ds_strstart s <= used ->
  st_wupd s used
  = (let X1 := set_strstart s (ds_strstart s - ds_w_size s) in
     let X2 := set_window X1 (arr_upd (ds_window X1) 0 (arr_slice (ds_window X1) (ds_w_size s) (ds_strstart s - ds_w_size s))) in
     let X3 := sl_fix X2 in
     let X4 := set_window X3 (arr_upd (ds_window X3) (ds_strstart X3) (arr_slice (cs_input (ds_strm X3)) (cs_next_in (ds_strm X3) - used) used)) in
     let X5 := set_strstart X4 (ds_strstart X4 + used) in
     set_block_start (set_insert X5 (ins_add (ds_insert X4) used (ds_w_size s))) (ds_strstart X4 + used)).
Proof.
  intros s used Hu Hw Hsl. unfold st_wupd, ins_add, sl_fix.
  replace (negb (used =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
  replace (ds_w_size s <=? used) with false by (symmetry; apply Z.leb_gt; lia).
  replace (ds_window_size s - ds_strstart s <=? used) with true by (symmetry; apply Z.leb_le; lia).
  cbv iota zeta. rewrite arr_blit_upd. dsred.
  destruct (ds_matches s <? 2); dsred; destruct (ds_strstart s - ds_w_size s <? ds_insert s); dsred; reflexivity.
Qed.

Lemma st_slide3_true : forall s have,
  (have <? cs_avail_in (ds_strm s)) && (ds_w_size s <=? ds_block_start s) = true ->
  st_slide3 s have
  = (let X1 := set_block_start (set_strstart s (ds_strstart s - ds_w_size s)) (ds_block_start s - ds_w_size s) in
     let X2 := set_window X1 (arr_upd (ds_window X1) 0 (arr_slice (ds_window X1) (ds_w_size s) (ds_strstart s - ds_w_size s))) in
     (sl_fix X2, wrap32 (have + ds_w_size s))).
Proof.
  intros s have Hc. unfold st_slide3, sl_fix. rewrite Hc. cbv iota zeta. rewrite arr_blit_upd. dsred.
  destruct (ds_matches s <? 2); dsred; destruct (ds_strstart s - ds_w_size s <? ds_insert s); dsred; reflexivity.
Qed.

Lemma st_slide3_false : forall s have,
  (have <? cs_avail_in (ds_strm s)) && (ds_w_size s <=? ds_block_start s) = false ->
  st_slide3 s have = (s, have).
Proof. intros s have Hc. unfold st_slide3. rewrite Hc. reflexivity. Qed.

Definition fin_cond (s : deflate_state) (flush : Z) : bool :=
  let have := t_have s in
  let left := wrap32 (ds_strstart s - ds_block_start s) in
  (t_mb s <=? left)
  || ((negb (left =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH)
      && (cs_avail_in (ds_strm s) =? 0) && (left <=? have)).

Definition fin_len (s : deflate_state) : Z := MIN (wrap32 (ds_strstart s - ds_block_start s)) (t_have s).

Definition fin_last (s : deflate_state) (flush : Z) : Z :=
  if (flush =? Z_FINISH) && (cs_avail_in (ds_strm s) =? 0) && (fin_len s =? wrap32 (ds_strstart s - ds_block_start s)) then 1 else 0.

Definition st_femit (s : deflate_state) (flush : Z) : deflate_state :=
  let s1 := tr_stored_block s (Some (ds_block_start s)) (fin_len s) (fin_last s flush) in
  flush_pending (set_block_start s1 (ds_block_start s1 + fin_len s)).

Lemma st_final_eq : forall s flush,
  st_final s flush
  = (if fin_cond s flush then (st_femit s flush, if negb (fin_last s flush =? 0) then finish_started else need_more)
     else (s, need_more)).
Proof.
  intros s flush. unfold st_final, fin_cond, st_femit, fin_last, fin_len, t_mb, t_have. cbv zeta.
  destruct (_ || _); reflexivity.
Qed.



Record so_inv (s : deflate_state) : Prop := {
  vi_bv : 0 <= ds_bi_valid s <= 16;
  vi_ai : 0 <= cs_avail_in (ds_strm s) < 2 ^ 32;
  vi_ni : 0 <= cs_next_in (ds_strm s);
  vi_inlen : cs_next_in (ds_strm s) + cs_avail_in (ds_strm s) <= arr_len (cs_input (ds_strm s));
  vi_ib : forall i, 0 <= i < arr_len (cs_input (ds_strm s)) -> 0 <= arr_get (cs_input (ds_strm s)) i < 256;
  vi_ti : 0 <= cs_total_in (ds_strm s) < 2 ^ 64;
  vi_to : 0 <= cs_total_out (ds_strm s) < 2 ^ 64;
  vi_wrap : 0 <= ds_wrap s <= 2;
  vi_ad : 1 <= ds_wrap s -> 0 <= cs_adler (ds_strm s) < 2 ^ 64;
  vi_str : ds_strstart s <= 2 * ds_w_size s;
  vi_bs : 0 <= ds_block_start s <= ds_strstart s;
  vi_wsz : ds_window_size s = 2 * ds_w_size s;
  vi_ins : 0 <= ds_insert s <= ds_w_size s;
  vi_mat : 0 <= ds_matches s < 2 ^ 31;
  vi_hw : 0 <= ds_high_water s < 2 ^ 64;
  vi_pbs : 7 <= ds_pending_buf_size s < 2 ^ 62;
  vi_wb : forall j, 0 <= j < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) j < 256 }.

Definition so_fp_ok (PBL : Z) (s2 : deflate_state) : Prop :=
  BINV PBL s2
  /\ let s3 := tr_flush_bits s2 in
     0 <= ds_pending s3 /\ ds_pending s3 + 1 < 2 ^ 31 /\ ds_pending s3 <= PBL
     /\ 0 <= ds_pending_out s3 /\ ds_pending_out s3 + fp_len s3 <= PBL
     /\ 0 <= cs_total_out (ds_strm s3) < 2 ^ 64.

Definition so_emit_ok (s : deflate_state) (flush : Z) : Prop :=
  let PBL := ds_lit_bufsize s * 4 in
  let s1 := tr_stored_block s None 0 (sb_lastv s flush) in
  BINV PBL s /\ 4 <= ds_pending s1 <= PBL
  /\ so_fp_ok PBL (sb_patch s1 (sb_len s)).

Definition so_copy_ok (s : deflate_state) (flush : Z) : Prop :=
  let s4 := st_emit1 s flush in
  let n1 := lc_len (sb_left s) (sb_len s) in
  sb_left s <> 0 ->
  0 <= ds_block_start s4 /\ ds_block_start s4 + n1 <= 2 * ds_w_size s4
  /\ n1 <= cs_avail_out (ds_strm s4) /\ 0 <= cs_total_out (ds_strm s4) < 2 ^ 64.

Definition so_rdo_ok (s : deflate_state) (flush : Z) : Prop :=
  let s4 := st_emit1 s flush in
  let s5 := fst (st_copy s4 (sb_left s) (sb_len s)) in
  let n2 := snd (st_copy s4 (sb_left s) (sb_len s)) in
  so_inv s5 /\ (n2 <> 0 -> 0 < n2 <= cs_avail_in (ds_strm s5) /\ n2 <= cs_avail_out (ds_strm s5)).

Definition so_trip_ok (s : deflate_state) (flush mb : Z) : Prop :=
  so_inv s
  /\ (sb_broke s flush mb = false ->
      so_emit_ok s flush /\ so_copy_ok s flush /\ so_rdo_ok s flush /\ so_inv (st_trip s flush)).

Fixpoint so_loop_ok (fuel : nat) (s : deflate_state) (flush mb : Z) : Prop :=
  match fuel with
  | O => False
  | S f => so_trip_ok s flush mb
           /\ (sb_broke s flush mb = false -> sb_lastv s flush = 0 -> so_loop_ok f (st_trip s flush) flush mb)
  end.

Lemma so_loop_ok_S : forall f s flush mb,
  so_loop_ok (S f) s flush mb
  = (so_trip_ok s flush mb /\ (sb_broke s flush mb = false -> sb_lastv s flush = 0 -> so_loop_ok f (st_trip s flush) flush mb)).
Proof. reflexivity. Qed.

Definition so_final_ok (s4 : deflate_state) (flush : Z) : Prop :=
  let PBL := ds_lit_bufsize s4 * 4 in
  fin_cond s4 flush = true ->
  let s5 := tr_stored_block s4 (Some (ds_block_start s4)) (fin_len s4) (fin_last s4 flush) in
  BINV PBL s4 /\ ds_pending s5 <= PBL
  /\ so_fp_ok PBL (set_block_start s5 (ds_block_start s5 + fin_len s4)).

Definition so_tail_ok (s0 : deflate_state) (flush : Z) (sL : deflate_state) (last : Z) : Prop :=
  0 <= cs_avail_in (ds_strm sL) <= cs_avail_in (ds_strm s0)
  /\ so_inv sL
  /\ let used := cs_avail_in (ds_strm s0) - cs_avail_in (ds_strm sL) in
     used <= cs_next_in (ds_strm sL)
  /\ let s2 := hw_st (st_wupd sL used) in
     so_inv s2
  /\ (last = 0 ->
      let s3 := fst (st_slide3 s2 (wrap32 (ds_window_size s2 - ds_strstart s2))) in
      let have := snd (st_slide3 s2 (wrap32 (ds_window_size s2 - ds_strstart s2))) in
      so_inv s3
      /\ let s4 := hw_st (st_fillw s3 (fmin have (cs_avail_in (ds_strm s3)))) in
         so_inv s4 /\ so_final_ok s4 flush).

Definition stored_safe (ds : deflate_state) (flush : Z) : Prop :=
  let mb := wrap32 (MIN (ds_pending_buf_size ds - 5) (ds_w_size ds)) in
  let fuel := Z.to_nat (cs_avail_out (ds_strm ds) + 1) in
  DWF ds
  /\ so_loop_ok fuel ds flush mb
  /\ so_tail_ok ds flush (fst (deflate_stored_loop fuel ds flush mb)) (snd (deflate_stored_loop fuel ds flush mb)).


Lemma deflate_stored_eq : forall s flush,
  deflate_stored s flush
  = (let mb := wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s)) in
     let fuel := Z.to_nat (cs_avail_out (ds_strm s) + 1) in
     let sL := fst (deflate_stored_loop fuel s flush mb) in
     let last := snd (deflate_stored_loop fuel s flush mb) in
     let s2 := hw_st (st_wupd sL (wrap32 (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL)))) in
     if negb (last =? 0) then (s2, finish_done)
     else if negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH)
             && (cs_avail_in (ds_strm s2) =? 0) && (ds_strstart s2 =? ds_block_start s2) then (s2, block_done)
     else
       let s3 := fst (st_slide3 s2 (wrap32 (ds_window_size s2 - ds_strstart s2))) in
       let have := snd (st_slide3 s2 (wrap32 (ds_window_size s2 - ds_strstart s2))) in
       st_final (hw_st (st_fillw s3 (fmin have (cs_avail_in (ds_strm s3))))) flush).
Proof.
  intros s flush. rewrite deflate_stored_eq1. cbv zeta.
  destruct (deflate_stored_loop _ s flush _) as [sL last]. cbn [fst snd].
  rewrite post_loop_eq, post_hw_eq.
  destruct (negb (last =? 0)); [reflexivity|].
  destruct (_ && _); [reflexivity|].
  destruct (st_slide3 _ _) as [s3 have]. cbn [fst snd]. apply post_slide_eq.
Qed.

Lemma MBv_wrap : forall ds, 7 <= ds_pending_buf_size ds -> 0 <= ds_w_size ds < 2 ^ 32 ->
  wrap32 (MIN (ds_pending_buf_size ds - 5) (ds_w_size ds)) = MBv ds.
Proof.
  intros ds H Hw. unfold MBv, MIN. rewrite wrap32_mod. apply Z.mod_small.
  destruct (Z.ltb_spec (ds_w_size ds) (ds_pending_buf_size ds - 5)); lia.
Qed.
