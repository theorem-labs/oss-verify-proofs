(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.

Module RefInflateA_LENLENS2.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma u16_order : tab_u16 order_a 19 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma order_lt19 : forall i, 0 <= i < 19 -> 0 <= arr_get order_a i < 19.
Proof.
  intros i Hi.
  assert (H : forallb (fun j => (0 <=? arr_get order_a (Z.of_nat j)) && (arr_get order_a (Z.of_nat j) <? 19)) (seq 0 19) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma ll_s_facts : forall s h,
  is_have (ll_s s h) = wrap32 (is_have s + 1) /\ is_ncode (ll_s s h) = is_ncode s /\ is_mode (ll_s s h) = is_mode s
  /\ is_window (ll_s s h) = is_window s /\ is_window_blk (ll_s s h) = is_window_blk s /\ is_wsize (ll_s s h) = is_wsize s
  /\ is_self_blk (ll_s s h) = is_self_blk s /\ is_wbits (ll_s s h) = is_wbits s
  /\ ll_s s h = iset_have (iset_lens s (arr_set (is_lens s) (arr_get order_a (is_have s)) (wrap16 (BITSv h 3)))) (wrap32 (is_have s + 1)).
Proof. intros. repeat split; reflexivity. Qed.
Lemma ll_r_facts : forall r,
  ir_next (ll_r r) = ir_next r /\ ir_have (ll_r r) = ir_have r /\ ir_put (ll_r r) = ir_put r /\ ir_left (ll_r r) = ir_left r
  /\ ir_hold (ll_r r) = Z.shiftr (ir_hold r) 3 /\ ir_bits (ll_r r) = wrap32 (ir_bits r - 3)
  /\ ir_in (ll_r r) = ir_in r /\ ir_out (ll_r r) = ir_out r /\ ir_ret (ll_r r) = ir_ret r.
Proof. intros. repeat split; reflexivity. Qed.

Lemma iwf_set_lens : forall st a, arr_len a = 320 -> (forall i, 0 <= i < 320 -> 0 <= arr_get a i < 2 ^ 16) -> iwf st -> iwf (iset_lens st a).
Proof.
  intros st a Hl Hb H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.
Lemma iwf_set_have : forall st v, 0 <= v < 2 ^ 32 -> iwf st -> iwf (iset_have st v).
Proof. intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len] in *. decompose [and] H. repeat apply conj; first [assumption | lia]. Qed.

Lemma wrap16_bits3 : forall h, 0 <= h -> wrap16 (BITSv h 3) = h mod 2 ^ 3.
Proof.
  intros h Hh. rewrite BITSv_land by lia. unfold wrap16. rewrite Z.land_ones by lia.
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small.
  pose proof (Z.mod_pos_bound h (2 ^ 3) ltac:(lia)). lia.
Qed.

Lemma ll_s_iwf : forall s h, 0 <= h -> 0 <= is_have s < 19 -> iwf s -> iwf (ll_s s h).
Proof.
  intros s h Hh Hhv Hwf. unfold ll_s.
  pose proof (iwf_x s Hwf) as X. unfold iwfx in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xll & _ & _ & Xlb & _).
  apply iwf_set_have; [rewrite wrap32_id by lia; lia|].
  apply iwf_set_lens; [rewrite arr_len_set; exact Xll | | exact Hwf].
  intros i Hi. rewrite arr_get_set. destruct ((arr_get order_a (is_have s) =? i) && _); [| apply Xlb; exact Hi].
  rewrite wrap16_bits3 by lia. pose proof (Z.mod_pos_bound h (2 ^ 3) ltac:(lia)). lia.
Qed.

Lemma lenlens_while1_stop : forall k s c r, is_ncode s <= is_have s -> lenlens_while1 k (mkW s c r) = ARun tt (mkW s c r).
Proof.
  intros k s c r H. destruct k; [reflexivity|]. rewrite lenlens_while1_S. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
Qed.

Section LL1.
End LL1.
End RefInflateA_LENLENS2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.

Module RefInflateA_LENLENS4.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Lemma iwf_ll_tab : forall st tbl nxt lb wk,
  arr_len tbl = 1444 -> arr_len wk = 288 -> 0 <= nxt <= 1444 -> 0 <= lb < 2 ^ 32 ->
  (forall i, 0 <= i < 1444 -> 0 <= arr_get tbl i < 2 ^ 32) ->
  (forall i, 0 <= i < 288 -> 0 <= arr_get wk i < 2 ^ 16) ->
  iwf st -> iwf (ll_tab st tbl nxt lb wk).
Proof.
  intros st tbl nxt lb wk H1 H2 H3 H4 H5 H6 H. unfold ll_tab, iwf, iwfx in *.
  destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.

Lemma ll_tab_facts : forall s tbl nxt lb wk,
  is_mode (ll_tab s tbl nxt lb wk) = is_mode s /\ is_window (ll_tab s tbl nxt lb wk) = is_window s
  /\ is_window_blk (ll_tab s tbl nxt lb wk) = is_window_blk s /\ is_wsize (ll_tab s tbl nxt lb wk) = is_wsize s
  /\ is_self_blk (ll_tab s tbl nxt lb wk) = is_self_blk s /\ is_wbits (ll_tab s tbl nxt lb wk) = is_wbits s
  /\ is_lens (ll_tab s tbl nxt lb wk) = is_lens s /\ is_work (ll_tab s tbl nxt lb wk) = wk /\ is_codes (ll_tab s tbl nxt lb wk) = tbl
  /\ is_nlen (ll_tab s tbl nxt lb wk) = is_nlen s /\ is_ndist (ll_tab s tbl nxt lb wk) = is_ndist s /\ is_have (ll_tab s tbl nxt lb wk) = is_have s.
Proof. intros. repeat split; reflexivity. Qed.

Definition ll_pre_s (s : inflate_state) : inflate_state := iset_lencode (iset_next (iset_lenbits s 7) 0) (CDyn 0).

Section ArmLLcall.
End ArmLLcall.
End RefInflateA_LENLENS4.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS4.

Module RefInflateA_LENLENS3.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma szwrap32_mod64_lt : forall a b, 0 <= a -> a < b -> b < 2 ^ 31 ->
  szwrap 32 a mod 2 ^ 64 < szwrap 32 b mod 2 ^ 64.
Proof.
  intros a b Ha Hab Hb. rewrite !szwrap32_small by lia. rewrite !Z.mod_small by lia. lia.
Qed.
Lemma szwrap32_mod64_ge : forall a b, 0 <= a -> a <= b -> b < 2 ^ 32 -> a < 2 ^ 31 ->
  szwrap 32 a mod 2 ^ 64 <= szwrap 32 b mod 2 ^ 64.
Proof.
  intros a b Ha Hab Hb Ha31. rewrite (szwrap32_small a) by lia. rewrite (Z.mod_small a) by lia.
  destruct (Z_lt_le_dec b (2 ^ 31)) as [Hs|Hs].
  - rewrite szwrap32_small by lia. rewrite Z.mod_small by lia. lia.
  - unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
    change (2 ^ 31) with 2147483648 in *. change (2 ^ 32) with 4294967296 in Hb.
    Z.to_euclidean_division_equations; lia.
Qed.
End RefInflateA_LENLENS3.

Module RefInflateA_LENLENS.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Lemma irset_ret_same : forall r x, ir_ret r = x -> irset_ret r x = r.
Proof. intros r x H. destruct r; cbn in *. subst. reflexivity. Qed.

Lemma szwrap32_mod64_gt18 : forall h, 18 < h < 2 ^ 32 -> 18 < szwrap 32 h mod 2 ^ 64 < 2 ^ 64.
Proof.
  intros h Hh. split; [| apply Z.mod_pos_bound; lia].
  destruct (Z_lt_le_dec h (2 ^ 31)) as [Hs|Hs].
  - rewrite szwrap32_small by lia. rewrite Z.mod_small by lia. lia.
  - unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
    change (2 ^ 31) with 2147483648 in Hs. change (2 ^ 32) with 4294967296 in Hh.
    Z.to_euclidean_division_equations; lia.
Qed.

Section ArmLENLENS.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_LENLENS : forall flush w, is_mode (w_s w) = LENLENS -> arm_ok flush w = true ->
    leave_okb (w_s w) = true /\ lenlens_okb w = true.
  Hypothesis OK_LENLENS_next : forall flush w w2, is_mode (w_s w) = LENLENS -> arm_ok flush w = true ->
    lenlens_next w = Some w2 -> arm_ok flush w2 = true.
End ArmLENLENS.
End RefInflateA_LENLENS.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS.

Module RefInflateA_CODELENS1.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma DECODE_k_O' : forall p index need s c r,
  DECODE_k 0 p index need (mkW s c r) = ARun (code_at s p (index (ir_hold r))) (mkW s c r).
Proof. intros. reflexivity. Qed.
Lemma DECODE_k_S' : forall k p index need s c r,
  DECODE_k (S k) p index need (mkW s c r)
  = let here := code_at s p (index (ir_hold r)) in
    if need here <=? ir_bits r then ARun here (mkW s c r)
    else if ir_have r =? 0 then ALeave (mkW s c r) else DECODE_k k p index need (mkW s c (pullr c r)).
Proof.
  intros.
  change (DECODE_k (S k) p index need (mkW s c r))
    with (abind HOLD (fun hold => abind (gr ir_bits) (fun bits => abind (gs (fun s0 => code_at s0 p (index hold))) (fun here =>
            if need here <=? bits then aret here else abind PULLBYTE (fun _ => DECODE_k k p index need)))) (mkW s c r)).
  unfold abind at 1. rewrite HOLD_eq. unfold abind at 1. cbn [gr w_r]. unfold abind at 1. cbn [gs w_s]. cbv zeta.
  destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r); [reflexivity|].
  unfold abind. rewrite PULLBYTE_eq. destruct (ir_have r =? 0); reflexivity.
Qed.
Lemma DECODE_k_run' : forall k p index need s c r h s1 c1 r1,
  DECODE_k k p index need (mkW s c r) = ARun h (mkW s1 c1 r1) -> s1 = s /\ c1 = c.
Proof.
  induction k as [|k IH]; intros p index need s c r h s1 c1 r1 H.
  - rewrite DECODE_k_O' in H. injection H as _ <- <-. split; reflexivity.
  - rewrite DECODE_k_S' in H. cbv zeta in H.
    destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r); [injection H as _ <- <-; split; reflexivity|].
    destruct (ir_have r =? 0); [discriminate H|]. exact (IH _ _ _ _ _ _ _ _ _ _ H).
Qed.
Lemma DECODE_k_leave : forall k p index need s c r w,
  DECODE_k k p index need (mkW s c r) = ALeave w -> exists r1, w = mkW s c r1.
Proof.
  induction k as [|k IH]; intros p index need s c r w H.
  - rewrite DECODE_k_O' in H. discriminate H.
  - rewrite DECODE_k_S' in H. cbv zeta in H.
    destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r); [discriminate H|].
    destruct (ir_have r =? 0); [injection H as <-; exists r; reflexivity|]. exact (IH _ _ _ _ _ _ _ H).
Qed.
Lemma NEEDBITS_k_leave : forall k n s c r w,
  NEEDBITS_k k n (mkW s c r) = ALeave w -> exists r1, w = mkW s c r1.
Proof.
  induction k as [|k IH]; intros n s c r w H.
  - cbn in H. unfold aret in H. discriminate H.
  - rewrite NEEDBITS_k_S in H. destruct (ir_bits r <? n); [| discriminate H].
    destruct (ir_have r =? 0); [injection H as <-; exists r; reflexivity | exact (IH _ _ _ _ _ H)].
Qed.


Definition cl_lit (s : inflate_state) (val : Z) : inflate_state :=
  iset_have (iset_lens s (arr_set (is_lens s) (is_have s) (wrap16 val))) (wrap32 (is_have s + 1)).

Fixpoint lrep (n : nat) (lens : arr) (have copy len : Z) : arr * Z * Z :=
  match n with
  | O => (lens, have, copy)
  | S n' => if negb (copy =? 0) then lrep n' (arr_set lens have (wrap16 len)) (wrap32 (have + 1)) (wrap32 (copy - 1)) len
            else (lens, have, copy)
  end.
Definition cl_rep (s : inflate_state) (copy len : Z) : inflate_state :=
  let '(lens, have, _) := lrep (Z.to_nat copy) (is_lens s) (is_have s) copy len in
  iset_have (iset_lens s lens) have.

Lemma loopZ_lrep : forall n len lens have cp,
  loopZ (Z.of_nat n)
    (fun st : arr * Z * Z => let '(lens, have, copy) := st in
       if negb (copy =? 0) then (true, (arr_set lens have (wrap16 len), wrap32 (have + 1), wrap32 (copy - 1)))
       else (false, (lens, have, copy)))
    (lens, have, cp) = lrep n lens have cp len.
Proof.
  induction n as [|n IH]; intros len lens have cp.
  - cbn [lrep Z.of_nat]. rewrite loopZ_le0 by lia. reflexivity.
  - rewrite Nat2Z.inj_succ. rewrite loopZ_step by lia. cbn [lrep].
    destruct (negb (cp =? 0)); [| reflexivity].
    replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by lia. apply IH.
Qed.

Lemma lens_repeat_eq : forall copy len s c r, 0 <= copy ->
  lens_repeat copy len (mkW s c r) = ARun tt (mkW (cl_rep s copy len) c r).
Proof.
  intros copy len s c r Hc. unfold lens_repeat. rewrite us_eq. f_equal. f_equal. unfold cl_rep.
  rewrite <- (Z2Nat.id copy) at 1 by exact Hc. rewrite loopZ_lrep. reflexivity.
Qed.

Fixpoint fill (n : nat) (lens : arr) (i v : Z) : arr :=
  match n with O => lens | S n' => fill n' (arr_set lens i v) (i + 1) v end.

Lemma lrep_fill : forall n lens have len,
  0 <= have -> have + Z.of_nat n < 2 ^ 32 ->
  lrep n lens have (Z.of_nat n) len = (fill n lens have (wrap16 len), have + Z.of_nat n, 0).
Proof.
  induction n as [|n IH]; intros lens have len Hh Hn.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [lrep fill]. rewrite Nat2Z.inj_succ in Hn |- *.
    replace (negb (Z.succ (Z.of_nat n) =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
    rewrite (wrap32_id (have + 1)) by lia. replace (wrap32 (Z.succ (Z.of_nat n) - 1)) with (Z.of_nat n) by (rewrite wrap32_id by lia; lia).
    rewrite IH by lia. f_equal. f_equal. lia.
Qed.
Lemma fill_len : forall n lens i v, arr_len (fill n lens i v) = arr_len lens.
Proof. induction n as [|n IH]; intros; cbn [fill]; [reflexivity | rewrite IH, arr_len_set; reflexivity]. Qed.
Lemma fill_get : forall n lens i v j, 0 <= i -> i + Z.of_nat n <= arr_len lens ->
  arr_get (fill n lens i v) j = if (i <=? j) && (j <? i + Z.of_nat n) then v else arr_get lens j.
Proof.
  induction n as [|n IH]; intros lens i v j Hi Hn.
  - cbn [fill Z.of_nat]. rewrite Z.add_0_r. destruct (Z.leb_spec i j); destruct (Z.ltb_spec j i); cbn [andb]; try reflexivity. lia.
  - cbn [fill]. rewrite Nat2Z.inj_succ in Hn |- *. rewrite IH by (rewrite ?arr_len_set; lia).
    rewrite arr_get_set. unfold arr_inb.
    destruct (Z.leb_spec (i + 1) j); destruct (Z.ltb_spec j (i + 1 + Z.of_nat n)); destruct (Z.leb_spec i j); destruct (Z.ltb_spec j (i + Z.succ (Z.of_nat n)));
      destruct (Z.eqb_spec i j); destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (arr_len lens)); cbn [andb]; try reflexivity; try lia.
Qed.

Lemma cl_rep_fill : forall s copy len, 0 <= is_have s -> 0 <= copy -> is_have s + copy < 2 ^ 32 ->
  cl_rep s copy len = iset_have (iset_lens s (fill (Z.to_nat copy) (is_lens s) (is_have s) (wrap16 len))) (is_have s + copy).
Proof.
  intros s copy len Hh Hc Hhc. unfold cl_rep.
  rewrite <- (Z2Nat.id copy) at 2 by exact Hc. rewrite lrep_fill by lia. rewrite Z2Nat.id by exact Hc. reflexivity.
Qed.

Lemma BITSv_nonneg : forall h n, 0 <= BITSv h n.
Proof. intros h n. unfold BITSv, wrap32. apply (proj2 (Z.land_nonneg _ _)). left. apply (proj2 (Z.land_nonneg _ _)). right. lia. Qed.

Definition cl_nb (val : Z) : Z := if val =? 16 then 2 else if val =? 17 then 3 else 7.
Definition cl_base (val : Z) : Z := if val =? 16 then 3 else if val =? 17 then 3 else 11.

Definition cl_bad (s : inflate_state) (c : icall) (r : iregs) : iw :=
  mkW (iset_mode s BAD) (icset_msg c MSG_invalid_bit_length_repeat) r.

Definition cl_after (s : inflate_state) (c : icall) (here : Z) (r2 : iregs) : ares bool :=
  let val := code_val here in
  let nb := cl_nb val in
  let r3 := ddrop r2 (code_bits here) in
  if (val =? 16) && (is_have s =? 0) then ARun false (cl_bad s c r3)
  else
    let len := if val =? 16 then arr_get (is_lens s) (is_have s - 1) else 0 in
    let copy := cl_base val + BITSv (ir_hold r3) nb in
    let r4 := ddrop r3 nb in
    if is_nlen s + is_ndist s <? is_have s + copy then ARun false (cl_bad s c r4)
    else ARun true (mkW (cl_rep s copy len) c r4).

Lemma codelens_body_eq : forall s c r,
  codelens_body (mkW s c r) =
  match DECODE1 (is_lencode s) (is_lenbits s) (mkW s c r) with
  | ARun here (mkW s1 c1 r1) =>
      if code_val here <? 16 then ARun true (mkW (cl_lit s1 (code_val here)) c1 (ddrop r1 (code_bits here)))
      else match NEEDBITS (code_bits here + cl_nb (code_val here)) (mkW s1 c1 r1) with
           | ARun _ (mkW s2 c2 r2) => cl_after s2 c2 here r2
           | ALeave w => ALeave w
           | ARet rc w => ARet rc w
           end
  | ALeave w => ALeave w
  | ARet rc w => ARet rc w
  end.
Proof.
  intros s c r. unfold codelens_body. rewrite abind_run, gs_eq. rewrite abind_run.
  destruct (DECODE1 (is_lencode s) (is_lenbits s) (mkW s c r)) as [here [s1 c1 r1] | w | rc w]; [| reflexivity | reflexivity].
  destruct (code_val here <? 16) eqn:Hv.
  { mstep1 DROPBITS_eq. mstep1 (@gs_eq inflate_state). unfold set_lens. mstep1 us_eq. mstep1 us_eq. rewrite aret_eq. reflexivity. }
  rewrite abind_run.
  unfold cl_after, cl_nb, cl_base.
  destruct (code_val here =? 16) eqn:H16.
  - rewrite abind_run.
    destruct (NEEDBITS (code_bits here + 2) (mkW s1 c1 r1)) as [[] [s2 c2 r2] | w | rc w]; [| reflexivity | reflexivity].
    mstep1 DROPBITS_eq. mstep1 (@gs_eq inflate_state). cbn [andb].
    destruct (is_have s2 =? 0).
    + rewrite abind_run, go_bad_eq, aret_eq. rewrite aret_eq. reflexivity.
    + mstep1 BITS_eq. mstep1 DROPBITS_eq. rewrite aret_eq. mstep1 (@gs_eq inflate_state). cbv zeta.
      cbn [is_nlen is_ndist is_have is_lens iset_mode].
      destruct (is_nlen s2 + is_ndist s2 <? _).
      * rewrite abind_run, go_bad_eq, aret_eq. reflexivity.
      * rewrite abind_run, lens_repeat_eq, aret_eq; [reflexivity|]. apply Z.add_nonneg_nonneg; [lia | apply BITSv_nonneg].
  - cbn [andb].
    destruct (code_val here =? 17) eqn:H17.
    + rewrite abind_run.
      destruct (NEEDBITS (code_bits here + 3) (mkW s1 c1 r1)) as [[] [s2 c2 r2] | w | rc w]; [| reflexivity | reflexivity].
      mstep1 DROPBITS_eq. mstep1 BITS_eq. mstep1 DROPBITS_eq. rewrite aret_eq. mstep1 (@gs_eq inflate_state). cbv zeta.
      cbn [is_nlen is_ndist is_have is_lens].
      destruct (is_nlen s2 + is_ndist s2 <? _).
      * rewrite abind_run, go_bad_eq, aret_eq. reflexivity.
      * rewrite abind_run, lens_repeat_eq, aret_eq; [reflexivity|]. apply Z.add_nonneg_nonneg; [lia | apply BITSv_nonneg].
    + rewrite abind_run.
      destruct (NEEDBITS (code_bits here + 7) (mkW s1 c1 r1)) as [[] [s2 c2 r2] | w | rc w]; [| reflexivity | reflexivity].
      mstep1 DROPBITS_eq. mstep1 BITS_eq. mstep1 DROPBITS_eq. rewrite aret_eq. mstep1 (@gs_eq inflate_state). cbv zeta.
      cbn [is_nlen is_ndist is_have is_lens].
      destruct (is_nlen s2 + is_ndist s2 <? _).
      * rewrite abind_run, go_bad_eq, aret_eq. reflexivity.
      * rewrite abind_run, lens_repeat_eq, aret_eq; [reflexivity|]. apply Z.add_nonneg_nonneg; [lia | apply BITSv_nonneg].
Qed.

Lemma codelens_while_S : forall k s c r,
  codelens_while (S k) (mkW s c r) =
    if is_have s <? is_nlen s + is_ndist s then
      match codelens_body (mkW s c r) with
      | ARun true w1 => codelens_while k w1
      | ARun false w1 => ARun tt w1
      | ALeave w1 => ALeave w1
      | ARet rc w1 => ARet rc w1
      end
    else ARun tt (mkW s c r).
Proof.
  intros k s c r. cbn [codelens_while]. rewrite abind_run, gs_eq.
  destruct (is_have s <? is_nlen s + is_ndist s); [| rewrite aret_eq; reflexivity].
  rewrite abind_run. destruct (codelens_body (mkW s c r)) as [[|] w1 | w1 | rc w1]; try reflexivity.
  all: rewrite ?aret_eq; reflexivity.
Qed.
Lemma codelens_while_O : forall w, codelens_while O w = ARun tt w.
Proof. intros. reflexivity. Qed.
Lemma codelens_while_stop : forall k s c r, is_nlen s + is_ndist s <= is_have s -> codelens_while k (mkW s c r) = ARun tt (mkW s c r).
Proof. intros k s c r H. destruct k; [reflexivity|]. rewrite codelens_while_S. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.


Definition cl_tab1 (s : inflate_state) (tbl : arr) (next lenbits : Z) (work : arr) : inflate_state :=
  iset_work (iset_lenbits (iset_next (iset_lencode (iset_codes s tbl) (CDyn 0)) next) lenbits) work.
Definition cl_tab2 (s : inflate_state) (tbl : arr) (next distbits : Z) (work : arr) : inflate_state :=
  iset_work (iset_distbits (iset_next (iset_distcode (iset_codes s tbl) (CDyn (is_next s))) next) distbits) work.

Definition cl_post (flush : Z) (s : inflate_state) (c : icall) (r : iregs) : ares unit :=
  if arr_get (is_lens s) 256 =? 0 then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_code_missing_end_of_block) r)
  else
    let '(ret, tbl, next, lenbits, work) := inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) in
    let s1 := cl_tab1 s tbl next lenbits work in
    let r1 := irset_ret r ret in
    if negb (ret =? 0) then ARun tt (mkW (iset_mode s1 BAD) (icset_msg c MSG_invalid_literal_lengths_set) r1)
    else
      let '(ret2, tbl2, next2, distbits, work2) := inflate_table DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) (is_codes s1) (is_next s1) 6 (is_work s1) in
      let s2 := cl_tab2 s1 tbl2 next2 distbits work2 in
      let r2 := irset_ret r1 ret2 in
      if negb (ret2 =? 0) then ARun tt (mkW (iset_mode s2 BAD) (icset_msg c MSG_invalid_distances_set) r2)
      else if flush =? Z_TREES then ALeave (mkW (iset_mode s2 LEN_) c r2)
      else arm_LEN_ ivar_ref (mkW (iset_mode s2 LEN_) c r2).

Lemma arm_CODELENS_eq : forall flush s c r,
  arm_CODELENS ivar_ref flush (mkW s c r) =
  match codelens_while 321 (mkW s c r) with
  | ARun _ (mkW s1 c1 r1) => if is_mode s1 =? BAD then ARun tt (mkW s1 c1 r1) else cl_post flush s1 c1 r1
  | ALeave w => ALeave w
  | ARet rc w => ARet rc w
  end.
Proof.
  intros flush s c r. unfold arm_CODELENS. rewrite abind_run.
  destruct (codelens_while 321 (mkW s c r)) as [[] [s1 c1 r1] | w | rc w]; [| reflexivity | reflexivity].
  rewrite abind_run, gs_eq. destruct (is_mode s1 =? BAD); [rewrite aret_eq; reflexivity|].
  unfold cl_post. destruct (arr_get (is_lens s1) 256 =? 0); [rewrite go_bad_eq; reflexivity|].
  destruct (inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as [[[[ret tbl] nxt] lb] wk].
  mstep1 us_eq. mstep1 ur_eq. fold (cl_tab1 s1 tbl nxt lb wk).
  destruct (negb (ret =? 0)); [rewrite go_bad_eq; reflexivity|].
  rewrite abind_run, gs_eq.
  destruct (inflate_table DISTS _ _ _ _ _ 6 _) as [[[[ret2 tbl2] nxt2] db] wk2].
  mstep1 us_eq. mstep1 ur_eq. fold (cl_tab2 (cl_tab1 s1 tbl nxt lb wk) tbl2 nxt2 db wk2).
  destruct (negb (ret2 =? 0)); [rewrite go_bad_eq; reflexivity|].
  mstep1 set_mode_eq. cbn [iv_flush_exits ivar_ref andb].
  destruct (flush =? Z_TREES); [rewrite aleave_eq|]; reflexivity.
Qed.


Definition cl_two (op : Z) : bool := false.

Fixpoint clw_chk (k : nat) (s : inflate_state) (c : icall) (r : iregs) : bool :=
  match k with
  | O => true
  | S k' =>
      if is_have s <? is_nlen s + is_ndist s then
        decode_okb cl_two s c r (is_lencode s) (is_lenbits s) &&
        match codelens_body (mkW s c r) with
        | ARun true (mkW s1 c1 r1) => clw_chk k' s1 c1 r1
        | _ => true
        end
      else true
  end.

Definition lens15b (lens : arr) (lo hi : Z) : bool :=
  forallb (fun i => let j := Z.of_nat i in (j <? lo) || (hi <=? j) || (arr_get lens j <=? 15)) (seq 0 320).

Definition cl_post_ok (s : inflate_state) : bool :=
  if arr_get (is_lens s) 256 =? 0 then true
  else
    lens15b (is_lens s) 0 (is_nlen s)
    && it_safe LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s)
    && (let '(ret, tbl, next, lenbits, work) := inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) in
        ll_post_ok tbl next lenbits work
        && (if ret =? 0 then
              let s1 := cl_tab1 s tbl next lenbits work in
              lens15b (is_lens s1) (is_nlen s1) (is_nlen s1 + is_ndist s1)
              && it_safe DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) (is_codes s1) (is_next s1) 6 (is_work s1)
              && (let '(ret2, tbl2, next2, distbits, work2) := inflate_table DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) (is_codes s1) (is_next s1) 6 (is_work s1) in
                  ll_post_ok tbl2 next2 distbits work2)
            else true)).

Definition codelens_okb (w : iw) : bool :=
  let s := w_s w in
  (is_nlen s + is_ndist s <=? 320)
  && clw_chk 321 s (w_c w) (w_r w)
  && match codelens_while 321 w with
     | ARun _ (mkW s1 c1 r1) => if is_mode s1 =? BAD then true else cl_post_ok s1
     | _ => true
     end.

Definition codelens_next (flush : Z) (w : iw) : option iw :=
  match codelens_while 321 w with
  | ARun _ (mkW s1 c1 r1) =>
      if is_mode s1 =? BAD then None
      else if arr_get (is_lens s1) 256 =? 0 then None
      else
        let '(ret, tbl, next, lenbits, work) := inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1) in
        if negb (ret =? 0) then None
        else
          let s2 := cl_tab1 s1 tbl next lenbits work in
          let '(ret2, tbl2, next2, distbits, work2) := inflate_table DISTS (is_lens s2) (is_nlen s2) (is_ndist s2) (is_codes s2) (is_next s2) 6 (is_work s2) in
          if negb (ret2 =? 0) then None
          else if flush =? Z_TREES then None
          else Some (mkW (iset_mode (cl_tab2 s2 tbl2 next2 distbits work2) LEN_) c1 (irset_ret (irset_ret r1 ret) ret2))
  | _ => None
  end.

Lemma lens15b_sound : forall lens lo hi, lens15b lens lo hi = true -> 0 <= lo -> hi <= 320 ->
  forall i, 0 <= i < hi - lo -> arr_get lens (lo + i) <= 15.
Proof.
  intros lens lo hi H Hlo Hhi i Hi. unfold lens15b in H.
  pose proof (forallb_seq_Z (fun j => (j <? lo) || (hi <=? j) || (arr_get lens j <=? 15)) 320%nat (lo + i) H ltac:(cbn; lia)) as Y.
  cbv beta in Y. destruct (Z.ltb_spec (lo + i) lo); [lia|]. destruct (Z.leb_spec hi (lo + i)); [lia|]. cbn [orb] in Y. apply Z.leb_le in Y. exact Y.
Qed.
End RefInflateA_CODELENS1.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.

Module RefInflateA_CODELENS2.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Local Ltac lreg_in := cbn; repeat (first [ left; reflexivity | right ]).
Definition ctab (s : inflate_state) : Z -> Z := code_at s (is_lencode s).
Definition cN (s : inflate_state) : Z := ctab_len (is_lencode s).

Section ArmCL2.
End ArmCL2.
End RefInflateA_CODELENS2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS2.

Module RefInflateA_CODELENS3.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Lemma cl_lit_facts : forall s val,
  is_mode (cl_lit s val) = is_mode s /\ is_window (cl_lit s val) = is_window s /\ is_window_blk (cl_lit s val) = is_window_blk s
  /\ is_wsize (cl_lit s val) = is_wsize s /\ is_self_blk (cl_lit s val) = is_self_blk s /\ is_wbits (cl_lit s val) = is_wbits s
  /\ is_have (cl_lit s val) = wrap32 (is_have s + 1) /\ is_nlen (cl_lit s val) = is_nlen s /\ is_ndist (cl_lit s val) = is_ndist s
  /\ is_lencode (cl_lit s val) = is_lencode s /\ is_lenbits (cl_lit s val) = is_lenbits s /\ is_codes (cl_lit s val) = is_codes s.
Proof. intros. repeat split; reflexivity. Qed.

Lemma cl_lit_iwf : forall s val, 0 <= is_have s < 320 -> iwf s -> iwf (cl_lit s val).
Proof.
  intros s val Hh Hwf. unfold cl_lit.
  pose proof (iwf_x s Hwf) as X. unfold iwfx in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xll & _ & _ & Xlb & _).
  apply iwf_set_have; [rewrite wrap32_id by lia; lia|].
  apply iwf_set_lens; [rewrite arr_len_set; exact Xll | | exact Hwf].
  intros i Hi. rewrite arr_get_set. destruct ((is_have s =? i) && _); [| apply Xlb; exact Hi].
  unfold wrap16. split; [apply Z.land_nonneg; right; lia|]. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Section ArmCL3.
End ArmCL3.
End RefInflateA_CODELENS3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS3.

Module RefInflateA_CODELENS4.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Definition nb_entry (site : nat) : Z := nth site [0x1afb8; 0x1acd8; 0x1a600] 0.
Definition nb_head (site : nat) : Z := nth site [0x1afc0; 0x1ace0; 0x1a608] 0.
Definition nb_exit (site : nat) : Z := nth site [0x1afe0; 0x1ad00; 0x1a628] 0.
Definition nb_k (site : nat) : Z := nth site [2; 3; 7] 0.

Section ArmCL4.
End ArmCL4.
End RefInflateA_CODELENS4.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS4.

Module RefInflateA_CODELENS5.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Section ArmCL5.

  Lemma ddrop_ddrop_facts : forall r a b,
    ir_hold (ddrop (ddrop r a) b) = Z.shiftr (Z.shiftr (ir_hold r) a) b /\ ir_bits (ddrop (ddrop r a) b) = wrap32 (wrap32 (ir_bits r - a) - b)
    /\ ir_put (ddrop (ddrop r a) b) = ir_put r /\ ir_left (ddrop (ddrop r a) b) = ir_left r /\ ir_in (ddrop (ddrop r a) b) = ir_in r
    /\ ir_out (ddrop (ddrop r a) b) = ir_out r /\ ir_ret (ddrop (ddrop r a) b) = ir_ret r /\ ir_next (ddrop (ddrop r a) b) = ir_next r /\ ir_have (ddrop (ddrop r a) b) = ir_have r.
  Proof. intros. unfold ddrop. destruct r; cbn; repeat split; reflexivity. Qed.
End ArmCL5.
End RefInflateA_CODELENS5.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS5.

Module RefInflateA_CODELENS6.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Definition pat4 (len : Z) : Z := Z.lor (Z.lor (Z.lor len (len * 2 ^ 16)) (len * 2 ^ 32)) (len * 2 ^ 48).


Lemma fill_S_snoc : forall j lens i v, fill (S j) lens i v = arr_set (fill j lens i v) (i + Z.of_nat j) v.
Proof.
  induction j as [|j IH]; intros lens i v.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - change (fill (S (S j)) lens i v) with (fill (S j) (arr_set lens i v) (i + 1) v). rewrite IH.
    change (fill (S j) lens i v) with (fill j (arr_set lens i v) (i + 1) v). f_equal. rewrite Nat2Z.inj_succ. lia.
Qed.

Definition fst_j (s : inflate_state) (len : Z) (j : nat) : inflate_state :=
  iset_lens s (fill j (is_lens s) (is_have s) len).

Lemma fst_j_O : forall s len, fst_j s len O = iset_lens s (is_lens s).
Proof. reflexivity. Qed.
Lemma iset_lens_same : forall s, iset_lens s (is_lens s) = s.
Proof. intros s. destruct s; reflexivity. Qed.
Lemma fst_j_facts : forall s len j,
  is_have (fst_j s len j) = is_have s /\ is_mode (fst_j s len j) = is_mode s /\ is_window (fst_j s len j) = is_window s
  /\ is_window_blk (fst_j s len j) = is_window_blk s /\ is_wsize (fst_j s len j) = is_wsize s /\ is_lens (fst_j s len j) = fill j (is_lens s) (is_have s) len
  /\ is_nlen (fst_j s len j) = is_nlen s /\ is_ndist (fst_j s len j) = is_ndist s /\ is_self_blk (fst_j s len j) = is_self_blk s /\ is_wbits (fst_j s len j) = is_wbits s.
Proof. intros. repeat split; reflexivity. Qed.
Lemma fst_j_S : forall s len j, fst_j s len (S j) = iset_lens (fst_j s len j) (arr_set (is_lens (fst_j s len j)) (is_have s + Z.of_nat j) len).
Proof. intros s len j. unfold fst_j. rewrite fill_S_snoc. destruct s; reflexivity. Qed.

Lemma fst_j_iwf : forall s len j, 0 <= len < 2 ^ 16 -> iwf s -> iwf (fst_j s len j).
Proof.
  intros s len j Hl Hwf. induction j as [|j IH].
  - unfold fst_j. cbn [fill]. rewrite iset_lens_same. exact Hwf.
  - rewrite fst_j_S. pose proof (iwf_x _ IH) as X. unfold iwfx in X.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xll & _ & _ & Xlb & _).
    apply iwf_set_lens; [rewrite arr_len_set; exact Xll | | exact IH].
    intros i Hi. rewrite arr_get_set. destruct (_ && _); [exact Hl | apply Xlb; exact Hi].
Qed.

Lemma cl_rep_fst : forall s copy len, 0 <= is_have s -> 0 <= copy -> is_have s + copy < 2 ^ 32 -> 0 <= len < 2 ^ 16 ->
  cl_rep s copy len = iset_have (fst_j s len (Z.to_nat copy)) (is_have s + copy).
Proof.
  intros s copy len Hh Hc Hhc Hl. rewrite cl_rep_fill by assumption. unfold fst_j. rewrite (wrap16_id len) by exact Hl. reflexivity.
Qed.

Section ArmCL6.

  Lemma zx2_lit : forall h, 0 <= h < 2 ^ 30 ->
    (h * 2 ^ 32 + 8589934592) / 2 ^ 31 = (h + 2) * 2 /\ (h * 2 ^ 32 + 12884901888) / 2 ^ 31 = (h + 3) * 2
    /\ (h * 2 ^ 32 + 17179869184) / 2 ^ 31 = (h + 4) * 2 /\ (h * 2 ^ 32 + 21474836480) / 2 ^ 31 = (h + 5) * 2.
  Proof. intros h Hh. change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648. change (2 ^ 30) with 1073741824 in Hh. Z.to_euclidean_division_equations; lia. Qed.

  Lemma land_2_eq : forall n, Z.land n 2 = n mod 4 - n mod 2.
  Proof.
    intros n.
    assert (H3 : Z.land n 3 = n mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
    assert (H1 : Z.land n 1 = n mod 2) by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
    assert (D : Z.land (Z.land n 2) (Z.land n 1) = 0).
    { apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec k 0) as [->|K0]; [cbn; rewrite Bool.andb_false_r; reflexivity|].
      destruct (Z.eq_dec k 1) as [->|K1]; [cbn; rewrite !Bool.andb_false_r; reflexivity|].
      replace (Z.testbit 2 k) with false; [rewrite Bool.andb_false_r; reflexivity|].
      symmetry. change 2 with (2 ^ 1). apply Z.pow2_bits_false. lia. }
    assert (E : Z.land n 3 = Z.land n 2 + Z.land n 1).
    { change 3 with (Z.lor 2 1). rewrite Z.land_lor_distr_r. rewrite (lor_lxor_disj _ _ D). symmetry. apply Z.add_nocarry_lxor. exact D. }
    lia.
  Qed.
End ArmCL6.
End RefInflateA_CODELENS6.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS6.

Module RefInflateA_CODELENS7.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Lemma land_m4 : forall x, Z.land x (-4) = x - x mod 4.
Proof.
  intros x.
  assert (H3 : Z.land x 3 = x mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
  assert (D : Z.land (Z.land x (-4)) (Z.land x 3) = 0).
  { rewrite (Z.land_comm x 3), Z.land_assoc, <- (Z.land_assoc x (-4) 3). change (Z.land (-4) 3) with 0. rewrite Z.land_0_r. reflexivity. }
  assert (E : Z.land x (Z.lor (-4) 3) = Z.land x (-4) + Z.land x 3).
  { rewrite Z.land_lor_distr_r. rewrite (lor_lxor_disj _ _ D). symmetry. apply Z.add_nocarry_lxor. exact D. }
  change (Z.lor (-4) 3) with (-1) in E. rewrite Z.land_m1_r in E. lia.
Qed.

Section ArmCL7.
End ArmCL7.
End RefInflateA_CODELENS7.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS7.

Module RefInflateA_CODELENS8.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Section ArmCL8.
End ArmCL8.
End RefInflateA_CODELENS8.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS8.

Module RefInflateA_CODELENS9.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS8.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Lemma cl_rep_facts : forall s copy len, 0 <= is_have s -> 0 <= copy -> is_have s + copy < 2 ^ 32 -> 0 <= len < 2 ^ 16 ->
  is_have (cl_rep s copy len) = is_have s + copy /\ is_mode (cl_rep s copy len) = is_mode s /\ is_lencode (cl_rep s copy len) = is_lencode s
  /\ is_lenbits (cl_rep s copy len) = is_lenbits s /\ is_nlen (cl_rep s copy len) = is_nlen s /\ is_ndist (cl_rep s copy len) = is_ndist s
  /\ same_blocks s (cl_rep s copy len) /\ leave_okb (cl_rep s copy len) = leave_okb s
  /\ is_window (cl_rep s copy len) = is_window s /\ is_window_blk (cl_rep s copy len) = is_window_blk s /\ is_wsize (cl_rep s copy len) = is_wsize s.
Proof.
  intros s copy len Hh Hc Hhc Hl. rewrite (cl_rep_fst s copy len Hh Hc Hhc Hl). unfold fst_j.
  repeat split; reflexivity.
Qed.

Ltac lazy_enum :=
  let r' := fresh "r'" in let Hr := fresh "Hr" in let Hn := fresh "Hn" in
  intros r' Hr Hn; cbn in Hr;
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
  first [ exfalso; apply Hn; cbn; tauto | split; [cbn; intuition discriminate | vm_compute; reflexivity] ].

Section ArmCL9.

  Lemma same_blocks_cl_lit : forall s val, same_blocks s (cl_lit s val). Proof. intros. unfold same_blocks; repeat split; reflexivity. Qed.
  Lemma leave_okb_cl_lit : forall s val, leave_okb (cl_lit s val) = leave_okb s. Proof. intros. reflexivity. Qed.

  Lemma nb_k_range : forall site, (site <= 2)%nat -> 2 <= nb_k site <= 7.
  Proof. intros site H. unfold nb_k. destruct site as [|[|[|]]]; cbn; lia. Qed.
End ArmCL9.
End RefInflateA_CODELENS9.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS9.

Module RefInflateA_CODELENS10.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Definition ir_nlen_ok (nlen anl : Z) : Prop := anl = nlen.

Definition cl_pre1 (s : inflate_state) : inflate_state := iset_lencode (iset_next (iset_lenbits s 9) 0) (CDyn 0).

Section ArmCL10.
  Definition cl_pre2 (s : inflate_state) : inflate_state := iset_distbits (iset_distcode s (CDyn (is_next s))) 6.

  Lemma iwf_cl_tab2 : forall st tbl nxt db wk,
    arr_len tbl = 1444 -> arr_len wk = 288 -> 0 <= nxt <= 1444 -> 0 <= db < 2 ^ 32 ->
    (forall i, 0 <= i < 1444 -> 0 <= arr_get tbl i < 2 ^ 32) ->
    (forall i, 0 <= i < 288 -> 0 <= arr_get wk i < 2 ^ 16) ->
    iwf st -> iwf (cl_tab2 st tbl nxt db wk).
  Proof.
    intros st tbl nxt db wk H1 H2 H3 H4 H5 H6 H. unfold cl_tab2, iwf, iwfx in *.
    destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len] in *.
    decompose [and] H. repeat apply conj; first [assumption | lia].
  Qed.
  Lemma cl_tab2_facts : forall s tbl nxt db wk,
    is_mode (cl_tab2 s tbl nxt db wk) = is_mode s /\ is_window (cl_tab2 s tbl nxt db wk) = is_window s
    /\ is_window_blk (cl_tab2 s tbl nxt db wk) = is_window_blk s /\ is_wsize (cl_tab2 s tbl nxt db wk) = is_wsize s
    /\ is_self_blk (cl_tab2 s tbl nxt db wk) = is_self_blk s /\ is_wbits (cl_tab2 s tbl nxt db wk) = is_wbits s
    /\ is_lens (cl_tab2 s tbl nxt db wk) = is_lens s /\ is_work (cl_tab2 s tbl nxt db wk) = wk /\ is_codes (cl_tab2 s tbl nxt db wk) = tbl
    /\ is_nlen (cl_tab2 s tbl nxt db wk) = is_nlen s /\ is_ndist (cl_tab2 s tbl nxt db wk) = is_ndist s /\ is_have (cl_tab2 s tbl nxt db wk) = is_have s.
  Proof. intros. repeat split; reflexivity. Qed.
End ArmCL10.
End RefInflateA_CODELENS10.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS10.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.

Module RefInflateA_TABLE.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).


Lemma bits_5_5 : forall h, 0 <= h -> (h / 2 ^ 5) mod 2 ^ 5 = h mod 2 ^ 10 / 2 ^ 5.
Proof. intros h Hh. change (2 ^ 5) with 32. change (2 ^ 10) with 1024. Z.to_euclidean_division_equations; lia. Qed.
Lemma bits_10_4 : forall h, 0 <= h -> (h / 2 ^ 10) mod 2 ^ 4 = h mod 2 ^ 14 / 2 ^ 10.
Proof. intros h Hh. change (2 ^ 4) with 16. change (2 ^ 10) with 1024. change (2 ^ 14) with 16384. Z.to_euclidean_division_equations; lia. Qed.

Definition tb_res (flush : Z) (s : inflate_state) (c : icall) (r1 : iregs) : ares unit :=
  let s' := tb_s s (ir_hold r1) in
  if (286 <? is_nlen s') || (30 <? is_ndist s') then ARun tt (mkW (iset_mode s' BAD) (icset_msg c MSG_too_many_length_or_distance_symbols) (tb_r r1))
  else arm_LENLENS ivar_ref flush (mkW (tb_s2 s (ir_hold r1)) c (tb_r r1)).

Lemma BITSv_mod' : forall h n, 0 <= h -> 0 <= n <= 32 -> BITSv h n = h mod 2 ^ n.
Proof. intros h n Hh Hn. rewrite BITSv_land by lia. apply Z.land_ones. lia. Qed.


Lemma arm_TABLE_eq : forall flush s c r s1 c1 r1,
  NEEDBITS 14 (mkW s c r) = ARun tt (mkW s1 c1 r1) -> 0 <= ir_hold r1 -> 14 <= ir_bits r1 < 64 ->
  arm_TABLE ivar_ref flush (mkW s c r) = tb_res flush s1 c1 r1.
Proof.
  intros flush s c r s1 c1 r1 HN Hh Hb. unfold arm_TABLE. rewrite abind_run, HN.
  mstep1 BITS_eq. mstep1 us_eq. mstep1 DROPBITS_eq. mstep1 BITS_eq. mstep1 us_eq. mstep1 DROPBITS_eq. mstep1 BITS_eq. mstep1 us_eq. mstep1 DROPBITS_eq.
  mstep1 (@gs_eq inflate_state). irnorm.
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite !BITSv_mod' by (try lia; repeat (apply Z.div_pos; [|lia]); lia).
  rewrite Z.div_div by lia.
  change (2 ^ 5 * 2 ^ 5) with (2 ^ 10).
  rewrite (wrap32_id (ir_bits r1 - 5)) by lia. rewrite (wrap32_id (ir_bits r1 - 5 - 5)) by lia. rewrite (wrap32_id (ir_bits r1 - 5 - 5 - 4)) by lia.
  replace (ir_bits r1 - 5 - 5 - 4) with (ir_bits r1 - 14) by lia.
  unfold tb_res, tb_s, tb_r. cbn [is_nlen is_ndist iset_ncode iset_ndist iset_nlen].
  rewrite Z.shiftr_div_pow2 by lia. rewrite bits_5_5, bits_10_4 by lia.
  replace (ir_hold r1 / 2 ^ 10 / 2 ^ 4) with (ir_hold r1 / 2 ^ 14) by (rewrite Z.div_div by lia; reflexivity).
  destruct ((286 <? ir_hold r1 mod 2 ^ 5 + 257) || (30 <? ir_hold r1 mod 2 ^ 10 / 2 ^ 5 + 1)).
  - rewrite go_bad_eq. reflexivity.
  - mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_TABLE_leave : forall flush w w', NEEDBITS 14 w = ALeave w' -> arm_TABLE ivar_ref flush w = ALeave w'.
Proof. intros flush w w' HN. unfold arm_TABLE. unfold abind at 1. rewrite HN. reflexivity. Qed.

Lemma tb_s_facts : forall s h,
  is_mode (tb_s s h) = is_mode s /\ is_window (tb_s s h) = is_window s /\ is_window_blk (tb_s s h) = is_window_blk s
  /\ is_wsize (tb_s s h) = is_wsize s /\ is_lens (tb_s s h) = is_lens s /\ is_work (tb_s s h) = is_work s
  /\ is_codes (tb_s s h) = is_codes s /\ is_self_blk (tb_s s h) = is_self_blk s /\ is_wbits (tb_s s h) = is_wbits s
  /\ is_nlen (tb_s s h) = h mod 2 ^ 5 + 257 /\ is_ndist (tb_s s h) = h mod 2 ^ 10 / 2 ^ 5 + 1 /\ is_ncode (tb_s s h) = h mod 2 ^ 14 / 2 ^ 10 + 4.
Proof. intros. repeat split; reflexivity. Qed.

Lemma iwf_set_nlen : forall st v, 0 <= v < 2 ^ 32 -> iwf st -> iwf (iset_nlen st v).
Proof. intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len] in *. decompose [and] H. repeat apply conj; first [assumption | lia]. Qed.
Lemma iwf_set_ndist : forall st v, 0 <= v < 2 ^ 32 -> iwf st -> iwf (iset_ndist st v).
Proof. intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len] in *. decompose [and] H. repeat apply conj; first [assumption | lia]. Qed.
Lemma iwf_set_ncode : forall st v, 0 <= v < 2 ^ 32 -> iwf st -> iwf (iset_ncode st v).
Proof. intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len] in *. decompose [and] H. repeat apply conj; first [assumption | lia]. Qed.
Lemma iwf_set_have : forall st v, 0 <= v < 2 ^ 32 -> iwf st -> iwf (iset_have st v).
Proof. intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len] in *. decompose [and] H. repeat apply conj; first [assumption | lia]. Qed.

Lemma tb_s_iwf : forall s h, iwf s -> iwf (tb_s s h).
Proof.
  intros s h H. unfold tb_s.
  pose proof (Z.mod_pos_bound h (2 ^ 5) ltac:(lia)). pose proof (Z.mod_pos_bound h (2 ^ 10) ltac:(lia)). pose proof (Z.mod_pos_bound h (2 ^ 14) ltac:(lia)).
  change (2 ^ 5) with 32 in *. change (2 ^ 10) with 1024 in *. change (2 ^ 14) with 16384 in *.
  assert (0 <= h mod 1024 / 32 < 32) by (Z.to_euclidean_division_equations; lia).
  assert (0 <= h mod 16384 / 1024 < 16) by (Z.to_euclidean_division_equations; lia).
  apply iwf_set_ncode; [lia|]. apply iwf_set_ndist; [lia|]. apply iwf_set_nlen; [lia | exact H].
Qed.

Lemma tb_r_facts : forall r,
  ir_next (tb_r r) = ir_next r /\ ir_have (tb_r r) = ir_have r /\ ir_put (tb_r r) = ir_put r /\ ir_left (tb_r r) = ir_left r
  /\ ir_hold (tb_r r) = Z.shiftr (ir_hold r) 14 /\ ir_bits (tb_r r) = ir_bits r - 14
  /\ ir_in (tb_r r) = ir_in r /\ ir_out (tb_r r) = ir_out r /\ ir_ret (tb_r r) = ir_ret r.
Proof. intros. repeat split; reflexivity. Qed.

Section ArmTABLE.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_TABLE : forall flush w, is_mode (w_s w) = TABLE -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_TABLE_next : forall flush w w2, is_mode (w_s w) = TABLE -> arm_ok flush w = true ->
    table_next w = Some w2 -> arm_ok flush w2 = true.
End ArmTABLE.
End RefInflateA_TABLE.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Lemma same_blocks_tab1 : forall s tbl nxt lb wk m, same_blocks s (iset_mode (cl_tab1 s tbl nxt lb wk) m).
Proof. intros. unfold same_blocks; repeat split; reflexivity. Qed.
Lemma same_blocks_tab2 : forall s tbl nxt lb wk tbl2 nxt2 db wk2 m,
  same_blocks s (iset_mode (cl_tab2 (cl_tab1 s tbl nxt lb wk) tbl2 nxt2 db wk2) m).
Proof. intros. unfold same_blocks; repeat split; reflexivity. Qed.
Lemma leave_okb_tab2 : forall s tbl nxt lb wk tbl2 nxt2 db wk2 m,
  leave_okb (iset_mode (cl_tab2 (cl_tab1 s tbl nxt lb wk) tbl2 nxt2 db wk2) m) = leave_okb s.
Proof. intros. reflexivity. Qed.

Definition cl_post_next (flush : Z) (s1 : inflate_state) (c1 : icall) (r1 : iregs) : option iw :=
  if arr_get (is_lens s1) 256 =? 0 then None
  else
    let '(ret, tbl, next, lenbits, work) := inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1) in
    if negb (ret =? 0) then None
    else
      let s2 := cl_tab1 s1 tbl next lenbits work in
      let '(ret2, tbl2, next2, distbits, work2) := inflate_table DISTS (is_lens s2) (is_nlen s2) (is_ndist s2) (is_codes s2) (is_next s2) 6 (is_work s2) in
      if negb (ret2 =? 0) then None
      else if flush =? Z_TREES then None
      else Some (mkW (iset_mode (cl_tab2 s2 tbl2 next2 distbits work2) LEN_) c1 (irset_ret (irset_ret r1 ret) ret2)).
Lemma codelens_next_eq : forall flush w,
  codelens_next flush w =
  match codelens_while 321 w with
  | ARun _ (mkW s1 c1 r1) => if is_mode s1 =? BAD then None else cl_post_next flush s1 c1 r1
  | _ => None
  end.
Proof. intros. reflexivity. Qed.

Lemma szwrap32_lt_small : forall h n, 0 <= h < 2 ^ 32 -> 0 <= n < 2 ^ 31 ->
  szwrap 32 h mod 2 ^ 64 < szwrap 32 n mod 2 ^ 64 -> h < n /\ szwrap 32 h = h.
Proof.
  intros h n Hh Hn Hlt. rewrite (szwrap32_small n) in Hlt by (clear - Hn; lia). rewrite (Z.mod_small n) in Hlt by (clear - Hn; lia).
  destruct (Z_lt_le_dec h (2 ^ 31)) as [Hs|Hb].
  - rewrite (szwrap32_small h) in Hlt |- * by (clear - Hh Hs; lia). rewrite (Z.mod_small h) in Hlt by (clear - Hh Hs; lia). clear - Hlt; lia.
  - exfalso. unfold szwrap in Hlt. change (2 ^ (32 - 1)) with 2147483648 in Hlt. change (2 ^ 31) with 2147483648 in Hb.
    clear - Hh Hn Hb Hlt. Z.to_euclidean_division_equations; lia.
Qed.
Lemma szwrap32_ge_small : forall h n, 0 <= h < 2 ^ 32 -> 0 <= n < 2 ^ 31 ->
  szwrap 32 n mod 2 ^ 64 <= szwrap 32 h mod 2 ^ 64 -> n <= h.
Proof.
  intros h n Hh Hn Hge. rewrite (szwrap32_small n) in Hge by (clear - Hn; lia). rewrite (Z.mod_small n) in Hge by (clear - Hn; lia).
  destruct (Z_lt_le_dec h (2 ^ 31)) as [Hs|Hb].
  - rewrite (szwrap32_small h) in Hge by (clear - Hh Hs; lia). rewrite (Z.mod_small h) in Hge by (clear - Hh Hs; lia). clear - Hge; lia.
  - change (2 ^ 31) with 2147483648 in Hb. clear - Hn Hb. lia.
Qed.

Lemma clw_chk_S : forall k s c r,
  clw_chk (S k) s c r =
  (if is_have s <? is_nlen s + is_ndist s then
     decode_okb cl_two s c r (is_lencode s) (is_lenbits s) &&
     match codelens_body (mkW s c r) with
     | ARun true (mkW s1 c1 r1) => clw_chk k s1 c1 r1
     | _ => true
     end
   else true).
Proof. intros. reflexivity. Qed.

Section ArmCL11.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_CODELENS : forall flush w, is_mode (w_s w) = CODELENS -> arm_ok flush w = true ->
    leave_okb (w_s w) = true /\ codelens_okb w = true.
  Hypothesis OK_CODELENS_next : forall flush w w2, is_mode (w_s w) = CODELENS -> arm_ok flush w = true ->
    codelens_next flush w = Some w2 -> arm_ok flush w2 = true.
End ArmCL11.
