(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.

Module RefInflateArmLib3.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section Tables.
  Variable s : inflate_state.
Variable c : icall.
Variable r : iregs.
  Hypothesis Hwf : iwf s.

  Lemma ctab_b : forall p i,
    match p with CDyn ofs => 0 <= ofs <= 1444 | _ => True end ->
    0 <= i < ctab_len p -> 0 <= code_at s p i < 2 ^ 32.
  Proof.
    intros p i Hp Hi. pose proof (iwf_x s Hwf) as X.
    assert (Xcodes : forall j, 0 <= j < 1444 -> 0 <= arr_get (is_codes s) j < 2 ^ 32) by (unfold iwfx in X; decompose [and] X; assumption).
    destruct p as [ofs| |]; cbn [ctab_len code_at] in *.
    - apply Xcodes. lia.
    - apply (tab_u32_sound _ 512 i u32_lenfix). cbn. lia.
    - apply (tab_u32_sound _ 32 i u32_distfix). cbn. lia.
  Qed.

  Lemma lencode_ok : match is_lencode s with CDyn ofs => 0 <= ofs <= 1444 | _ => True end.
  Proof. pose proof (iwf_x s Hwf) as X. unfold iwfx in X. decompose [and] X. assumption. Qed.
  Lemma distcode_ok : match is_distcode s with CDyn ofs => 0 <= ofs <= 1444 | _ => True end.
  Proof. pose proof (iwf_x s Hwf) as X. unfold iwfx in X. decompose [and] X. assumption. Qed.
End Tables.


Lemma idx4_eq : forall x, 0 <= x < 2 ^ 30 -> (x * 2 ^ 32) mod 2 ^ 64 / 2 ^ 30 = 4 * x.
Proof.
  intros x Hx. change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616. change (2 ^ 30) with 1073741824 in *.
  Z.to_euclidean_division_equations; lia.
Qed.
End RefInflateArmLib3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.

Module RefInflateA_DISTEXT.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateOkb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Lemma arm_DISTEXT_off : forall s c r, is_extra s = 0 ->
  arm_DISTEXT ivar_ref (mkW s c r) = arm_MATCH ivar_ref (mkW (iset_mode s MATCH) c r).
Proof.
  intros s c r H. unfold arm_DISTEXT. mstep1 (@gs_eq inflate_state). rewrite H. cbn [Z.eqb negb].
  mstep1 (@aret_eq unit). mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_DISTEXT_on : forall s c r, is_extra s <> 0 ->
  arm_DISTEXT ivar_ref (mkW s c r) =
    match NEEDBITS (is_extra s) (mkW s c r) with
    | ARun _ (mkW s1 c1 r1) => arm_MATCH ivar_ref (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c1 (dx_r r1 (is_extra s)))
    | ALeave w1 => ALeave w1
    | ARet rc w1 => ARet rc w1
    end.
Proof.
  intros s c r H. unfold arm_DISTEXT. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) H). cbn [negb].
  rewrite abind_run. rewrite abind_run.
  destruct (NEEDBITS (is_extra s) (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1] eqn:HN; try reflexivity.
  destruct (NEEDBITS_k_run 8 _ s c r s1 c1 r1 HN) as [-> ->].
  mstep1 BITS_eq. mstep1 us_eq. mstep1 DROPBITS_eq. unfold add_back, aux. cbn [iv_aux ivar_ref]. rewrite us_eq. cbv beta iota.
  mstep1 set_mode_eq. reflexivity.
Qed.

Lemma dx_s_facts : forall s h,
  is_mode (dx_s s h) = is_mode s /\ is_flags (dx_s s h) = is_flags s /\ is_wrap (dx_s s h) = is_wrap s /\ is_check (dx_s s h) = is_check s
  /\ is_lens (dx_s s h) = is_lens s /\ is_work (dx_s s h) = is_work s /\ is_codes (dx_s s h) = is_codes s
  /\ is_window (dx_s s h) = is_window s /\ is_window_blk (dx_s s h) = is_window_blk s
  /\ is_wsize (dx_s s h) = is_wsize s /\ is_self_blk (dx_s s h) = is_self_blk s /\ is_wbits (dx_s s h) = is_wbits s.
Proof. intros s h. unfold dx_s. repeat split; reflexivity. Qed.
Lemma dx_r_facts : forall r e,
  ir_next (dx_r r e) = ir_next r /\ ir_have (dx_r r e) = ir_have r /\ ir_put (dx_r r e) = ir_put r /\ ir_left (dx_r r e) = ir_left r
  /\ ir_hold (dx_r r e) = Z.shiftr (ir_hold r) e /\ ir_bits (dx_r r e) = wrap32 (ir_bits r - e)
  /\ ir_in (dx_r r e) = ir_in r /\ ir_out (dx_r r e) = ir_out r /\ ir_ret (dx_r r e) = ir_ret r.
Proof. intros r e. unfold dx_r. destruct r; repeat split; reflexivity. Qed.

Lemma iwf_set_offset : forall st v, 0 <= v < 2 ^ 32 -> iwf st -> iwf (iset_offset st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.
Lemma iwf_set_back : forall st v, - 2 ^ 31 <= v < 2 ^ 31 -> iwf st -> iwf (iset_back st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.
Lemma dx_s_iwf : forall s h, iwf s -> iwf (dx_s s h).
Proof.
  intros s h H. unfold dx_s. apply iwf_set_back; [apply swrap32_range|]. apply iwf_set_offset; [apply wrap32_range | exact H].
Qed.
Lemma szwrap32_congr : forall x, szwrap 32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 32) with 4294967296.
  Z.to_euclidean_division_equations; lia.
Qed.
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Section ArmDISTEXT.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_DISTEXT : forall flush w, is_mode (w_s w) = DISTEXT -> arm_ok flush w = true ->
    leave_okb (w_s w) = true /\ distext_okb (w_s w) = true.
  Hypothesis OK_DISTEXT_next : forall flush w w2, is_mode (w_s w) = DISTEXT -> arm_ok flush w = true ->
    distext_next w = Some w2 -> arm_ok flush w2 = true.
End ArmDISTEXT.
End RefInflateA_DISTEXT.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.

Module RefInflateA_STORED.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Znumtheory.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition bb_r (r : iregs) : iregs :=
  irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7)).

Lemma arm_STORED_dry : forall flush s c r w1,
  NEEDBITS 32 (mkW s c (bb_r r)) = ALeave w1 -> arm_STORED ivar_ref flush (mkW s c r) = ALeave w1.
Proof. intros flush s c r w1 HN. unfold arm_STORED. mstep1 BYTEBITS_eq. fold (bb_r r). rewrite abind_run, HN. reflexivity. Qed.

Definition st_tail (flush : Z) (s : inflate_state) (c : icall) (r1 : iregs) : ares unit :=
  if negb (Z.land (ir_hold r1) 65535 =? Z.lxor (Z.shiftr (ir_hold r1) 16) 65535)
  then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_stored_block_lengths) r1)
  else let w2 := mkW (iset_mode (iset_length s (Z.land (wrap32 (ir_hold r1)) 65535)) COPY_) c (irset_bits (irset_hold r1 0) 0) in
       if flush =? Z_TREES then ALeave w2 else arm_COPY_ w2.

Lemma arm_STORED_run : forall flush s c r r1,
  NEEDBITS 32 (mkW s c (bb_r r)) = ARun tt (mkW s c r1) -> arm_STORED ivar_ref flush (mkW s c r) = st_tail flush s c r1.
Proof.
  intros flush s c r r1 HN. unfold arm_STORED. mstep1 BYTEBITS_eq. fold (bb_r r). rewrite abind_run, HN.
  mstep1 HOLD_eq. unfold st_tail.
  destruct (negb (Z.land (ir_hold r1) 65535 =? Z.lxor (Z.shiftr (ir_hold r1) 16) 65535)).
  - rewrite go_bad_eq. reflexivity.
  - mstep1 us_eq. mstep1 INITBITS_eq. mstep1 set_mode_eq. cbn [iv_flush_exits ivar_ref andb].
    destruct (flush =? Z_TREES); [apply aleave_eq | reflexivity].
Qed.

Lemma bb_r_facts : forall r, 0 <= ir_bits r < 64 -> 0 <= ir_hold r < 2 ^ ir_bits r ->
  ir_next (bb_r r) = ir_next r /\ ir_have (bb_r r) = ir_have r /\ ir_put (bb_r r) = ir_put r /\ ir_left (bb_r r) = ir_left r
  /\ ir_in (bb_r r) = ir_in r /\ ir_out (bb_r r) = ir_out r /\ ir_ret (bb_r r) = ir_ret r
  /\ ir_bits (bb_r r) = ir_bits r - Z.land (ir_bits r) 7 /\ ir_hold (bb_r r) = Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7)
  /\ ir_bits (bb_r r) = 8 * (ir_bits r / 8) /\ 0 <= ir_hold (bb_r r) < 2 ^ ir_bits (bb_r r).
Proof.
  intros r Hb Hh. pose proof (land7_range (ir_bits r)) as Hk.
  assert (Hk2 : Z.land (ir_bits r) 7 <= ir_bits r) by (rewrite land7_mod; apply Z.mod_le; lia).
  assert (Ebits : wrap32 (ir_bits r - Z.land (ir_bits r) 7) = ir_bits r - Z.land (ir_bits r) 7) by (apply ZIface.wrap32_id; lia).
  unfold bb_r. cbn. rewrite Ebits. repeat (split; [reflexivity|]).
  split; [rewrite land7_mod; Z.to_euclidean_division_equations; lia|].
  rewrite Z.shiftr_div_pow2 by lia. apply hold_drop; lia.
Qed.

Lemma land16_wrap32 : forall h, 0 <= h -> Z.land (wrap32 h) 65535 = h mod 2 ^ 16.
Proof.
  intros h Hh. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. rewrite ZIface.wrap32_mod.
  change (2 ^ 32) with (2 ^ 16 * 2 ^ 16). rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.
Lemma len_check_iff : forall h, 0 <= h ->
  (Z.land h 65535 = Z.lxor (Z.shiftr h 16) 65535 <-> h mod 2 ^ 16 = Z.lxor (h / 2 ^ 16) 65535).
Proof.
  intros h Hh. change 65535 with (Z.ones 16) at 1. rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Section ArmSTORED.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_STORED : forall flush w, is_mode (w_s w) = STORED -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_STORED_COPY_ : forall flush s c r l c' r', is_mode s = STORED -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length s l) COPY_) c' r') = true.

  Local Ltac norm8 := try change (8 * 1) with 8; try change (8 * 2) with 16; try change (8 * 3) with 24; try change (8 * 4) with 32.
  Local Ltac nlia := cbv beta iota delta [Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; lia.
  Local Ltac byte_side :=
    match goal with
    | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- 0 <= arr_get (ic_input ?c) ?i => exact (proj1 (Rinb i ltac:(lia)))
    | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- arr_get (ic_input ?c) ?i < 256 => exact (proj2 (Rinb i ltac:(lia)))
    end.
End ArmSTORED.
End RefInflateA_STORED.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma DECODE_k_O : forall p index need s c r,
  DECODE_k 0 p index need (mkW s c r) = ARun (code_at s p (index (ir_hold r))) (mkW s c r).
Proof. intros. reflexivity. Qed.

Lemma DECODE_k_S : forall k p index need s c r,
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


Lemma dchk_sound : forall k s c p index need r r',
  dchk k c index need (ctab_size p) (code_at s p) r = Some r' ->
  let here := code_at s p (index (ir_hold r')) in
  0 <= index (ir_hold r') < ctab_size p /\ 0 <= need here <= 32
  /\ ir_put r' = ir_put r /\ ir_left r' = ir_left r /\ ir_in r' = ir_in r /\ ir_out r' = ir_out r /\ ir_ret r' = ir_ret r
  /\ (need here <= ir_bits r' -> DECODE_k k p index need (mkW s c r) = ARun here (mkW s c r'))
  /\ (ir_bits r' < need here -> ir_have r' = 0 /\ DECODE_k k p index need (mkW s c r) = ALeave (mkW s c r')).
Proof.
  induction k as [|k IH]; intros s c p index need r r' H; cbn [dchk] in H; cbv zeta;
    (destruct ((0 <=? index (ir_hold r)) && (index (ir_hold r) <? ctab_size p) && (0 <=? need (code_at s p (index (ir_hold r)))) && (need (code_at s p (index (ir_hold r))) <=? 32)) eqn:Hc; [| discriminate H]);
    apply andb_prop in Hc as [Hc H4]; apply andb_prop in Hc as [Hc H3]; apply andb_prop in Hc as [H1 H2];
    apply Z.leb_le in H1; apply Z.ltb_lt in H2; apply Z.leb_le in H3; apply Z.leb_le in H4.
  - destruct (Z.leb_spec (need (code_at s p (index (ir_hold r)))) (ir_bits r)) as [Hb|Hb]; [| discriminate H].
    injection H as <-.
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
    all: intros X; first [rewrite DECODE_k_O; reflexivity | exfalso; lia].
  - rewrite DECODE_k_S. cbv zeta.
    destruct (Z.leb_spec (need (code_at s p (index (ir_hold r)))) (ir_bits r)) as [Hb|Hb].
    + injection H as <-. repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
      all: intros X; first [reflexivity | exfalso; lia].
    + destruct (Z.eqb_spec (ir_have r) 0) as [Hh|Hh].
      * injection H as <-. repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
        all: intros X; first [reflexivity | exfalso; lia | split; [exact Hh | reflexivity]].
      * exact (IH s c p index need (pullr c r) r' H).
Qed.




Definition dist_tail (c : icall) (here : Z) (r : iregs) (sb : inflate_state) : ares unit :=
  let r' := ddrop r (code_bits here) in
  let s' := addback sb (code_bits here) in
  if negb (Z.land (code_op here) 64 =? 0) then ARun tt (mkW (iset_mode s' BAD) (icset_msg c MSG_invalid_distance_code) r')
  else arm_DISTEXT ivar_ref (mkW (iset_mode (iset_extra (iset_offset s' (code_val here)) (Z.land (code_op here) 15)) DISTEXT) c r').

Lemma DECODE_k_run : forall k p index need s c r h s1 c1 r1,
  DECODE_k k p index need (mkW s c r) = ARun h (mkW s1 c1 r1) -> s1 = s /\ c1 = c.
Proof.
  induction k as [|k IH]; intros p index need s c r h s1 c1 r1 H.
  - rewrite DECODE_k_O in H. injection H as _ <- <-. split; reflexivity.
  - rewrite DECODE_k_S in H. cbv zeta in H.
    destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r); [injection H as _ <- <-; split; reflexivity|].
    destruct (ir_have r =? 0); [discriminate H|]. exact (IH _ _ _ _ _ _ _ _ _ _ H).
Qed.

Lemma arm_DIST_eq : forall s c r,
  arm_DIST ivar_ref (mkW s c r) =
    match DECODE1 (is_distcode s) (is_distbits s) (mkW s c r) with
    | ARun last (mkW _ _ r1) =>
        if Z.land (code_op last) 240 =? 0 then
          match DECODE2 (is_distcode s) last (mkW s c r1) with
          | ARun here (mkW _ _ r2) => dist_tail c here (ddrop r2 (code_bits last)) (addback s (code_bits last))
          | ALeave w => ALeave w
          | ARet rc w => ARet rc w
          end
        else dist_tail c last r1 s
    | ALeave w => ALeave w
    | ARet rc w => ARet rc w
    end.
Proof.
  intros s c r. unfold arm_DIST. mstep1 (@gs_eq inflate_state). rewrite abind_run.
  destruct (DECODE1 (is_distcode s) (is_distbits s) (mkW s c r)) as [last [s1 c1 r1] | w | rc w] eqn:H1; try reflexivity.
  destruct (DECODE_k_run _ _ _ _ _ _ _ _ _ _ _ H1) as [-> ->].
  rewrite abind_run.
  destruct (Z.land (code_op last) 240 =? 0).
  - rewrite abind_run.
    destruct (DECODE2 (is_distcode s) last (mkW s c r1)) as [here [s2 c2 r2] | w | rc w] eqn:H2; try reflexivity.
    destruct (DECODE_k_run _ _ _ _ _ _ _ _ _ _ _ H2) as [-> ->].
    mstep1 DROPBITS_eq. unfold add_back, aux. cbn [iv_aux ivar_ref]. mstep1 us_eq. rewrite aret_eq. cbv beta iota.
    mstep1 DROPBITS_eq. mstep1 us_eq. unfold dist_tail, ddrop, addback. cbn [ir_hold ir_bits irset_bits irset_hold is_back iset_back].
    destruct (negb (Z.land (code_op here) 64 =? 0)); [rewrite go_bad_eq; reflexivity|].
    mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
  - rewrite aret_eq. cbv beta iota. mstep1 DROPBITS_eq. unfold add_back, aux. cbn [iv_aux ivar_ref]. mstep1 us_eq.
    unfold dist_tail, ddrop, addback.
    destruct (negb (Z.land (code_op last) 64 =? 0)); [rewrite go_bad_eq; reflexivity|].
    mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.
Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Lemma land_pow2m1 : forall a n, 0 <= n -> Z.land a (2 ^ n - 1) = a mod 2 ^ n.
Proof. intros a n Hn. rewrite <- (Z.land_ones a n) by lia. f_equal. unfold Z.ones. rewrite Z.shiftl_1_l. lia. Qed.

Lemma BITSv_mod : forall h n, 0 <= h -> 0 <= n <= 32 -> BITSv h n = h mod 2 ^ n.
Proof. intros h n Hh Hn. rewrite BITSv_land by lia. apply Z.land_ones. lia. Qed.

Lemma dchk_step : forall k c index need N tab r r',
  dchk k c index need N tab r = Some r' -> ir_bits r < need (tab (index (ir_hold r))) ->
  0 <= index (ir_hold r) < N /\ need (tab (index (ir_hold r))) <= 32
  /\ match k with
     | O => False
     | S k' => (ir_have r = 0 /\ r' = r) \/ (ir_have r <> 0 /\ dchk k' c index need N tab (pullr c r) = Some r')
     end.
Proof.
  intros k c index need N tab r r' H Hb.
  destruct k as [|k']; cbn [dchk] in H;
    (destruct ((0 <=? index (ir_hold r)) && (index (ir_hold r) <? N) && (0 <=? need (tab (index (ir_hold r)))) && (need (tab (index (ir_hold r))) <=? 32)) eqn:Hc; [| discriminate H]);
    apply andb_prop in Hc as [Hc H4]; apply andb_prop in Hc as [Hc H3]; apply andb_prop in Hc as [H1 H2];
    apply Z.leb_le in H1; apply Z.ltb_lt in H2; apply Z.leb_le in H3; apply Z.leb_le in H4;
    rewrite (proj2 (Z.leb_gt _ _) Hb) in H.
  - discriminate H.
  - split; [lia|]. split; [exact H4|].
    destruct (Z.eqb_spec (ir_have r) 0) as [Hh|Hh]; [left; split; [exact Hh | congruence] | right; split; [exact Hh | exact H]].
Qed.

Lemma dchk_found : forall k c index need N tab r r',
  dchk k c index need N tab r = Some r' -> need (tab (index (ir_hold r))) <= ir_bits r ->
  0 <= index (ir_hold r) < N /\ r' = r.
Proof.
  intros k c index need N tab r r' H Hb.
  destruct k as [|k']; cbn [dchk] in H;
    (destruct ((0 <=? index (ir_hold r)) && (index (ir_hold r) <? N) && (0 <=? need (tab (index (ir_hold r)))) && (need (tab (index (ir_hold r))) <=? 32)) eqn:Hc; [| discriminate H]);
    apply andb_prop in Hc as [Hc H4]; apply andb_prop in Hc as [Hc H3]; apply andb_prop in Hc as [H1 H2];
    apply Z.leb_le in H1; apply Z.ltb_lt in H2;
    rewrite (proj2 (Z.leb_le _ _) Hb) in H.
  - injection H as <-. split; [lia | reflexivity].
  - injection H as <-. split; [lia | reflexivity].
Qed.
Definition dtab (s : inflate_state) : Z -> Z := code_at s (is_distcode s).
Definition dN (s : inflate_state) : Z := ctab_len (is_distcode s).

Lemma ctab_size_len : forall p, ctab_size p = ctab_len p.
Proof. intros p. destruct p; reflexivity. Qed.

Section ArmDIST1.
End ArmDIST1.
