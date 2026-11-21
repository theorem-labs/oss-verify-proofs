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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.

Module RefInflateA_HCRC.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
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


Definition hcrc_fin (s : inflate_state) (c : icall) (r : iregs) : ares unit :=
  ARun tt (mkW (iset_mode (iset_check s 0) TYPE) (icset_adler c 0) r).

Lemma arm_HCRC_nocrc : forall s c r, Z.land (is_flags s) 512 = 0 -> arm_HCRC (mkW s c r) = hcrc_fin s c r.
Proof.
  intros s c r H. unfold arm_HCRC. mstep1 (@gs_eq inflate_state). rewrite H. cbn [Z.eqb negb].
  mstep1 (@aret_eq bool). mstep1 set_adler_check_eq. rewrite set_mode_eq. reflexivity.
Qed.
Lemma arm_HCRC_dry : forall s c r w1, Z.land (is_flags s) 512 <> 0 -> NEEDBITS 16 (mkW s c r) = ALeave w1 -> arm_HCRC (mkW s c r) = ALeave w1.
Proof.
  intros s c r w1 H HN. unfold arm_HCRC. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) H). cbn [negb].
  rewrite abind_run. rewrite abind_run. rewrite HN. reflexivity.
Qed.
Definition hcrc_tail (s : inflate_state) (c : icall) (r1 : iregs) : ares unit :=
  if negb (Z.land (is_wrap s) 4 =? 0) && negb (ir_hold r1 =? Z.land (is_check s) 65535)
  then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_header_crc_mismatch) r1)
  else hcrc_fin s c (irset_bits (irset_hold r1 0) 0).
Lemma arm_HCRC_run : forall s c r r1, Z.land (is_flags s) 512 <> 0 -> NEEDBITS 16 (mkW s c r) = ARun tt (mkW s c r1) ->
  arm_HCRC (mkW s c r) = hcrc_tail s c r1.
Proof.
  intros s c r r1 H HN. unfold arm_HCRC. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) H). cbn [negb].
  rewrite abind_run. rewrite abind_run. rewrite HN. mstep1 HOLD_eq. mstep1 (@gs_eq inflate_state). unfold hcrc_tail.
  destruct (negb (Z.land (is_wrap s) 4 =? 0) && negb (ir_hold r1 =? Z.land (is_check s) 65535)).
  - mstep1 go_bad_eq. rewrite aret_eq. reflexivity.
  - mstep1 INITBITS_eq. rewrite aret_eq. mstep1 set_adler_check_eq. rewrite set_mode_eq. reflexivity.
Qed.

Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Lemma land_mod64_low : forall x m, 0 <= m < 2 ^ 63 -> Z.land (x mod 2 ^ 64) m = Z.land x m.
Proof.
  intros x m Hm. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z_lt_le_dec n 64) as [Hl|Hh].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit m n) with false; [rewrite !Bool.andb_false_r; reflexivity|].
    symmetry. destruct (Z.eq_dec m 0) as [->|Hm0]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 63); [| lia].
    apply Z.log2_lt_pow2; lia.
Qed.

Section ArmHCRC.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_HCRC : forall flush w, is_mode (w_s w) = HCRC -> arm_ok flush w = true -> leave_okb (w_s w) = true.

  Local Ltac norm8 := try change (8 * 1) with 8; try change (8 * 2) with 16; try change (8 * 3) with 24; try change (8 * 4) with 32.
  Local Ltac nlia := cbv beta iota delta [Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; lia.
  Local Ltac byte_side :=
    match goal with
    | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- 0 <= arr_get (ic_input ?c) ?i => exact (proj1 (Rinb i ltac:(lia)))
    | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- arr_get (ic_input ?c) ?i < 256 => exact (proj2 (Rinb i ltac:(lia)))
    end.
End ArmHCRC.
End RefInflateA_HCRC.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.

Module RefInflateA_NAME.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Fixpoint scan_k (input : arr) (next have : Z) (k : nat) (copy : Z) : Z * Z :=
  match k with
  | O => (copy, 0)
  | S k' => let len := arr_get input (next + copy) in
            let copy' := copy + 1 in
            if negb (len =? 0) && (copy' <? have) then scan_k input next have k' copy' else (copy', len)
  end.

Lemma scan_k_loopZ : forall input next have k copy lp,
  0 <= copy -> have < 2 ^ 32 -> copy + Z.of_nat k = have -> (0 < k)%nat ->
  loopZ (Z.of_nat k)
    (fun cl : Z * Z => let '(copy, _) := cl in
       let len := arr_get input (next + copy) in
       let copy := wrap32 (copy + 1) in
       (negb (len =? 0) && (copy <? have), (copy, len)))
    (copy, lp)
  = scan_k input next have k copy.
Proof.
  intros input next have k. induction k as [|k IH]; intros copy lp Hc Hh Hk Hk0; [lia|].
  rewrite loopZ_step by lia. cbn [scan_k].
  rewrite (wrap32_id (copy + 1)) by lia.
  destruct (negb (arr_get input (next + copy) =? 0) && (copy + 1 <? have)) eqn:E.
  - replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. apply IH; lia.
  - reflexivity.
Qed.

Lemma scan_zero_k : forall input next have, 0 < have < 2 ^ 32 ->
  scan_zero input next have = scan_k input next have (Z.to_nat have) 0.
Proof.
  intros input next have Hh. unfold scan_zero.
  rewrite <- (Z2Nat.id have) at 1 by lia. apply scan_k_loopZ; lia.
Qed.

Lemma scan_k_facts : forall input next have k copy,
  0 <= copy < have -> copy + Z.of_nat k >= have ->
  let '(copy', len) := scan_k input next have k copy in
  copy < copy' <= have /\ len = arr_get input (next + copy' - 1) /\ 0 <= copy' /\ (len <> 0 -> copy' < have -> False).
Proof.
  intros input next have k. induction k as [|k IH]; intros copy Hc Hk; [cbn; lia|].
  cbn [scan_k].
  destruct (negb (arr_get input (next + copy) =? 0) && (copy + 1 <? have)) eqn:E.
  - apply andb_prop in E. destruct E as [_ E]. apply Z.ltb_lt in E.
    specialize (IH (copy + 1) ltac:(lia) ltac:(lia)). destruct (scan_k input next have k (copy + 1)) as [c' l']. lia.
  - replace (next + (copy + 1) - 1) with (next + copy) by lia. split; [lia|]. split; [reflexivity|]. split; [lia|].
    intros H1 H2. rewrite (proj2 (Z.eqb_neq _ _) H1) in E. cbn [negb andb] in E. apply Z.ltb_ge in E. lia.
Qed.


Definition nl_s1 (s : inflate_state) (c : icall) (r : iregs) (copy : Z) : inflate_state :=
  if hcrc_on s then iset_check s (icrc32_upd (is_check s) (arr_slice (ic_input c) (ir_next r) copy)) else s.
Definition nl_r2 (r : iregs) (copy : Z) : iregs :=
  irset_next (irset_have r (wrap32 (ir_have r - copy))) (ir_next r + copy).

Lemma name_like_eq : forall flag s c r,
  name_like flag (mkW s c r) =
    if negb (Z.land (is_flags s) flag =? 0) then
      if ir_have r =? 0 then ARun false (mkW s c r)
      else let '(copy, len) := scan_zero (ic_input c) (ir_next r) (ir_have r) in
           ARun (len =? 0) (mkW (nl_s1 s c r copy) c (nl_r2 r copy))
    else ARun true (mkW s c r).
Proof.
  intros flag s c r. unfold name_like. mstep1 (@gs_eq inflate_state).
  destruct (negb (Z.land (is_flags s) flag =? 0)); [| rewrite aret_eq; reflexivity].
  mstep1 (@gr_eq iregs). destruct (ir_have r =? 0); [rewrite aret_eq; reflexivity|].
  rewrite abind_run. unfold aget at 1. cbn [w_c].
  destruct (scan_zero (ic_input c) (ir_next r) (ir_have r)) as [copy len].
  rewrite abind_run. unfold nl_s1.
  assert (E1 : (if hcrc_on s then crc_input copy else aret tt) (mkW s c r)
               = ARun tt (mkW (if hcrc_on s then iset_check s (icrc32_upd (is_check s) (arr_slice (ic_input c) (ir_next r) copy)) else s) c r)).
  { destruct (hcrc_on s); [reflexivity | rewrite aret_eq; reflexivity]. }
  rewrite E1. mstep1 ur_eq. unfold nl_r2. cbn [w_s w_c w_r wset_r].
  destruct (len =? 0); cbn [negb]; rewrite aret_eq; reflexivity.
Qed.

Lemma arm_COMMENT_off : forall s c r, Z.land (is_flags s) 4096 = 0 ->
  arm_COMMENT (mkW s c r) = arm_HCRC (mkW (iset_mode s HCRC) c r).
Proof.
  intros s c r H. unfold arm_COMMENT. rewrite abind_run, name_like_eq, H. cbn [Z.eqb negb].
  mstep1 set_mode_eq. reflexivity.
Qed.
Lemma arm_COMMENT_dry : forall s c r, Z.land (is_flags s) 4096 <> 0 -> ir_have r = 0 ->
  arm_COMMENT (mkW s c r) = ALeave (mkW s c r).
Proof.
  intros s c r H Hh. unfold arm_COMMENT. rewrite abind_run, name_like_eq, (proj2 (Z.eqb_neq _ _) H), Hh. cbn [Z.eqb negb].
  rewrite aleave_eq. reflexivity.
Qed.
Lemma arm_COMMENT_scan : forall s c r copy len, Z.land (is_flags s) 4096 <> 0 -> ir_have r <> 0 ->
  scan_zero (ic_input c) (ir_next r) (ir_have r) = (copy, len) ->
  arm_COMMENT (mkW s c r) =
    if len =? 0 then arm_HCRC (mkW (iset_mode (nl_s1 s c r copy) HCRC) c (nl_r2 r copy))
    else ALeave (mkW (nl_s1 s c r copy) c (nl_r2 r copy)).
Proof.
  intros s c r copy len H Hh HS. unfold arm_COMMENT. rewrite abind_run, name_like_eq, (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) Hh), HS. cbn [negb].
  destruct (len =? 0); [mstep1 set_mode_eq; reflexivity | rewrite aleave_eq; reflexivity].
Qed.

Lemma arm_NAME_off : forall s c r, Z.land (is_flags s) 2048 = 0 ->
  arm_NAME (mkW s c r) = arm_COMMENT (mkW (iset_mode (iset_length s 0) COMMENT) c r).
Proof.
  intros s c r H. unfold arm_NAME. rewrite abind_run, name_like_eq, H. cbn [Z.eqb negb].
  mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.
Lemma arm_NAME_dry : forall s c r, Z.land (is_flags s) 2048 <> 0 -> ir_have r = 0 ->
  arm_NAME (mkW s c r) = ALeave (mkW s c r).
Proof.
  intros s c r H Hh. unfold arm_NAME. rewrite abind_run, name_like_eq, (proj2 (Z.eqb_neq _ _) H), Hh. cbn [Z.eqb negb].
  rewrite aleave_eq. reflexivity.
Qed.
Lemma arm_NAME_scan : forall s c r copy len, Z.land (is_flags s) 2048 <> 0 -> ir_have r <> 0 ->
  scan_zero (ic_input c) (ir_next r) (ir_have r) = (copy, len) ->
  arm_NAME (mkW s c r) =
    if len =? 0 then arm_COMMENT (mkW (iset_mode (iset_length (nl_s1 s c r copy) 0) COMMENT) c (nl_r2 r copy))
    else ALeave (mkW (nl_s1 s c r copy) c (nl_r2 r copy)).
Proof.
  intros s c r copy len H Hh HS. unfold arm_NAME. rewrite abind_run, name_like_eq, (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) Hh), HS. cbn [negb].
  destruct (len =? 0); [mstep1 us_eq; mstep1 set_mode_eq; reflexivity | rewrite aleave_eq; reflexivity].
Qed.

Lemma nl_s1_facts : forall s c r copy,
  is_mode (nl_s1 s c r copy) = is_mode s /\ is_flags (nl_s1 s c r copy) = is_flags s /\ is_wrap (nl_s1 s c r copy) = is_wrap s
  /\ is_head (nl_s1 s c r copy) = is_head s
  /\ is_lens (nl_s1 s c r copy) = is_lens s /\ is_work (nl_s1 s c r copy) = is_work s /\ is_codes (nl_s1 s c r copy) = is_codes s
  /\ is_window (nl_s1 s c r copy) = is_window s /\ is_window_blk (nl_s1 s c r copy) = is_window_blk s
  /\ is_wsize (nl_s1 s c r copy) = is_wsize s /\ is_self_blk (nl_s1 s c r copy) = is_self_blk s /\ is_wbits (nl_s1 s c r copy) = is_wbits s.
Proof. intros s c r copy. unfold nl_s1. destruct (hcrc_on s); repeat split; reflexivity. Qed.

Lemma nl_r2_facts : forall r copy, 0 <= copy <= ir_have r -> ir_have r < 2 ^ 32 ->
  ir_next (nl_r2 r copy) = ir_next r + copy /\ ir_have (nl_r2 r copy) = ir_have r - copy
  /\ ir_put (nl_r2 r copy) = ir_put r /\ ir_left (nl_r2 r copy) = ir_left r
  /\ ir_hold (nl_r2 r copy) = ir_hold r /\ ir_bits (nl_r2 r copy) = ir_bits r
  /\ ir_in (nl_r2 r copy) = ir_in r /\ ir_out (nl_r2 r copy) = ir_out r /\ ir_ret (nl_r2 r copy) = ir_ret r.
Proof.
  intros r copy Hc Hh. unfold nl_r2. cbn. rewrite wrap32_id by lia. repeat split; reflexivity.
Qed.


Lemma land_bit_div : forall a n, 0 <= a -> 0 <= n -> Z.land a (2 ^ n) = (a / 2 ^ n) mod 2 * 2 ^ n.
Proof.
  intros a n Ha Hn.
  assert (Hb : (a / 2 ^ n) mod 2 = Z.b2z (Z.testbit a n)) by (rewrite Z.testbit_spec'; [reflexivity | exact Hn]).
  rewrite Hb. apply Z.bits_inj'. intros m Hm.
  rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec n m) as [<-|Hne].
  - rewrite Bool.andb_true_r. destruct (Z.testbit a n); cbn [Z.b2z]; [rewrite Z.mul_1_l, Z.pow2_bits_true; [reflexivity | lia] | rewrite Z.mul_0_l, Z.bits_0; reflexivity].
  - rewrite Bool.andb_false_r. destruct (Z.testbit a n); cbn [Z.b2z]; [rewrite Z.mul_1_l, Z.pow2_bits_false; [reflexivity | lia] | rewrite Z.mul_0_l, Z.bits_0; reflexivity].
Qed.

Lemma slli51_ltz : forall x, szwrap 64 (x mod 2 ^ 64 * 2 ^ 51) < 0 <-> Z.land x 4096 <> 0.
Proof.
  intros x. rewrite <- (land_mod64_low x 4096) by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)) as Hy. set (y := x mod 2 ^ 64) in *. clearbody y.
  change 4096 with (2 ^ 12). rewrite (land_bit_div y 12) by lia.
  unfold szwrap. change (2 ^ (64 - 1)) with (2 ^ 63).
  Z.to_euclidean_division_equations. lia.
Qed.
Lemma slli52_ltz : forall x, szwrap 64 (x mod 2 ^ 64 * 2 ^ 52) < 0 <-> Z.land x 2048 <> 0.
Proof.
  intros x. rewrite <- (land_mod64_low x 2048) by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)) as Hy. set (y := x mod 2 ^ 64) in *. clearbody y.
  change 2048 with (2 ^ 11). rewrite (land_bit_div y 11) by lia.
  unfold szwrap. change (2 ^ (64 - 1)) with (2 ^ 63).
  Z.to_euclidean_division_equations. lia.
Qed.

Lemma sxu_le : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (szwrap 32 x mod 2 ^ 64 <= szwrap 32 y mod 2 ^ 64 <-> x <= y).
Proof. intros x y Hx Hy. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.
Lemma sxu_lt : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (szwrap 32 x mod 2 ^ 64 < szwrap 32 y mod 2 ^ 64 <-> x < y).
Proof. intros x y Hx Hy. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.

Lemma scan_k_S : forall input next have k copy,
  scan_k input next have (S k) copy =
    (if negb (arr_get input (next + copy) =? 0) && (copy + 1 <? have)
     then scan_k input next have k (copy + 1) else (copy + 1, arr_get input (next + copy))).
Proof. reflexivity. Qed.

Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).
Local Ltac byte_side :=
  match goal with
  | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- 0 <= arr_get (ic_input ?c) ?i => exact (proj1 (Rinb i ltac:(lia)))
  | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- arr_get (ic_input ?c) ?i < 256 => exact (proj2 (Rinb i ltac:(lia)))
  end.


Local Ltac lreg_in := cbn; repeat (first [ left; reflexivity | right ]).

Section ArmNAME.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_COMMENT : forall flush w, is_mode (w_s w) = COMMENT -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_NAME : forall flush w, is_mode (w_s w) = NAME -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_COMMENT_HCRC : forall flush s c r r', is_mode s = COMMENT -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode s HCRC) c r') = true.
  Hypothesis OK_COMMENT_HCRCc : forall flush s c r ck r', is_mode s = COMMENT -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_check s ck) HCRC) c r') = true.
  Hypothesis OK_NAME_COMMENT : forall flush s c r r', is_mode s = NAME -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length s 0) COMMENT) c r') = true.
  Hypothesis OK_NAME_COMMENTc : forall flush s c r ck r', is_mode s = NAME -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length (iset_check s ck) 0) COMMENT) c r') = true.

  Lemma flags_sx : forall s, iwf s -> szwrap 32 (is_flags s mod 2 ^ 32) = is_flags s.
  Proof.
    intros s Rwf. pose proof (iwf_x s Rwf) as (_ & _ & Qflags & _).
    rewrite szwrap_mod by (clear; lia). clear - Qflags. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia.
  Qed.

  Lemma nl_s1_off : forall s c r copy, hcrc_on s = false -> nl_s1 s c r copy = s.
  Proof. intros s c r copy H. unfold nl_s1. rewrite H. reflexivity. Qed.
  Lemma nl_s1_on : forall s c r copy, hcrc_on s = true ->
    nl_s1 s c r copy = iset_check s (icrc32_upd (is_check s) (arr_slice (ic_input c) (ir_next r) copy)).
  Proof. intros s c r copy H. unfold nl_s1. rewrite H. reflexivity. Qed.
  Lemma hcrc_on_eq : forall s, hcrc_on s = negb (Z.land (is_flags s) 512 =? 0) && negb (Z.land (is_wrap s) 4 =? 0).
  Proof. reflexivity. Qed.

  Definition nm_s3 (s1 : inflate_state) : inflate_state := iset_mode (iset_length s1 0) COMMENT.
End ArmNAME.
End RefInflateA_NAME.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.

Module RefInflateA_EXTRA.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition ex_copy (s : inflate_state) (r : iregs) : Z :=
  if ir_have r <? is_length s then ir_have r else is_length s.
Definition ex_s2 (s : inflate_state) (c : icall) (r : iregs) (copy : Z) : inflate_state :=
  if copy =? 0 then s else iset_length (nl_s1 s c r copy) (wrap32 (is_length s - copy)).
Definition ex_r2 (r : iregs) (copy : Z) : iregs :=
  if copy =? 0 then r else nl_r2 r copy.
Definition ex_s3 (s2 : inflate_state) : inflate_state := iset_mode (iset_length s2 0) NAME.

Lemma arm_EXTRA_off : forall s c r, Z.land (is_flags s) 1024 = 0 ->
  arm_EXTRA (mkW s c r) = arm_NAME (mkW (ex_s3 s) c r).
Proof.
  intros s c r H. unfold arm_EXTRA. mstep1 (@gs_eq inflate_state). rewrite H. cbn [Z.eqb negb].
  mstep1 (@aret_eq bool). mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_EXTRA_on : forall s c r, Z.land (is_flags s) 1024 <> 0 ->
  arm_EXTRA (mkW s c r) =
    let copy := ex_copy s r in
    if negb (is_length (ex_s2 s c r copy) =? 0) then ALeave (mkW (ex_s2 s c r copy) c (ex_r2 r copy))
    else arm_NAME (mkW (ex_s3 (ex_s2 s c r copy)) c (ex_r2 r copy)).
Proof.
  intros s c r H. unfold arm_EXTRA. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) H). cbn [negb].
  rewrite abind_run. rewrite abind_run. rewrite (@gr_eq iregs). cbv beta iota.
  fold (ex_copy s r). cbv zeta. unfold ex_s2, ex_r2.
  destruct (ex_copy s r =? 0); cbn [negb].
  - mstep1 (@aret_eq unit). mstep1 (@gs_eq inflate_state).
    destruct (is_length s =? 0); cbn [negb]; rewrite aret_eq; cbv beta iota; [| rewrite aleave_eq; reflexivity].
    mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
  - rewrite abind_run. rewrite abind_run.
    assert (E1 : (if hcrc_on s then crc_input (ex_copy s r) else aret tt) (mkW s c r) = ARun tt (mkW (nl_s1 s c r (ex_copy s r)) c r)).
    { unfold nl_s1. destruct (hcrc_on s); [reflexivity | rewrite aret_eq; reflexivity]. }
    rewrite E1. mstep1 ur_eq. rewrite us_eq. cbv beta iota. fold (nl_r2 r (ex_copy s r)).
    mstep1 (@gs_eq inflate_state).
    pose proof (nl_s1_facts s c r (ex_copy s r)) as (_ & _ & _ & _ & _).
    replace (is_length (nl_s1 s c r (ex_copy s r))) with (is_length s) by (unfold nl_s1; destruct (hcrc_on s); reflexivity).
    cbn [is_length iset_length].
    destruct (wrap32 (is_length s - ex_copy s r) =? 0); cbn [negb]; rewrite aret_eq; cbv beta iota; [| rewrite aleave_eq; reflexivity].
    mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma ex_copy_facts : forall s r, 0 <= is_length s -> 0 <= ir_have r ->
  0 <= ex_copy s r <= ir_have r /\ ex_copy s r <= is_length s /\ (ex_copy s r = 0 <-> is_length s = 0 \/ ir_have r = 0).
Proof. intros s r Hl Hh. unfold ex_copy. destruct (Z.ltb_spec (ir_have r) (is_length s)); lia. Qed.

Lemma ex_s2_facts : forall s c r copy,
  is_mode (ex_s2 s c r copy) = is_mode s /\ is_flags (ex_s2 s c r copy) = is_flags s /\ is_wrap (ex_s2 s c r copy) = is_wrap s
  /\ is_head (ex_s2 s c r copy) = is_head s
  /\ is_lens (ex_s2 s c r copy) = is_lens s /\ is_work (ex_s2 s c r copy) = is_work s /\ is_codes (ex_s2 s c r copy) = is_codes s
  /\ is_window (ex_s2 s c r copy) = is_window s /\ is_window_blk (ex_s2 s c r copy) = is_window_blk s
  /\ is_wsize (ex_s2 s c r copy) = is_wsize s /\ is_self_blk (ex_s2 s c r copy) = is_self_blk s /\ is_wbits (ex_s2 s c r copy) = is_wbits s.
Proof.
  intros s c r copy. unfold ex_s2, nl_s1. destruct (copy =? 0); [repeat split; reflexivity|]. destruct (hcrc_on s); repeat split; reflexivity.
Qed.

Lemma iset_length_length : forall s a b, iset_length (iset_length s a) b = iset_length s b.
Proof. intros s a b. destruct s; reflexivity. Qed.

Section ArmEXTRA.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_EXTRA : forall flush w, is_mode (w_s w) = EXTRA -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_EXTRA_NAME : forall flush s c r r', is_mode s = EXTRA -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length s 0) NAME) c r') = true.
  Hypothesis OK_EXTRA_NAMEc : forall flush s c r ck r', is_mode s = EXTRA -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length (iset_check s ck) 0) NAME) c r') = true.

  Lemma leave_okb_s2 : forall s c r copy, leave_okb s = true -> leave_okb (ex_s2 s c r copy) = true.
  Proof.
    intros s c r copy H. unfold ex_s2, nl_s1. destruct (copy =? 0); [exact H|].
    rewrite hcrc_on_eq. destruct (Z.eqb_spec (Z.land (is_flags s) 512) 0) as [E|E]; cbn [negb andb]; [exact H|].
    destruct (Z.land (is_wrap s) 4 =? 0); cbn [negb andb]; [exact H|].
    unfold leave_okb in *. cbn [is_wrap is_flags is_check iset_length iset_check].
    destruct (Z.eqb_spec (is_flags s) 0) as [F|F]; [exfalso; apply E; rewrite F; reflexivity|]. cbn [negb]. rewrite Bool.orb_true_r. reflexivity.
  Qed.
End ArmEXTRA.
End RefInflateA_EXTRA.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.

Module RefInflateA_HDR.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition hcrc2 (s : inflate_state) (hold : Z) : inflate_state :=
  if hcrc_on s then iset_check s (icrc32_upd (is_check s) [wrap8 hold; wrap8 (Z.shiftr hold 8)]) else s.
Definition hcrc4 (s : inflate_state) (hold : Z) : inflate_state :=
  if hcrc_on s then iset_check s (icrc32_upd (is_check s) [wrap8 hold; wrap8 (Z.shiftr hold 8); wrap8 (Z.shiftr hold 16); wrap8 (Z.shiftr hold 24)]) else s.
Definition r00 (r1 : iregs) : iregs := irset_bits (irset_hold r1 0) 0.

Lemma hcrc_on_length : forall s l, hcrc_on (iset_length s l) = hcrc_on s. Proof. reflexivity. Qed.

Lemma arm_TIME_eq : forall s c r,
  arm_TIME (mkW s c r) =
    match NEEDBITS 32 (mkW s c r) with
    | ARun _ (mkW s1 c1 r1) => arm_OS (mkW (iset_mode (hcrc4 s1 (ir_hold r1)) OS) c1 (r00 r1))
    | ALeave w1 => ALeave w1
    | ARet rc w1 => ARet rc w1
    end.
Proof.
  intros s c r. unfold arm_TIME. rewrite abind_run. destruct (NEEDBITS 32 (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1]; try reflexivity.
  mstep1 HOLD_eq. mstep1 (@gs_eq inflate_state). unfold hcrc4. rewrite abind_run.
  destruct (hcrc_on s1); [unfold CRC4; rewrite us_eq | rewrite aret_eq]; cbv beta iota; mstep1 INITBITS_eq; mstep1 set_mode_eq; reflexivity.
Qed.

Lemma arm_OS_eq : forall s c r,
  arm_OS (mkW s c r) =
    match NEEDBITS 16 (mkW s c r) with
    | ARun _ (mkW s1 c1 r1) => arm_EXLEN (mkW (iset_mode (hcrc2 s1 (ir_hold r1)) EXLEN) c1 (r00 r1))
    | ALeave w1 => ALeave w1
    | ARet rc w1 => ARet rc w1
    end.
Proof.
  intros s c r. unfold arm_OS. rewrite abind_run. destruct (NEEDBITS 16 (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1]; try reflexivity.
  mstep1 HOLD_eq. mstep1 (@gs_eq inflate_state). unfold hcrc2. rewrite abind_run.
  destruct (hcrc_on s1); [unfold CRC2; rewrite us_eq | rewrite aret_eq]; cbv beta iota; mstep1 INITBITS_eq; mstep1 set_mode_eq; reflexivity.
Qed.

Lemma arm_EXLEN_off : forall s c r, Z.land (is_flags s) 1024 = 0 ->
  arm_EXLEN (mkW s c r) = arm_NAME (mkW (ex_s3 (iset_mode s EXTRA)) c r).
Proof.
  intros s c r H. unfold arm_EXLEN. mstep1 (@gs_eq inflate_state). rewrite H. cbn [Z.eqb negb].
  mstep1 (@aret_eq unit). mstep1 set_mode_eq. apply arm_EXTRA_off. exact H.
Qed.

Lemma arm_EXLEN_on : forall s c r, Z.land (is_flags s) 1024 <> 0 ->
  arm_EXLEN (mkW s c r) =
    match NEEDBITS 16 (mkW s c r) with
    | ARun _ (mkW s1 c1 r1) => arm_EXTRA (mkW (iset_mode (hcrc2 (iset_length s1 (wrap32 (ir_hold r1))) (ir_hold r1)) EXTRA) c1 (r00 r1))
    | ALeave w1 => ALeave w1
    | ARet rc w1 => ARet rc w1
    end.
Proof.
  intros s c r H. unfold arm_EXLEN. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) H). cbn [negb].
  rewrite abind_run. rewrite abind_run.
  destruct (NEEDBITS 16 (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1] eqn:HN; try reflexivity.
  assert (Es : s1 = s).
  { unfold NEEDBITS in HN. clear H. revert s c r HN. generalize 8%nat as k. induction k as [|k IH]; intros s c r HN.
    - cbn in HN. unfold aret in HN. congruence.
    - rewrite NEEDBITS_k_S in HN. destruct (ir_bits r <? 16); [| congruence]. destruct (ir_have r =? 0); [congruence | exact (IH _ _ _ HN)]. }
  subst s1.
  mstep1 HOLD_eq. mstep1 us_eq. unfold hcrc2. rewrite hcrc_on_length. rewrite abind_run.
  destruct (hcrc_on s); [unfold CRC2; rewrite us_eq | rewrite aret_eq]; cbv beta iota; rewrite INITBITS_eq; cbv beta iota; mstep1 set_mode_eq; reflexivity.
Qed.

Lemma NEEDBITS_k_run : forall k n s c r s1 c1 r1,
  NEEDBITS_k k n (mkW s c r) = ARun tt (mkW s1 c1 r1) -> s1 = s /\ c1 = c.
Proof.
  induction k as [|k IH]; intros n s c r s1 c1 r1 HN.
  - cbn in HN. unfold aret in HN. split; congruence.
  - rewrite NEEDBITS_k_S in HN. destruct (ir_bits r <? n); [| split; congruence]. destruct (ir_have r =? 0); [congruence | exact (IH _ _ _ _ _ _ _ HN)].
Qed.

Lemma iset_mode_mode : forall s a b, iset_mode (iset_mode s a) b = iset_mode s b.
Proof. intros s a b. destruct s; reflexivity. Qed.
Lemma iset_length_mode : forall s a l, iset_length (iset_mode s a) l = iset_mode (iset_length s l) a.
Proof. intros s a l. destruct s; reflexivity. Qed.
Lemma ex_s3_mode : forall s a, ex_s3 (iset_mode s a) = ex_s3 s.
Proof. intros s a. unfold ex_s3. rewrite iset_length_mode, iset_mode_mode. reflexivity. Qed.

Lemma hcrc2_facts : forall s h,
  is_mode (hcrc2 s h) = is_mode s /\ is_flags (hcrc2 s h) = is_flags s /\ is_wrap (hcrc2 s h) = is_wrap s
  /\ is_head (hcrc2 s h) = is_head s /\ is_length (hcrc2 s h) = is_length s
  /\ is_lens (hcrc2 s h) = is_lens s /\ is_work (hcrc2 s h) = is_work s /\ is_codes (hcrc2 s h) = is_codes s
  /\ is_window (hcrc2 s h) = is_window s /\ is_window_blk (hcrc2 s h) = is_window_blk s
  /\ is_wsize (hcrc2 s h) = is_wsize s /\ is_self_blk (hcrc2 s h) = is_self_blk s /\ is_wbits (hcrc2 s h) = is_wbits s.
Proof. intros s h. unfold hcrc2. destruct (hcrc_on s); repeat split; reflexivity. Qed.
Lemma hcrc4_facts : forall s h,
  is_mode (hcrc4 s h) = is_mode s /\ is_flags (hcrc4 s h) = is_flags s /\ is_wrap (hcrc4 s h) = is_wrap s
  /\ is_head (hcrc4 s h) = is_head s /\ is_length (hcrc4 s h) = is_length s
  /\ is_lens (hcrc4 s h) = is_lens s /\ is_work (hcrc4 s h) = is_work s /\ is_codes (hcrc4 s h) = is_codes s
  /\ is_window (hcrc4 s h) = is_window s /\ is_window_blk (hcrc4 s h) = is_window_blk s
  /\ is_wsize (hcrc4 s h) = is_wsize s /\ is_self_blk (hcrc4 s h) = is_self_blk s /\ is_wbits (hcrc4 s h) = is_wbits s.
Proof. intros s h. unfold hcrc4. destruct (hcrc_on s); repeat split; reflexivity. Qed.

Lemma crc_list_range : forall ck l, (forall b, In b l -> 0 <= b < 256) -> 0 <= icrc32_upd ck l < 2 ^ 64.
Proof.
  intros ck l Hl. unfold icrc32_upd. fold (crc32_upd ck l).
  pose proof (crc32_upd_range ck l Hl) as X. lia.
Qed.
Lemma wrap8_in2 : forall h b, In b [wrap8 h; wrap8 (Z.shiftr h 8)] -> 0 <= b < 256.
Proof. intros h b Hb. destruct Hb as [<-|[<-|[]]]; apply wrap8_range. Qed.
Lemma wrap8_in4 : forall h b, In b [wrap8 h; wrap8 (Z.shiftr h 8); wrap8 (Z.shiftr h 16); wrap8 (Z.shiftr h 24)] -> 0 <= b < 256.
Proof. intros h b Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; apply wrap8_range. Qed.
Lemma hcrc2_iwf : forall s h, iwf s -> iwf (hcrc2 s h).
Proof. intros s h H. unfold hcrc2. destruct (hcrc_on s); [apply iwf_set_check; [apply crc_list_range; apply wrap8_in2 | exact H] | exact H]. Qed.
Lemma hcrc4_iwf : forall s h, iwf s -> iwf (hcrc4 s h).
Proof. intros s h H. unfold hcrc4. destruct (hcrc_on s); [apply iwf_set_check; [apply crc_list_range; apply wrap8_in4 | exact H] | exact H]. Qed.

Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Lemma r00_facts : forall r1,
  ir_next (r00 r1) = ir_next r1 /\ ir_have (r00 r1) = ir_have r1 /\ ir_put (r00 r1) = ir_put r1 /\ ir_left (r00 r1) = ir_left r1
  /\ ir_hold (r00 r1) = 0 /\ ir_bits (r00 r1) = 0 /\ ir_in (r00 r1) = ir_in r1 /\ ir_out (r00 r1) = ir_out r1 /\ ir_ret (r00 r1) = ir_ret r1.
Proof. intros r1. unfold r00. destruct r1; repeat split; reflexivity. Qed.

Local Ltac inl6 H := cbn in H; destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].

Section ArmHDR.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_TIME : forall flush w, is_mode (w_s w) = TIME -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_OS : forall flush w, is_mode (w_s w) = OS -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_EXLEN : forall flush w, is_mode (w_s w) = EXLEN -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_TIME_OS : forall flush s c r r', is_mode s = TIME -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode s OS) c r') = true.
  Hypothesis OK_TIME_OSc : forall flush s c r ck r', is_mode s = TIME -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_check s ck) OS) c r') = true.
  Hypothesis OK_OS_EXLEN : forall flush s c r r', is_mode s = OS -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode s EXLEN) c r') = true.
  Hypothesis OK_OS_EXLENc : forall flush s c r ck r', is_mode s = OS -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_check s ck) EXLEN) c r') = true.
  Hypothesis OK_OS_NAME : forall flush s c r r', is_mode s = OS -> Z.land (is_flags s) 1024 = 0 -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length s 0) NAME) c r') = true.
  Hypothesis OK_OS_NAMEc : forall flush s c r ck r', is_mode s = OS -> Z.land (is_flags s) 1024 = 0 -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length (iset_check s ck) 0) NAME) c r') = true.
  Hypothesis OK_EXLEN_NAME : forall flush s c r r', is_mode s = EXLEN -> Z.land (is_flags s) 1024 = 0 -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length s 0) NAME) c r') = true.
  Hypothesis OK_EXLEN_EXTRA : forall flush s c r l r', is_mode s = EXLEN -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_length s l) EXTRA) c r') = true.
  Hypothesis OK_EXLEN_EXTRAc : forall flush s c r ck l r', is_mode s = EXLEN -> hcrc_on s = true -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_check (iset_length s l) ck) EXTRA) c r') = true.
End ArmHDR.
End RefInflateA_HDR.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition fl_s (s : inflate_state) (hold : Z) : inflate_state := iset_flags s (swrap32 hold).

Lemma arm_FLAGS_eq : forall s c r,
  arm_FLAGS (mkW s c r) =
    match NEEDBITS 16 (mkW s c r) with
    | ARun _ (mkW s1 c1 r1) =>
        let s' := fl_s s1 (ir_hold r1) in
        if negb (Z.land (swrap32 (ir_hold r1)) 255 =? Z_DEFLATED) then ARun tt (mkW (iset_mode s' BAD) (icset_msg c1 MSG_unknown_compression_method) r1)
        else if negb (Z.land (swrap32 (ir_hold r1)) 57344 =? 0) then ARun tt (mkW (iset_mode s' BAD) (icset_msg c1 MSG_unknown_header_flags_set) r1)
        else arm_TIME (mkW (iset_mode (hcrc2 s' (ir_hold r1)) TIME) c1 (r00 r1))
    | ALeave w1 => ALeave w1
    | ARet rc w1 => ARet rc w1
    end.
Proof.
  intros s c r. unfold arm_FLAGS. rewrite abind_run. destruct (NEEDBITS 16 (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1]; try reflexivity.
  mstep1 HOLD_eq. mstep1 us_eq. mstep1 (@gs_eq inflate_state). cbn [is_flags iset_flags]. cbv zeta. unfold fl_s.
  destruct (Z.land (swrap32 (ir_hold r1)) 255 =? Z_DEFLATED); cbn [negb]; [| rewrite go_bad_eq; reflexivity].
  destruct (Z.land (swrap32 (ir_hold r1)) 57344 =? 0); cbn [negb]; [| rewrite go_bad_eq; reflexivity].
  unfold hcrc2. rewrite abind_run.
  destruct (hcrc_on (iset_flags s1 (swrap32 (ir_hold r1)))); [unfold CRC2; rewrite us_eq | rewrite aret_eq]; cbv beta iota; mstep1 INITBITS_eq; mstep1 set_mode_eq; reflexivity.
Qed.

Lemma fl_s_facts : forall s h,
  is_mode (fl_s s h) = is_mode s /\ is_flags (fl_s s h) = swrap32 h /\ is_wrap (fl_s s h) = is_wrap s
  /\ is_head (fl_s s h) = is_head s /\ is_check (fl_s s h) = is_check s
  /\ is_lens (fl_s s h) = is_lens s /\ is_work (fl_s s h) = is_work s /\ is_codes (fl_s s h) = is_codes s
  /\ is_window (fl_s s h) = is_window s /\ is_window_blk (fl_s s h) = is_window_blk s
  /\ is_wsize (fl_s s h) = is_wsize s /\ is_self_blk (fl_s s h) = is_self_blk s /\ is_wbits (fl_s s h) = is_wbits s.
Proof. intros s h. unfold fl_s. repeat split; reflexivity. Qed.

Lemma fl_s_iwf : forall s h, iwf s -> iwf (fl_s s h).
Proof. intros s h H. unfold fl_s. apply iwf_set_flags; [apply swrap32_range | exact H]. Qed.

Lemma swrap32_szwrap : forall h, swrap32 h = szwrap 32 h.
Proof.
  intros h. unfold swrap32, szwrap. rewrite wrap32_mod. unfold two31. change (2 ^ (32 - 1)) with 2147483648. reflexivity.
Qed.
Lemma land255_mod : forall x, Z.land x 255 = x mod 2 ^ 8.
Proof. intros x. change 255 with (Z.ones 8). apply Z.land_ones. lia. Qed.
Lemma swrap32_low8 : forall h, Z.land (swrap32 h) 255 = h mod 2 ^ 8.
Proof.
  intros h. rewrite land255_mod, swrap32_szwrap. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 32) with 4294967296.
  Z.to_euclidean_division_equations; lia.
Qed.
Lemma testbit_57344 : forall m, 0 <= m -> Z.testbit 57344 m = ((13 <=? m) && (m <? 16))%bool.
Proof.
  intros m Hm. replace 57344 with (Z.shiftl (Z.ones 3) 13) by reflexivity. rewrite Z.shiftl_spec by lia.
  destruct (Z.leb_spec 13 m).
  - rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. destruct (Z.ltb_spec (m - 13) 3); destruct (Z.ltb_spec m 16); try reflexivity; lia.
  - rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.
Lemma testbit_7 : forall m, 0 <= m -> Z.testbit 7 m = (m <? 3).
Proof. intros m Hm. replace 7 with (Z.ones 3) by reflexivity. apply Z.testbit_ones_nonneg; lia. Qed.
Lemma land_57344 : forall x, Z.land x 57344 = Z.shiftl (Z.land (Z.shiftr x 13) 7) 13.
Proof.
  intros x. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftl_spec, (testbit_57344 n Hn) by lia.
  destruct (Z.leb_spec 13 n).
  - rewrite Z.land_spec, Z.shiftr_spec, (testbit_7 (n - 13)) by lia. replace (n - 13 + 13) with n by lia.
    cbn [andb]. destruct (Z.ltb_spec (n - 13) 3); destruct (Z.ltb_spec n 16); try reflexivity; lia.
  - rewrite (Z.testbit_neg_r _ (n - 13)) by lia. cbn [andb]. rewrite Bool.andb_false_r. reflexivity.
Qed.
Lemma land_57344_zero : forall x, Z.land x 57344 = 0 <-> (x / 2 ^ 13) mod 2 ^ 3 = 0.
Proof.
  intros x. rewrite land_57344, Z.shiftl_eq_0_iff, Z.shiftr_div_pow2 by lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma swrap32_hi3 : forall h, (szwrap 32 h mod 2 ^ 64 / 2 ^ 13) mod 2 ^ 3 = 0 <-> Z.land (swrap32 h) 57344 = 0.
Proof.
  intros h. rewrite land_57344_zero, swrap32_szwrap.
  generalize (szwrap 32 h) as x. intros x.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 13) with 8192. change (2 ^ 3) with 8.
  Z.to_euclidean_division_equations. lia.
Qed.
Lemma hcrc_on_fl : forall s h, hcrc_on (fl_s s h) = negb (Z.land (szwrap 32 h) 512 =? 0) && negb (Z.land (is_wrap s) 4 =? 0).
Proof. intros s h. unfold fl_s, hcrc_on. cbn [is_flags is_wrap iset_flags]. rewrite swrap32_szwrap. reflexivity. Qed.
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).
Local Ltac byte_side :=
  match goal with
  | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- 0 <= arr_get (ic_input ?c) ?i => exact (proj1 (Rinb i ltac:(lia)))
  | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- arr_get (ic_input ?c) ?i < 256 => exact (proj2 (Rinb i ltac:(lia)))
  end.

Section ArmFLAGS.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_FLAGS : forall flush w, is_mode (w_s w) = FLAGS -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_FLAGS_TIME : forall flush s c r f r', is_mode s = FLAGS -> Z.land f 255 = Z_DEFLATED -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_flags s f) TIME) c r') = true.
  Hypothesis OK_FLAGS_TIMEc : forall flush s c r f ck r', is_mode s = FLAGS -> Z.land f 255 = Z_DEFLATED -> hcrc_on (iset_flags s f) = true ->
    arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode (iset_check (iset_flags s f) ck) TIME) c r') = true.

  Definition fl_res (s : inflate_state) (c : icall) (r1 : iregs) : ares unit :=
    let s' := fl_s s (ir_hold r1) in
    if negb (Z.land (swrap32 (ir_hold r1)) 255 =? Z_DEFLATED) then ARun tt (mkW (iset_mode s' BAD) (icset_msg c MSG_unknown_compression_method) r1)
    else if negb (Z.land (swrap32 (ir_hold r1)) 57344 =? 0) then ARun tt (mkW (iset_mode s' BAD) (icset_msg c MSG_unknown_header_flags_set) r1)
    else arm_TIME (mkW (iset_mode (hcrc2 s' (ir_hold r1)) TIME) c (r00 r1)).
End ArmFLAGS.
