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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefAdler_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.

Module RefInflateA_LENGTH.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_TERM.
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


Definition done_w (s : inflate_state) (c : icall) (r : iregs) : iw :=
  mkW (iset_mode s DONE) c (irset_ret r Z_STREAM_END).

Lemma arm_LENGTH_skip : forall s c r,
  is_wrap s = 0 \/ is_flags s = 0 ->
  arm_LENGTH (mkW s c r) = ALeave (done_w s c r).
Proof.
  intros s c r H. unfold arm_LENGTH. mstep1 (@gs_eq inflate_state).
  replace (negb (is_wrap s =? 0) && negb (is_flags s =? 0)) with false
    by (destruct H as [E|E]; rewrite E; cbn; [|rewrite Bool.andb_false_r]; reflexivity).
  mstep1 (@aret_eq bool). mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_LENGTH_dry : forall s c r w1,
  is_wrap s <> 0 -> is_flags s <> 0 -> NEEDBITS 32 (mkW s c r) = ALeave w1 ->
  arm_LENGTH (mkW s c r) = ALeave w1.
Proof.
  intros s c r w1 Hw Hf HN. unfold arm_LENGTH. mstep1 (@gs_eq inflate_state).
  rewrite (proj2 (Z.eqb_neq _ _) Hw), (proj2 (Z.eqb_neq _ _) Hf). cbn [negb andb].
  rewrite abind_run. rewrite abind_run. rewrite HN. reflexivity.
Qed.

Lemma arm_LENGTH_run : forall s c r r1,
  is_wrap s <> 0 -> is_flags s <> 0 -> NEEDBITS 32 (mkW s c r) = ARun tt (mkW s c r1) ->
  arm_LENGTH (mkW s c r)
  = if negb (Z.land (is_wrap s) 4 =? 0) && negb (ir_hold r1 =? Z.land (is_total s) 4294967295)
    then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_incorrect_length_check) r1)
    else ALeave (done_w s c (irset_bits (irset_hold r1 0) 0)).
Proof.
  intros s c r r1 Hw Hf HN. unfold arm_LENGTH. mstep1 (@gs_eq inflate_state).
  rewrite (proj2 (Z.eqb_neq _ _) Hw), (proj2 (Z.eqb_neq _ _) Hf). cbn [negb andb].
  rewrite abind_run. rewrite abind_run. rewrite HN.
  mstep1 HOLD_eq. mstep1 (@gs_eq inflate_state).
  destruct (negb (Z.land (is_wrap s) 4 =? 0) && negb (ir_hold r1 =? Z.land (is_total s) 4294967295)).
  - mstep1 go_bad_eq. rewrite aret_eq. reflexivity.
  - mstep1 INITBITS_eq. rewrite aret_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Section ArmLENGTH.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_in : forall flush w, is_mode (w_s w) = LENGTH -> arm_ok flush w = true -> leave_okb (w_s w) = true.

  Local Ltac norm8 := try change (8 * 1) with 8; try change (8 * 2) with 16; try change (8 * 3) with 24; try change (8 * 4) with 32.
  Local Ltac nlia := cbv beta iota delta [Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; lia.
  Local Ltac byte_side :=
    match goal with
    | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- 0 <= arr_get (ic_input ?c) ?i => exact (proj1 (Rinb i ltac:(lia)))
    | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- arr_get (ic_input ?c) ?i < 256 => exact (proj2 (Rinb i ltac:(lia)))
    end.
End ArmLENGTH.
End RefInflateA_LENGTH.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CHECK.RefInflateA_LENGTH.
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


Lemma arm_CHECK_skip : forall s c r,
  is_wrap s = 0 -> arm_CHECK (mkW s c r) = ALeave (done_w (iset_mode s LENGTH) c r).
Proof.
  intros s c r Hw. unfold arm_CHECK. mstep1 (@gs_eq inflate_state). rewrite Hw. cbn [Z.eqb negb].
  mstep1 (@aret_eq bool). mstep1 set_mode_eq. rewrite (arm_LENGTH_skip _ c r); [reflexivity|]. left. exact Hw.
Qed.

Lemma arm_CHECK_dry : forall s c r w1,
  is_wrap s <> 0 -> NEEDBITS 32 (mkW s c r) = ALeave w1 -> arm_CHECK (mkW s c r) = ALeave w1.
Proof.
  intros s c r w1 Hw HN. unfold arm_CHECK. mstep1 (@gs_eq inflate_state).
  rewrite (proj2 (Z.eqb_neq _ _) Hw). cbn [negb]. rewrite abind_run. rewrite abind_run. rewrite HN. reflexivity.
Qed.

Lemma is_wrap_total : forall s x, is_wrap (iset_total s x) = is_wrap s. Proof. reflexivity. Qed.
Lemma is_flags_total : forall s x, is_flags (iset_total s x) = is_flags s. Proof. reflexivity. Qed.
Lemma is_check_total : forall s x, is_check (iset_total s x) = is_check s. Proof. reflexivity. Qed.
Lemma is_wrap_check : forall s x, is_wrap (iset_check s x) = is_wrap s. Proof. reflexivity. Qed.
Lemma is_flags_check : forall s x, is_flags (iset_check s x) = is_flags s. Proof. reflexivity. Qed.
Lemma ic_outbuf_total_out : forall c x, ic_outbuf (icset_total_out c x) = ic_outbuf c. Proof. intros; destruct c; reflexivity. Qed.

Definition chk_out (r1 : iregs) : Z := wrap32 (ir_out r1 - ir_left r1).
Definition chk_s2 (s : inflate_state) (r1 : iregs) : inflate_state := iset_total s (wrap64 (is_total s + chk_out r1)).
Definition chk_c2 (c : icall) (r1 : iregs) : icall := icset_total_out c (wrap64 (ic_total_out c + chk_out r1)).
Definition chk_r3 (r1 : iregs) : iregs := irset_out (irset_out r1 (chk_out r1)) (ir_left r1).
Definition chk_v (s : inflate_state) (r1 : iregs) : Z := if negb (is_flags s =? 0) then ir_hold r1 else ZSWAP32 (ir_hold r1).
Definition chk_tail (s3 : inflate_state) (c3 : icall) (r1 : iregs) (wrap v : Z) : ares unit :=
  if negb (Z.land wrap 4 =? 0) && negb (v =? is_check s3)
  then ARun tt (mkW (iset_mode s3 BAD) (icset_msg c3 MSG_incorrect_data_check) (chk_r3 r1))
  else arm_LENGTH (mkW (iset_mode s3 LENGTH) c3 (irset_bits (irset_hold (chk_r3 r1) 0) 0)).

Lemma arm_CHECK_run_noupd : forall s c r r1,
  is_wrap s <> 0 -> NEEDBITS 32 (mkW s c r) = ARun tt (mkW s c r1) ->
  (Z.land (is_wrap s) 4 = 0 \/ chk_out r1 = 0) ->
  arm_CHECK (mkW s c r) = chk_tail (chk_s2 s r1) (chk_c2 c r1) r1 (is_wrap s) (chk_v s r1).
Proof.
  intros s c r r1 Hw HN Hno. unfold arm_CHECK. mstep1 (@gs_eq inflate_state).
  rewrite (proj2 (Z.eqb_neq _ _) Hw). cbn [negb]. rewrite abind_run. rewrite abind_run. rewrite HN.
  mstep1 (@gr_eq iregs). mstep1 ur_eq. mstep1 uc_eq. mstep1 us_eq. mstep1 (@gs_eq inflate_state).
  fold (chk_out r1).
  rewrite is_wrap_total.
  replace (negb (Z.land (is_wrap s) 4 =? 0) && negb (chk_out r1 =? 0)) with false
    by (destruct Hno as [E|E]; rewrite E; cbn; [|rewrite Bool.andb_false_r]; reflexivity).
  mstep1 (@aret_eq unit). mstep1 ur_eq. mstep1 HOLD_eq. mstep1 (@gs_eq inflate_state).
  rewrite is_flags_total, is_wrap_total.
  cbn [ir_hold irset_out ir_left]. unfold chk_tail, chk_v, chk_s2, chk_c2, chk_r3.
  destruct (negb (Z.land (is_wrap s) 4 =? 0) && negb ((if negb (is_flags s =? 0) then ir_hold r1 else ZSWAP32 (ir_hold r1)) =? is_check (iset_total s (wrap64 (is_total s + chk_out r1))))).
  - mstep1 go_bad_eq. rewrite aret_eq. reflexivity.
  - mstep1 INITBITS_eq. rewrite aret_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_CHECK_run_upd : forall s c r r1,
  is_wrap s <> 0 -> NEEDBITS 32 (mkW s c r) = ARun tt (mkW s c r1) ->
  Z.land (is_wrap s) 4 <> 0 -> chk_out r1 <> 0 ->
  let v := UPDATE_CHECK_bytes s (is_check s) (arr_slice (ic_outbuf c) (ir_put r1 - chk_out r1) (chk_out r1)) in
  arm_CHECK (mkW s c r) = chk_tail (iset_check (chk_s2 s r1) v) (icset_adler (chk_c2 c r1) v) r1 (is_wrap s) (chk_v s r1).
Proof.
  intros s c r r1 Hw HN H4 Hout. unfold arm_CHECK. mstep1 (@gs_eq inflate_state).
  rewrite (proj2 (Z.eqb_neq _ _) Hw). cbn [negb]. rewrite abind_run. rewrite abind_run. rewrite HN.
  mstep1 (@gr_eq iregs). mstep1 ur_eq. mstep1 uc_eq. mstep1 us_eq. mstep1 (@gs_eq inflate_state).
  fold (chk_out r1).
  rewrite is_wrap_total.
  rewrite (proj2 (Z.eqb_neq _ _) H4), (proj2 (Z.eqb_neq _ _) Hout). cbn [negb andb].
  rewrite abind_run. rewrite abind_run. cbn [w_c w_r ir_put irset_out].
  rewrite ic_outbuf_total_out.
  rewrite set_adler_check_eq. cbv beta iota. mstep1 ur_eq. mstep1 HOLD_eq. mstep1 (@gs_eq inflate_state).
  rewrite ?is_flags_check, ?is_wrap_check, ?is_flags_total, ?is_wrap_total, ?is_check_total.
  cbn [ir_hold irset_out ir_left]. unfold chk_tail, chk_v, chk_s2, chk_c2, chk_r3.
  destruct (negb (Z.land (is_wrap s) 4 =? 0) && negb ((if negb (is_flags s =? 0) then ir_hold r1 else ZSWAP32 (ir_hold r1)) =? is_check _)).
  - mstep1 go_bad_eq. rewrite aret_eq. reflexivity.
  - mstep1 INITBITS_eq. rewrite aret_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Section ArmCHECK.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_CHECK : forall flush w, is_mode (w_s w) = CHECK -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_LENGTH_flags : forall flush s c r, is_mode s = LENGTH -> is_flags s <> 0 -> arm_ok flush (mkW s c r) = true.

  Local Ltac norm8 := try change (8 * 1) with 8; try change (8 * 2) with 16; try change (8 * 3) with 24; try change (8 * 4) with 32.
  Local Ltac nlia := cbv beta iota delta [Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; lia.
  Local Ltac byte_side :=
    match goal with
    | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- 0 <= arr_get (ic_input ?c) ?i => exact (proj1 (Rinb i ltac:(lia)))
    | Rinb : (forall i, _ -> 0 <= arr_get (ic_input ?c) i < 256) |- arr_get (ic_input ?c) ?i < 256 => exact (proj2 (Rinb i ltac:(lia)))
    end.


  Definition chk_s3 (s : inflate_state) (r1 : iregs) (ov : option Z) : inflate_state :=
    match ov with Some V => iset_check (chk_s2 s r1) V | None => chk_s2 s r1 end.
  Definition chk_c3 (c : icall) (r1 : iregs) (ov : option Z) : icall :=
    match ov with Some V => icset_adler (chk_c2 c r1) V | None => chk_c2 c r1 end.

  Lemma chk_c3_facts : forall c r1 ov,
    ic_next_in (chk_c3 c r1 ov) = ic_next_in c /\ ic_avail_in (chk_c3 c r1 ov) = ic_avail_in c
    /\ ic_next_out (chk_c3 c r1 ov) = ic_next_out c /\ ic_avail_out (chk_c3 c r1 ov) = ic_avail_out c
    /\ ic_input (chk_c3 c r1 ov) = ic_input c /\ ic_outbuf (chk_c3 c r1 ov) = ic_outbuf c
    /\ ic_total_in (chk_c3 c r1 ov) = ic_total_in c /\ ic_total_out (chk_c3 c r1 ov) = wrap64 (ic_total_out c + chk_out r1)
    /\ ic_adler (chk_c3 c r1 ov) = match ov with Some V => V | None => ic_adler c end
    /\ ic_data_type (chk_c3 c r1 ov) = ic_data_type c.
  Proof. intros c r1 [V|]; destruct c; repeat split; reflexivity. Qed.

  Lemma chk_s3_eq : forall s r1 ov, exists t ck,
    chk_s3 s r1 ov = iset_check (iset_total s t) ck /\ 0 <= t < 2 ^ 64 /\ ck = match ov with Some V => V | None => is_check s end.
  Proof.
    intros s r1 [V|]; unfold chk_s3, chk_s2.
    - exists (wrap64 (is_total s + chk_out r1)), V. split; [reflexivity|]. split; [apply ZIface.wrap64_range | reflexivity].
    - exists (wrap64 (is_total s + chk_out r1)), (is_check s). split; [destruct s; reflexivity|]. split; [apply ZIface.wrap64_range | reflexivity].
  Qed.
End ArmCHECK.
