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
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_NAME.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_HDR.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition fl_s (s : inflate_state) (hold : Z) : inflate_state := iset_flags s (swrap32 hold).

Lemma land255_mod : forall x, Z.land x 255 = x mod 2 ^ 8.
Proof. intros x. change 255 with (Z.ones 8). apply Z.land_ones. lia. Qed.

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
