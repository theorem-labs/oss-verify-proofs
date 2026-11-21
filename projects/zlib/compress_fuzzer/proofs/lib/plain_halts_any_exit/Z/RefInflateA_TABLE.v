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
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_NAME.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
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

Section ArmTABLE.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_TABLE : forall flush w, is_mode (w_s w) = TABLE -> arm_ok flush w = true -> leave_okb (w_s w) = true.

  Hypothesis OK_TABLE_next : forall flush w w2, is_mode (w_s w) = TABLE -> arm_ok flush w = true ->
    table_next w = Some w2 -> arm_ok flush w2 = true.
End ArmTABLE.
