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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.

Module RefInflateA_BAD.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section ArmBAD.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_in : forall flush w, is_mode (w_s w) = BAD -> arm_ok flush w = true -> leave_okb (w_s w) = true.
End ArmBAD.
End RefInflateA_BAD.

Module RefInflateA_LIT.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma arm_LIT_eq : forall s c r,
  arm_LIT (mkW s c r)
  = if ir_left r =? 0 then ALeave (mkW s c r)
    else ARun tt (mkW (iset_mode s LEN)
                      (icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) (wrap8 (is_length s))))
                      (irset_left (irset_put r (ir_put r + 1)) (wrap32 (ir_left r - 1)))).
Proof.
  intros s c r. unfold arm_LIT, abind, gr, gs, uc, ur, us, set_mode, aleave.
  cbn [w_s w_c w_r wset_s wset_c wset_r]. destruct (ir_left r =? 0); reflexivity.
Qed.

Section ArmLIT.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_in : forall flush w, is_mode (w_s w) = LIT -> arm_ok flush w = true -> leave_okb (w_s w) = true.
End ArmLIT.
End RefInflateA_LIT.

Module RefInflateA_TYPE.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition r_drop3 (r : iregs) : iregs := irset_bits (irset_hold r (ir_hold r / 2 ^ 3)) (ir_bits r - 3).

Definition typedo_B (flush : Z) (w : iw) : ares unit :=
  let s := w_s w in let c := w_c w in let r := w_r w in
  let v := ir_hold r mod 2 ^ 1 in
  let t := (ir_hold r / 2 ^ 1) mod 2 ^ 2 in
  let s1 := iset_last s v in
  if t =? 0 then ARun tt (mkW (iset_mode s1 STORED) c (r_drop3 r))
  else if t =? 1 then
    (if flush =? Z_TREES then ALeave (mkW (iset_mode (fixedtables s1) LEN_) c (r_drop3 r))
     else ARun tt (mkW (iset_mode (fixedtables s1) LEN_) c (r_drop3 r)))
  else if t =? 2 then ARun tt (mkW (iset_mode s1 TABLE) c (r_drop3 r))
  else ARun tt (mkW (iset_mode s1 BAD) (icset_msg c MSG_invalid_block_type) (r_drop3 r)).

Lemma arm_TYPEDO_run : forall flush s c r s1 c1 r1,
  is_last s = 0 ->
  NEEDBITS 3 (mkW s c r) = ARun tt (mkW s1 c1 r1) ->
  3 <= ir_bits r1 < 64 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  arm_TYPEDO ivar_ref flush (mkW s c r) = typedo_B flush (mkW s1 c1 r1).
Proof.
  intros flush s c r s1 c1 r1 Hlast HN Hb Hh.
  assert (E1 : wrap32 (ir_bits r1 - 1) = ir_bits r1 - 1) by (apply wrap32_id; lia).
  assert (E2 : wrap32 (ir_bits r1 - 1 - 2) = ir_bits r1 - 3) by (rewrite wrap32_id by lia; lia).
  assert (E3 : Z.shiftr (ir_hold r1 / 2 ^ 1) 2 = ir_hold r1 / 2 ^ 3).
  { rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia. reflexivity. }
  assert (E4 : Z.shiftr (ir_hold r1) 1 = ir_hold r1 / 2 ^ 1) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (B1 : BITSv (ir_hold r1) 1 = ir_hold r1 mod 2 ^ 1) by (rewrite BITSv_land, Z.land_ones by lia; reflexivity).
  assert (B2 : BITSv (ir_hold r1 / 2 ^ 1) 2 = (ir_hold r1 / 2 ^ 1) mod 2 ^ 2) by (rewrite BITSv_land, Z.land_ones by (first [apply Z.div_pos; lia | lia]); reflexivity).
  unfold arm_TYPEDO. mstep1 (@gs_eq inflate_state). rewrite Hlast. cbn [Z.eqb negb].
  rewrite abind_run, HN.
  mstep1 BITS_eq. mstep1 us_eq. mstep1 DROPBITS_eq. irnorm. rewrite E1, E4. mstep1 BITS_eq. irnorm. rewrite B1, B2.
  unfold typedo_B, r_drop3. irnorm.
  destruct ((ir_hold r1 / 2 ^ 1) mod 2 ^ 2 =? 0) eqn:T0.
  { rewrite abind_run. rewrite abind_run. rewrite set_mode_eq. cbv beta iota. rewrite aret_eq. rewrite DROPBITS_eq. irnorm. rewrite E3, E2. reflexivity. }
  destruct ((ir_hold r1 / 2 ^ 1) mod 2 ^ 2 =? 1) eqn:T1.
  { rewrite abind_run. rewrite abind_run. rewrite us_eq. cbv beta iota. rewrite abind_run. rewrite set_mode_eq. cbv beta iota. cbn [iv_flush_exits ivar_ref andb].
    destruct (flush =? Z_TREES).
    - rewrite abind_run, DROPBITS_eq. cbv beta iota. rewrite aleave_eq. irnorm. rewrite E3, E2. reflexivity.
    - rewrite aret_eq. rewrite DROPBITS_eq. irnorm. rewrite E3, E2. reflexivity. }
  destruct ((ir_hold r1 / 2 ^ 1) mod 2 ^ 2 =? 2) eqn:T2.
  { rewrite abind_run. rewrite abind_run. rewrite set_mode_eq. cbv beta iota. rewrite aret_eq. rewrite DROPBITS_eq. irnorm. rewrite E3, E2. reflexivity. }
  rewrite abind_run. rewrite abind_run. rewrite go_bad_eq. cbv beta iota. rewrite aret_eq. rewrite DROPBITS_eq. irnorm. rewrite E3, E2. reflexivity.
Qed.

Lemma arm_TYPEDO_leave : forall flush s c r w1,
  is_last s = 0 -> NEEDBITS 3 (mkW s c r) = ALeave w1 ->
  arm_TYPEDO ivar_ref flush (mkW s c r) = ALeave w1.
Proof.
  intros flush s c r w1 Hlast HN.
  unfold arm_TYPEDO. mstep1 (@gs_eq inflate_state). rewrite Hlast. cbn [Z.eqb negb].
  rewrite abind_run, HN. reflexivity.
Qed.

Lemma arm_TYPEDO_last : forall flush s c r,
  is_last s <> 0 ->
  arm_TYPEDO ivar_ref flush (mkW s c r)
  = ARun tt (mkW (iset_mode s CHECK) c
                 (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7)))).
Proof.
  intros flush s c r Hlast.
  unfold arm_TYPEDO. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) Hlast). cbn [negb].
  mstep1 BYTEBITS_eq. rewrite set_mode_eq. reflexivity.
Qed.


Lemma NEEDBITS3_eq : forall s c r,
  0 <= ir_bits r < 64 ->
  NEEDBITS 3 (mkW s c r)
  = if ir_bits r <? 3 then
      (if ir_have r =? 0 then ALeave (mkW s c r) else ARun tt (mkW s c (pullr c r)))
    else ARun tt (mkW s c r).
Proof.
  intros s c r Hb. unfold NEEDBITS. rewrite NEEDBITS_k_S.
  destruct (ir_bits r <? 3) eqn:E; [|reflexivity]. destruct (ir_have r =? 0); [reflexivity|].
  apply NEEDBITS_k_done. unfold pullr. cbn [ir_bits]. apply Z.ltb_lt in E. rewrite wrap32_id by lia. lia.
Qed.

Section ArmTYPE.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_TYPE : forall flush w, is_mode (w_s w) = TYPE -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_TYPEDO : forall flush w, is_mode (w_s w) = TYPEDO -> arm_ok flush w = true -> leave_okb (w_s w) = true.
End ArmTYPE.
End RefInflateA_TYPE.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ArmTerm.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_in_DONE : forall flush w, is_mode (w_s w) = DONE -> arm_ok flush w = true -> leave_okb (w_s w) = true.
End ArmTerm.
