(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Znumtheory.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
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
