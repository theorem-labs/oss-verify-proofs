(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The walk of check_cursor_message (fuzz/fuzz_decode.c:93-115), fuzz_decode.plain 0x1374c (33
   instructions, 16-byte frame), against lib/Prog/check_cursor_message_c.v. check_cursor_message_ok
   (msg_agrees) gives each field of the library's message as the grammar's; rewritten into the
   message's cells, every bne compares a register with itself. The status test at 0x137a0 is
   decided over Z (status is a byte); for status F0 the payload pointer is b + sysex_at, since the
   offset is not 0. None branches to the `jal abort` at 0x137cc.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout DgnChkLib check_cursor_message_c.
Import ListNotations.
Open Scope Z_scope.

(* a bne of a register with itself *)
Local Ltac same := step; rewrite ?eqb_same; cbv beta iota delta [negb].

Theorem check_cursor_message_holds : check_cursor_message_contract.
Proof.
  unfold check_cursor_message_contract, CHECK_CURSOR_MESSAGE, CHECK_CURSOR_MESSAGE_FRAME, SM_SIZE, DM_SIZE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    b p q lo sm msg pad OK RS RX MP MQ ST HLO DP DQ MI.
  unfold check_cursor_message_ok, msg_agrees in OK. rewrite !andb_true_iff in OK.
  destruct OK as [[[[[[EO EL] ES] ER] E1] E2] EX].
  apply Z.eqb_eq in EO, EL, ES, ER, E1, E2.
  unfold spec_msg_cells in MP. unfold dmsg_cells in MQ.
  rewrite EO, EL, ES, ER, E1, E2 in MQ.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  step. step.                                              (* addi sp; sd ra *)
  step. step. same.                                        (* msg->offset != m->at *)
  step. step. same.                                        (* msg->len != m->len *)
  step. step. same.                                        (* msg->status != m->status *)
  step. step. same.                                        (* running *)
  step. step. same.                                        (* d1 *)
  step. step. same.                                        (* d2 *)
  rewrite (zxb_b8 (sm_status sm)) by lia.
  step. step.                                              (* li a4, 0xf0; bne a3, a4 *)
  rewrite (eqb_int64 (sm_status sm) 240) by lia.
  destruct (Z.eqb_spec (sm_status sm) 240) as [E0|E0]; cbv beta iota delta [negb].
  - rewrite ?E0 in EX. cbn [Z.eqb Pos.eqb implb] in EX. rewrite andb_true_iff in EX.
    destruct EX as [EY EZ]. apply Z.eqb_eq in EY, EZ.
    specialize (RX E0).
    rewrite EY, EZ in MQ. unfold sysex_ptr in MQ.
    replace (sm_sysex_at sm =? 0) with false in MQ by (symmetry; apply Z.eqb_neq; exact RX).
    step. step. step. same.                                (* msg->sysex != b + m->sysex_at *)
    step. step. same.                                      (* msg->sysex_len != m->sysex_len *)
    step. step. step.                                      (* ld ra; addi sp; ret *)
    apply evt_done; do 16 eexists; split; [reflexivity|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
      release_frame FR ST (bv_unsigned sp); exact ST.
  - step. step. step.                                      (* ld ra; addi sp; ret *)
    apply evt_done; do 16 eexists; split; [reflexivity|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
      release_frame FR ST (bv_unsigned sp); exact ST.
Qed.
