(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The walk of check_cursor_step (fuzz/fuzz_decode.c:41-91), fuzz_decode.plain 0x136dc (28
   instructions, 16-byte frame), against lib/Prog/check_cursor_step_c.v. The model's equalities
   dc_pos = sm_next and dc_status = sm_status_out are rewritten into the cursor's cells first, so the
   two bne at 0x1372c and 0x13738 compare a register with itself. The five code tests at
   0x136f0-0x13720 are decided over Z (DgnChkLib.v) by check_cursor_step_ok: (code = 0) = (r = 0),
   and code = k -> r = k for k = -7, -8, -6, 1. None branches to the `jal abort` at 0x13748.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import diginet_cursor_init_c DgnLayout DgnChkLib
  check_cursor_step_c.
Import ListNotations.
Open Scope Z_scope.

(* a test whose condition is closed *)
Local Ltac lit_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let v := eval vm_compute in cnd in
      replace cnd with v by (vm_compute; reflexivity); cbv iota
  end.

(* beq a1, a4 (r = k) skips beq a3, a4 (code = k), which goes to the abort *)
Local Ltac skip_test code r k :=
  step; rewrite (eqb_int64 r k) by lia;
  destruct (Z.eqb_spec r k); cbv iota;
  [ | step; rewrite (eqb_int64 code k) by lia;
      replace (code =? k) with false by (symmetry; apply Z.eqb_neq; lia); cbv iota ].

(* a bne of a register with itself *)
Local Ltac same := step; rewrite ?eqb_same; cbv beta iota delta [negb].

Theorem check_cursor_step_holds : check_cursor_step_contract.
Proof.
  unfold check_cursor_step_contract, CHECK_CURSOR_STEP, CHECK_CURSOR_STEP_FRAME, SM_SIZE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p c body r lo sm cur OK RC RR HP MP MC ST HLO DP DC MI.
  unfold check_cursor_step_ok in OK. rewrite !andb_true_iff in OK.
  destruct OK as [[[[[[E0 E7] E8] E6] E1] EP] ES].
  apply Z.eqb_eq in EP. apply Z.eqb_eq in ES. apply Bool.eqb_prop in E0.
  assert (H7 : sm_code sm <> -7 \/ r = -7).
  { destruct (Z.eqb_spec (sm_code sm) (-7)) as [X|X]; [right | left; exact X].
    rewrite ?X in E7. apply Z.eqb_eq. exact E7. }
  assert (H8 : sm_code sm <> -8 \/ r = -8).
  { destruct (Z.eqb_spec (sm_code sm) (-8)) as [X|X]; [right | left; exact X].
    rewrite ?X in E8. apply Z.eqb_eq. exact E8. }
  assert (H6 : sm_code sm <> -6 \/ r = -6).
  { destruct (Z.eqb_spec (sm_code sm) (-6)) as [X|X]; [right | left; exact X].
    rewrite ?X in E6. apply Z.eqb_eq. exact E6. }
  assert (H1 : sm_code sm <> 1 \/ r = 1).
  { destruct (Z.eqb_spec (sm_code sm) 1) as [X|X]; [right | left; exact X].
    rewrite ?X in E1. apply Z.eqb_eq. exact E1. }
  clear E7 E8 E6 E1.
  unfold spec_msg_cells in MP. unfold cursor_cells in MC.
  rewrite EP, ES, Z2Nat.id in MC by lia.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  step. step. step.                                        (* addi sp; sd ra; lw a3, 0(a0) *)
  rewrite (sx32_int (sm_code sm)) by lia.
  step. step.                                              (* seqz a4, a3; snez a5, a1 *)
  rewrite (sltiu1_int (sm_code sm)) by lia. rewrite (sltu0_int r) by lia. rewrite E0.
  step.                                                    (* 0x136f0 beq a5, a4: code = 0 <> r = 0 *)
  destruct (r =? 0); cbn [Z.b2z negb]; lit_if.
  all: step; skip_test (sm_code sm) r (-7).                (* 0x136f4 .. 0x136fc *)
  all: step; skip_test (sm_code sm) r (-8).                (* 0x13700 .. 0x13708 *)
  all: step; skip_test (sm_code sm) r (-6).                (* 0x1370c .. 0x13714 *)
  all: step; skip_test (sm_code sm) r 1.                   (* 0x13718 .. 0x13720 *)
  all: step; step; same.                                   (* c->pos != m->next *)
  all: step; step; same.                                   (* c->status != m->status_out *)
  all: step; step; step.                                   (* ld ra; addi sp; ret *)
  all: apply evt_done; do 16 eexists; split; [reflexivity|];
       split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
       release_frame FR ST (bv_unsigned sp); exact ST.
Qed.
