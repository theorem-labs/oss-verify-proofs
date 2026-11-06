(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The walk of check_events_step (fuzz/fuzz_decode.c:152-185), fuzz_decode.plain 0x137d0 (40
   instructions, 16-byte frame), against lib/Prog/check_events_step_c.v. check_events_step_ok gives
   rd = the code of the owed step; for rd = 1 it gives each field of ev->msg as the grammar's and
   ev->kind = the owed kind. Rewritten into the event's cells, every bne compares a register with
   itself; the tests rd = 1 (0x137e4) and status = F0 (0x13834) are decided over Z. None branches to
   the `jal abort` at 0x1386c.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout DgnChkLib check_events_step_c.
Import ListNotations.
Open Scope Z_scope.

(* a bne of a register with itself *)
Local Ltac same := step; rewrite ?eqb_same; cbv beta iota delta [negb].

Local Ltac epilogue FR ST sp :=
  step; step; step;                                        (* ld ra; addi sp; ret *)
  apply evt_done; do 16 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  release_frame FR ST (bv_unsigned sp); exact ST.

Theorem check_events_step_holds : check_events_step_contract.
Proof.
  unfold check_events_step_contract, CHECK_EVENTS_STEP, CHECK_EVENTS_STEP_FRAME, OW_SIZE, DE_SIZE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    b o e rd lo ow ev p1 p2 mpad OK RC RS RX MO ME ST HLO DO DE MI.
  unfold check_events_step_ok in OK. rewrite andb_true_iff in OK. destruct OK as [ER OK].
  apply Z.eqb_eq in ER. subst rd.
  unfold owed_cells, spec_msg_cells, spec_event_cells, arr_cells in MO.
  unfold event_cells, dmsg_cells, arr_cells in ME.
  cbn [map seq app] in MO, ME.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  step. step. step.                                        (* addi sp; sd ra; lw a4, 0(a1) *)
  rewrite (sx32_int (sm_code (ow_m ow))) by lia.
  same.                                                    (* rd != m->code *)
  step. step.                                              (* li a4, 1; bne a2, a4 *)
  rewrite (eqb_int64 (sm_code (ow_m ow)) 1) by lia.
  destruct (Z.eqb_spec (sm_code (ow_m ow)) 1) as [E1|E1]; cbv beta iota delta [negb].
  2: epilogue FR ST sp.
  rewrite ?E1 in OK. cbn [Z.eqb Pos.eqb implb] in OK.
  unfold msg_agrees in OK. rewrite !andb_true_iff in OK.
  destruct OK as [[[[[[[EO EL] ES] ER] ED1] ED2] EX] EK].
  apply Z.eqb_eq in EO, EL, ES, ER, ED1, ED2, EK.
  rewrite EO, EL, ES, ER, ED1, ED2, EK in ME.
  step. step. same.                                        (* ev->msg.offset != m->at *)
  step. step. same.                                        (* len *)
  step. step. same.                                        (* status *)
  step. step. same.                                        (* running *)
  step. step. same.                                        (* d1 *)
  step. step. same.                                        (* d2 *)
  rewrite (zxb_b8 (sm_status (ow_m ow))) by lia.
  step. step.                                              (* li a4, 0xf0; bne a2, a4 *)
  rewrite (eqb_int64 (sm_status (ow_m ow)) 240) by lia.
  destruct (Z.eqb_spec (sm_status (ow_m ow)) 240) as [E0|E0]; cbv beta iota delta [negb].
  - rewrite ?E0 in EX. cbn [Z.eqb Pos.eqb implb] in EX. rewrite andb_true_iff in EX.
    destruct EX as [EY EZ]. apply Z.eqb_eq in EY, EZ.
    specialize (RX E0).
    rewrite EY, EZ in ME. unfold sysex_ptr in ME.
    replace (sm_sysex_at (ow_m ow) =? 0) with false in ME by (symmetry; apply Z.eqb_neq; exact RX).
    step. step. step. same.                                (* ev->msg.sysex != b + m->sysex_at *)
    step. step. same.                                      (* sysex_len *)
    step. step. same.                                      (* ev->kind != o->e.kind *)
    epilogue FR ST sp.
  - step. step. same.                                      (* ev->kind != o->e.kind *)
    epilogue FR ST sp.
Qed.
