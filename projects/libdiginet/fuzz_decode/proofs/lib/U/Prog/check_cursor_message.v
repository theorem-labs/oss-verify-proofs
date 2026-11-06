(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The walk of check_cursor_message (fuzz/fuzz_decode.c:93-115), fuzz_decode.ubsan 0x13708, against
   lib/U/Prog/check_cursor_message_c.v. The ok path runs from 0x13708 to the `ret` at 0x13794 and never moves sp:
   36 instructions for an F0 message, 24 for any other status (the bne at 0x13760 goes straight to the `ret`).
   The model's equalities (msg_agrees: offset = at, len, status, running, d1, d2, and for F0 sysex = sysex_at and
   sysex_len) are rewritten into the message's cells first, so each of the eight tests that branch to the
   `jal abort` at 0x137a0 (the bne at 0x1371c, 0x13728, 0x13734, 0x13740, 0x1374c, 0x13758, 0x13784, 0x13790)
   compares a register with itself and is not taken. For F0 the payload pointer of the message is b + sysex_at
   (DgnLayout.v sysex_ptr, the offset is not 0 by the contract), the value of the add at 0x13768.
   UBSan checks, each to the unimp at 0x137a4:
   - 0x13708 `or a3, a2, a1` / 0x1370c `andi a3, a3, 7` / 0x13710 `bnez a3` (q or p not 8-aligned) is not taken by
     p mod 8 = 0 and q mod 8 = 0 (ccm_align: (q | p) & 7 = 0);
   - 0x1376c `bltu a3, a0` (b + sysex_at wraps) is not taken by 0 <= sysex_at and b + sysex_at < 2^64
     (ccm_nowrap);
   - 0x13770 `snez a0, a0` / 0x13774 `seqz a4, a3` / 0x13778 `xor a0, a0, a4` / 0x1377c `beqz a0` (b is NULL
     exactly when the sum is not) is not taken by 0 < b, which makes snez 1 (ccm_snez) and the sum not 0, which
     makes seqz 0 (ccm_seqz).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnChkLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout check_cursor_message_c.
Import ListNotations.
Open Scope Z_scope.

(* 0x13708-0x1370c: or a3, a2, a1; andi a3, a3, 7 with both pointers 8-aligned *)
Lemma ccm_align : forall p q, 0 <= p < 2^64 -> 0 <= q < 2^64 -> p mod 8 = 0 -> q mod 8 = 0 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 q)) (bv_unsigned (Z_to_bv 64 p))))) 7 = 0.
Proof.
  intros p q Hp Hq Ap Aq. rewrite (unsigned_lit q), (unsigned_lit p) by lia.
  rewrite unsigned_lit_wrap. rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc.
  change (Z.land (Z.ones 64) 7) with 7. rewrite Z.land_lor_distr_l.
  change 7 with (Z.ones 3). rewrite !Z.land_ones by lia. change (2^3) with 8.
  rewrite Ap, Aq. reflexivity.
Qed.

(* 0x1376c: bltu a3, a0 with a3 = x + b that does not wrap *)
Lemma ccm_nowrap : forall x b, 0 <= x -> 0 <= b -> x + b < 2^64 ->
  bv_ltu (Z_to_bv 64 (x + b)) (Z_to_bv 64 b) = false.
Proof. intros x b Hx Hb Hs. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.

(* 0x13770: snez a0, a0 of a pointer that is not NULL *)
Lemma ccm_snez : forall z, 0 < z < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 1.
Proof.
  intros z Hz. rewrite v_sltu_b2z, !unsigned_lit by lia.
  replace (0 <? z) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* 0x13774: seqz a4, a3 of a sum that is not 0 *)
Lemma ccm_seqz : forall z, 0 < z < 2^64 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 0.
Proof.
  intros z Hz. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (z <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* a bne of a register with itself *)
Local Ltac same := step; rewrite ?eqb_same; cbv beta iota delta [negb].

Theorem check_cursor_message_holds : check_cursor_message_contract.
Proof.
  unfold check_cursor_message_contract, CHECK_CURSOR_MESSAGE, CHECK_CURSOR_MESSAGE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    b p q lo sm msg pad OK HS HX AP AQ UB MP MQ ST HLO DP DQ MI.
  unfold check_cursor_message_ok, msg_agrees in OK. rewrite !andb_true_iff in OK.
  destruct OK as [[[[[[EO EL] ES] ER] E1] E2] EX].
  apply Z.eqb_eq in EO. apply Z.eqb_eq in EL. apply Z.eqb_eq in ES.
  apply Z.eqb_eq in ER. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
  pose proof (ro_cells_bound _ _ _ _ MP) as BP. pose proof (ro_cells_bound _ _ _ _ MQ) as BQ.
  change (Z.of_nat (cells_size (spec_msg_cells sm))) with 56 in BP.
  change (Z.of_nat (cells_size (dmsg_cells b pad msg))) with 40 in BQ.
  unfold spec_msg_cells in MP. unfold dmsg_cells in MQ.
  rewrite EO, EL, ES, ER, E1, E2 in MQ.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x13708-0x13710: the alignment test of msg and m *)
  step. step. rewrite (ccm_align p q) by lia.
  step. if_false.
  step. step. same.                                        (* msg->offset != m->at *)
  step. step. same.                                        (* msg->len != m->len *)
  step. step. same.                                        (* msg->status != m->status *)
  step. step. same.                                        (* msg->running != m->running *)
  step. step. same.                                        (* msg->d1 != m->d1 *)
  step. step. same.                                        (* msg->d2 != m->d2 *)
  step.                                                    (* 0x1375c addi a4, zero, 0xf0 *)
  rewrite (zxb_b8 (sm_status sm)) by lia.
  step.                                                    (* 0x13760 bne a3, a4: status F0 *)
  rewrite (eqb_int64 (sm_status sm) 240) by lia.
  destruct (Z.eqb_spec (sm_status sm) 240) as [E|N]; cbv beta iota delta [negb].
  2: { step.                                               (* 0x13794 ret *)
       apply evt_done. do 16 eexists. split; [reflexivity|].
       split; [exact MU|]. split; [exact WM|]. split; [exact MI|exact ST]. }
  destruct (UB E) as (HB & HA & HSUM). pose proof (HX E) as HNZ.
  replace (sm_status sm =? 240) with true in EX by (symmetry; apply Z.eqb_eq; exact E).
  cbn [implb] in EX. apply andb_true_iff in EX. destruct EX as [DX DL].
  apply Z.eqb_eq in DX. apply Z.eqb_eq in DL.
  replace (sysex_ptr b (dm_sysex msg)) with (sm_sysex_at sm + b) in MQ
    by (unfold sysex_ptr; rewrite DX;
        replace (sm_sysex_at sm =? 0) with false by (symmetry; apply Z.eqb_neq; exact HNZ);
        cbv beta iota; lia).
  rewrite DL in MQ.
  step.                                                    (* 0x13764 ld a3, 0x28(a1) *)
  step.                                                    (* 0x13768 add a3, a3, a0 *)
  step.                                                    (* 0x1376c bltu a3, a0 *)
  rewrite (ccm_nowrap (sm_sysex_at sm) b) by lia. cbv iota.
  step. rewrite (ccm_snez b) by lia.                       (* 0x13770 snez a0, a0 *)
  step. rewrite (ccm_seqz (sm_sysex_at sm + b)) by lia.    (* 0x13774 seqz a4, a3 *)
  step.                                                    (* 0x13778 xor a0, a0, a4 *)
  step. if_false.                                          (* 0x1377c beqz a0 *)
  step. same.                                              (* msg->sysex != b + m->sysex_at *)
  step. step. same.                                        (* msg->sysex_len != m->sysex_len *)
  step.                                                    (* 0x13794 ret *)
  apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|exact ST].
Qed.
