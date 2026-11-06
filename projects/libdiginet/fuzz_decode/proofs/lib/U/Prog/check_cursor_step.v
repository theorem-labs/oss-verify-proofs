(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The walk of check_cursor_step (fuzz/fuzz_decode.c:41-91), fuzz_decode.ubsan 0x1368c (27 instructions walked to the
   `ret` at 0x136f4; the ok path never moves sp), against lib/U/Prog/check_cursor_step_c.v. The UBSan twin of
   lib/Prog/check_cursor_step.v. The model's equalities dc_pos = sm_next and dc_status = sm_status_out are rewritten
   into the cursor's cells first, so the two bne at 0x136e4 and 0x136f0 compare a register with itself. The five
   code tests at 0x136a0-0x136d0 are decided over Z (DgnChkLib.v) by check_cursor_step_ok: (code = 0) = (r = 0),
   and code = k -> r = k for k = -7, -8, -6, 1. None branches to the `jal abort` at 0x13700.
   UBSan traps: 0x1368c `andi a3, a0, 7` / 0x13690 `bnez a3` and 0x136d4 `andi a1, a2, 7` / 0x136d8 `bnez a1` to the
   unimp at 0x13704 are not taken: p mod 8 = 0 and c mod 8 = 0 (land7_mod8).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnChkLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import diginet_cursor_init_c DgnLayout
  check_cursor_step_c.
Import ListNotations.
Open Scope Z_scope.

(* andi _, x, 7: the low three bits are the residue mod 8 *)
Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

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

(* andi / bnez of an 8-aligned address *)
Local Ltac aligned A HA := step; rewrite ?unsigned_lit by lia; rewrite land7_mod8, HA by lia; step; if_false.

Theorem check_cursor_step_holds : check_cursor_step_contract.
Proof.
  unfold check_cursor_step_contract, CHECK_CURSOR_STEP, CHECK_CURSOR_STEP_FRAME, SM_SIZE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p c body r lo sm cur OK RC RR HP AP AC MP MC ST HLO DP DC MI.
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
  pose proof (ro_cells_bound rsegs m p _ MP) as BP. pose proof (ro_cells_bound rsegs m c _ MC) as BC.
  cbn [spec_msg_cells cursor_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BP, BC.
  unfold spec_msg_cells in MP. unfold cursor_cells in MC.
  rewrite EP, ES, Z2Nat.id in MC by lia.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  aligned p AP.                                            (* 0x1368c andi; 0x13690 bnez: UBSan *)
  step.                                                    (* lw a3, 0(a0) *)
  rewrite (sx32_int (sm_code sm)) by lia.
  step. step.                                              (* seqz a4, a3; snez a5, a1 *)
  rewrite (sltiu1_int (sm_code sm)) by lia. rewrite (sltu0_int r) by lia. rewrite E0.
  step.                                                    (* 0x136a0 beq a5, a4: code = 0 <> r = 0 *)
  destruct (r =? 0); cbn [Z.b2z negb]; lit_if.
  all: step; skip_test (sm_code sm) r (-7).                (* 0x136a4 .. 0x136ac *)
  all: step; skip_test (sm_code sm) r (-8).                (* 0x136b0 .. 0x136b8 *)
  all: step; skip_test (sm_code sm) r (-6).                (* 0x136bc .. 0x136c4 *)
  all: step; skip_test (sm_code sm) r 1.                   (* 0x136c8 .. 0x136d0 *)
  all: aligned c AC.                                       (* 0x136d4 andi; 0x136d8 bnez: UBSan *)
  all: step; step; same.                                   (* c->pos != m->next *)
  all: step; step; same.                                   (* c->status != m->status_out *)
  all: step.                                               (* ret *)
  all: apply evt_done; do 16 eexists; split; [reflexivity|];
       split; [eassumption|]; split; [eassumption|]; split; eassumption.
Qed.
