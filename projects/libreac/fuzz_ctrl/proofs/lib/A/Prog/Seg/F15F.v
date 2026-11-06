(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 748 of its 797 lines of code are new or changed and 962 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F14.v, with its module paths, module names, addresses and numbers changed; 549 of its 668 lines of code are new or changed and 678 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F15.v; 109 of its 214 lines of code are new or changed and 563 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F15.v babf75c6d098 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F15.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F15.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint twins of Seg/F15.v's run lemmas (segments F15 = 0x82174 -> 0x82178 and F15b = 0x82178 ->
   0x822a0 / 0x821d0; no call, no memory change):
   - f15_evt_dc_F: F15.f15_evt_dc (:166), the single `bnez a0` at 0x82174 with a0 = 0. It reads and writes no
     memory (instruction fetch is not an access), so it has NO rng premise.
   - f15_evt_c4_F: F15.f15_evt_c4 (:185), `li a0,1 ; bne s9,a0` with s9 <> 1. No data access, no rng premise.
   - f15_evt_34_F: F15.f15_evt_34 (:206), the s9 = 1 arm: the four checked tests, the loop set-up and the v1.9
     load of [A+112]. Its eight 8-byte loads are exactly the eight regions its own bytes_at premises name
     ([A+272], [A+264], [A+96], [A+88], [A+80], [A+112], [Q], [N]): one rng premise each, in that order.
   F15.f15_run (:278) is NOT re-run: like sl_run_lib it concludes SR, not evt, so it is out of the spec's scope
   (a Theorem Labs lane ruling of 2026-10-28 on sl_run_lib, the same lemma shape); it stays plain.
   F15.v itself is unchanged apart from comment text; its f15_cond / f15_sub tactics and its arithmetic lemmas are reused by Import,
   and only f15_state (which ends in Exec.evt_done) is restated here over ExecF.evtF_done. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv memcmp_c bcmp_wrap_c
  reac_ctrl_identity_fragment_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F13 F14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
(* F15 itself, imported for its f15_cond / f15_sub tactics and its arithmetic lemmas. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F15.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF ExecF_all.
Import ListNotations.
(* As in F15.v: YK11 last among the term-level names (its seg_rom / getr). *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* F15.f15_state over ExecF.evtF (its only change: ExecF.evtF_done in place of Exec.evt_done). *)
Ltac f15F_state :=
  apply ExecF.evtF_done;
  first [ reflexivity
        | (repeat match goal with
           | |- context [Z_to_bv 64 (?a + 0)] => replace (a + 0) with a by lia
           end); reflexivity ].

(* ---- the single-instruction run of F15: 0x82174 with a0 = 0, landing at 0x82178. No data access. ---- *)
Lemma f15_evt_dc_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0v = Z_to_bv 64 0 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82174) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m ->.
  step.
  f15_cond false ltac:(apply Bool.negb_false_iff; apply f15_eqb_true; lia).
  f15F_state.
Qed.

Lemma f15_evt_dc_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0v = Z_to_bv 64 0 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82174) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m E0.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  exact (f15_evt_dc_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6 Fr fc m E0).
Qed.

(* ---- F15b, the s9 <> 1 arm: two instructions, landing at 0x822a0. No data access. ---- *)
Lemma f15_evt_c4_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
    s9v = Z_to_bv 64 r -> 0 <= r <= 1 -> r <> 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x822a0) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m r -> Hr Hr1.
  step. step.
  f15_cond true ltac:(apply Bool.negb_true_iff; apply f15_eqb_false; lia).
  f15F_state.
Qed.

Lemma f15_evt_c4_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
    s9v = Z_to_bv 64 r -> 0 <= r <= 1 -> r <> 1 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x822a0) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m r E9 Hr Hr1.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  exact (f15_evt_c4_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9v s10 s11 t3 t4 t5 t6 Fr fc m r E9 Hr Hr1).
Qed.

(* ---- F15b, the s9 = 1 arm: the four checked tests, the loop set-up and the load of [A+112]. The eight
   8-byte loads are the eight regions the lemma's own bytes_at premises name. ---- *)
Lemma f15_evt_34_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A F Q N L Nf : Z),
    s1v = Z_to_bv 64 A -> s9v = Z_to_bv 64 1 ->
    0 <= F /\ F + 72 < 2 ^ 64 -> 0 <= Q /\ Q + 8 < 2 ^ 64 -> 0 <= N /\ N + 8 < 2 ^ 64 ->
    1 <= L <= 51 ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 Q)) ->
    bytes_at rsegs m (A + 264) (le8 (Z_to_bv 64 N)) ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 (F + 8))) ->
    bytes_at rsegs m (A + 88) (le8 (Z_to_bv 64 (F + 19))) ->
    bytes_at rsegs m (A + 80) (le8 (Z_to_bv 64 (F + 15))) ->
    bytes_at rsegs m (A + 112) (le8 (Z_to_bv 64 Nf)) ->
    bytes_at rsegs m Q (le8 (Z_to_bv 64 (F + 19))) ->
    bytes_at rsegs m N (le8 (Z_to_bv 64 L)) ->
    ExecF.rng RNG (A + 272) 8 -> ExecF.rng RNG (A + 264) 8 ->
    ExecF.rng RNG (A + 96) 8 -> ExecF.rng RNG (A + 88) 8 -> ExecF.rng RNG (A + 80) 8 ->
    ExecF.rng RNG (A + 112) 8 -> ExecF.rng RNG Q 8 -> ExecF.rng RNG N 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp (Z_to_bv 64 Nf) t1 t2 s0 s1v (Z_to_bv 64 (F + 15)) (Z_to_bv 64 0)
                                (Z_to_bv 64 (F + 19)) (Z_to_bv 64 L) (Z_to_bv 64 (L + 5))
                                (Z_to_bv 64 (F + 15)) a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m A F Q N L Nf -> -> HF HQ HN HL H272 H264 H96 H88 H80 H112 HQv HNv
    G272 G264 G96 G88 G80 G112 GQ GN.
  pose proof (rd8 m (A + 272) _ H272 (length_le8 _)) as R272.
  pose proof (rd8 m (A + 264) _ H264 (length_le8 _)) as R264.
  pose proof (rd8 m (A + 96) _ H96 (length_le8 _)) as R96.
  pose proof (rd8 m (A + 88) _ H88 (length_le8 _)) as R88.
  pose proof (rd8 m (A + 80) _ H80 (length_le8 _)) as R80.
  pose proof (rd8 m (A + 112) _ H112 (length_le8 _)) as R112.
  pose proof (rd8 m Q _ HQv (length_le8 _)) as RQ.
  pose proof (rd8 m N _ HNv (length_le8 _)) as RN.
  (* 0x82178 li a0,1 ; 0x8217c bne s9,a0 (s9 = 1): not taken *)
  step. step.
  f15_cond false ltac:(apply Bool.negb_false_iff; apply f15_eqb_true; lia).
  (* 0x82180 ld a0,272(s1) ; 0x82184 ld a2,0(a0) ; 0x82188 ld a0,96(s1) *)
  step. step. step.
  (* 0x8218c bltu a2,a0: pl = (F + 8) + 11, not taken *)
  step.
  f15_cond false ltac:(apply f15_ltu_false; lia).
  (* 0x82190 sub a0,a2,a0 = 11 *)
  step. f15_sub 11.
  (* 0x82194 li a1,64 ; 0x82198 bltu a1,a0: 64 < 11 false *)
  step. step.
  f15_cond false ltac:(apply f15_ltu_false; lia).
  (* 0x8219c ld a1,264(s1) ; 0x821a0 ld a3,0(a1) ; 0x821a4 addi a1,a3,2 ; 0x821a8 li a4,64 *)
  step. step. step. step.
  (* 0x821ac sub a0,a4,a0 = 53 (both operands are literals here, so the step normalizes it) *)
  step.
  (* 0x821b0 bltu a0,a1: 53 < L + 2 false (L <= 51) *)
  step.
  f15_cond false ltac:(apply f15_ltu_false; lia).
  (* 0x821b4 ld a0,88(s1) ; 0x821b8 bne a2,a0: pl = F + 19, not taken *)
  step. step.
  f15_cond false ltac:(apply Bool.negb_false_iff; apply f15_eqb_true; lia).
  (* 0x821bc li a1,0 ; 0x821c0 addi a4,a3,5 ; 0x821c4 ld a0,80(s1) ; 0x821c8 mv a5,a0 ; 0x821cc ld t0,112(s1) *)
  step. step. step. step. step.
  f15F_state.
Qed.

Lemma f15_evt_34_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A F Q N L Nf : Z),
    s1v = Z_to_bv 64 A -> s9v = Z_to_bv 64 1 ->
    0 <= F /\ F + 72 < 2 ^ 64 -> 0 <= Q /\ Q + 8 < 2 ^ 64 -> 0 <= N /\ N + 8 < 2 ^ 64 ->
    1 <= L <= 51 ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 Q)) ->
    bytes_at rsegs m (A + 264) (le8 (Z_to_bv 64 N)) ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 (F + 8))) ->
    bytes_at rsegs m (A + 88) (le8 (Z_to_bv 64 (F + 19))) ->
    bytes_at rsegs m (A + 80) (le8 (Z_to_bv 64 (F + 15))) ->
    bytes_at rsegs m (A + 112) (le8 (Z_to_bv 64 Nf)) ->
    bytes_at rsegs m Q (le8 (Z_to_bv 64 (F + 19))) ->
    bytes_at rsegs m N (le8 (Z_to_bv 64 L)) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp (Z_to_bv 64 Nf) t1 t2 s0 s1v (Z_to_bv 64 (F + 15)) (Z_to_bv 64 0)
                                (Z_to_bv 64 (F + 19)) (Z_to_bv 64 L) (Z_to_bv 64 (L + 5))
                                (Z_to_bv 64 (F + 15)) a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m A F Q N L Nf E1 E9 HF HQ HN HL H272 H264 H96 H88 H80 H112 HQv HNv.
  pose proof H272 as (P272a & P272b & _). rewrite length_le8 in P272b.
  pose proof H264 as (P264a & P264b & _). rewrite length_le8 in P264b.
  pose proof H96 as (P96a & P96b & _). rewrite length_le8 in P96b.
  pose proof H88 as (P88a & P88b & _). rewrite length_le8 in P88b.
  pose proof H80 as (P80a & P80b & _). rewrite length_le8 in P80b.
  pose proof H112 as (P112a & P112b & _). rewrite length_le8 in P112b.
  pose proof HQv as (PQa & PQb & _). rewrite length_le8 in PQb.
  pose proof HNv as (PNa & PNb & _). rewrite length_le8 in PNb.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f15_evt_34_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9v s10 s11 t3 t4 t5 t6 Fr fc m A F Q N L Nf E1 E9 HF HQ HN HL
           H272 H264 H96 H88 H80 H112 HQv HNv).
  all: apply ExecF.rng_all; lia.
Qed.

(* ---- The pins: each *_of_F states F15's v1.9 text, term for term. ---- *)
Example f15_evt_dc_of_F_verbatim : True.
Proof.
  let a := type of F15.f15_evt_dc in let b := type of f15_evt_dc_of_F in constr_eq a b.
  exact I.
Qed.

Example f15_evt_c4_of_F_verbatim : True.
Proof.
  let a := type of F15.f15_evt_c4 in let b := type of f15_evt_c4_of_F in constr_eq a b.
  exact I.
Qed.

Example f15_evt_34_of_F_verbatim : True.
Proof.
  let a := type of F15.f15_evt_34 in let b := type of f15_evt_34_of_F in constr_eq a b.
  exact I.
Qed.

