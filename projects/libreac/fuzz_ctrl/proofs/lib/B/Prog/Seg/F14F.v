(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 748 of its 797 lines of code are new or changed and 962 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F14.v; 49 of its 96 lines of code are new or changed and 750 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F14.v f14_evt_10 (:234), f14_evt_0c_n (:263), f14_evt_0c (:361) at
     a working branch 3803efccea0 (blob 5318e97101cdc5a7b50380c65df5a64b90c37315);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
     lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f14_evt_10_of_F (evtF_evt + RNG_all) re-derives F14.f14_evt_10 verbatim (that run has no call and
     touches no memory). f14_evt_0c_pre_F is a split stretch (split rule, parent 23:50Z): it re-runs
     F14.v:306-310, the 7 steps 0x8235c -> the bcmp wrapper entry BCMP_WRAP = 0x42aac of BOTH f14_evt_0c_n
     (:263) and f14_evt_0c (:361); those two runs differ only in the memory invariant that the CALLEE's
     contract consumes (mem_inv / MN.ro_agree), which the pre-call stretch does not use, so one stretch serves
     both. The wrapper's return pc 0x82378 IS the runs' exit cut (B82378_at), so there is no _post_F stretch,
     and no callee contract is stated here: the walk (a Theorem Labs lane) composes bcmp_wrap itself. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv memcmp_c bcmp_wrap_c
  reac_ctrl_identity_fragment_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot F13.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import F14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

(* ---- the s9 <> 0 arm (t_sum_ok j): three instructions, no memory access at all, landing at 0x8237c.
   The footprint (evtF) twin of F14.f14_evt_10, in its binders. ---- *)
Lemma f14_evt_10_F : forall (RNG : footprint)
  (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r v : Z),
  a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
  s9 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v <> 0 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v
                              a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 r) s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x8237c) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x8235c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m r v -> Hr -> Hvb Hvnz.
  assert (Hbltz : bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = false).
  { unfold bv_lts. rewrite (signed_lit r) by lia. rewrite (signed_lit 0) by lia. apply Z.ltb_ge. lia. }
  step.
  replace (bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0)) with false by (symmetry; exact Hbltz). cbv iota.
  step. step.
  assert (EV : bv_unsigned (Z_to_bv 64 v) = v) by (apply unsigned_lit; lia).
  replace (negb (bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0))) with true
    by (symmetry; apply Bool.negb_true_iff; unfold bv_eqb; rewrite EV;
        change (bv_unsigned (Z_to_bv 64 0)) with 0; apply Z.eqb_neq; exact Hvnz).
  cbv iota.
  apply evtF_done. reflexivity.
Qed.

(* The compare lemma: the source statement F14.f14_evt_10 back from f14_evt_10_F with RNG := RNG_all. *)
Lemma f14_evt_10_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r v : Z),
    a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    s9 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v <> 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v
                                a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 r) s8 s9 s10 s11 t3 t4 t5 t6)
                             Fr (Z_to_bv 64 0x8237c) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8235c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m r v Ea Hr Es Hvb Hvnz.
  apply (evtF_evt rsegs RNG_all).
  exact (f14_evt_10_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6 Fr fc m r v Ea Hr Es Hvb Hvnz).
Qed.
Definition f14_evt_10_src_check : ltac:(let T := type of F14.f14_evt_10 in exact T) := f14_evt_10_of_F.

(* ---- the s9 = 0 arm, pre-call stretch: the two record loads and the jal, 0x8235c -> the wrapper entry
   BCMP_WRAP = 0x42aac with ra = 0x82378 (the exit cut).  The only memory accesses are the two spill loads
   [A + 200, A + 208) and [A + 208, A + 216); no instrumented check runs before the call. ---- *)
Lemma f14_evt_0c_pre_F : forall (RNG : footprint)
  (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A r L R : Z),
  s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
  0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
  s9 = Z_to_bv 64 0 ->
  bytes_at rsegs m (A + 200) (le8 (Z_to_bv 64 L)) ->
  bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 R)) ->
  rng RNG (A + 200) 8 -> rng RNG (A + 208) 8 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82378) sp gp tp t0 t1 t2 s0 s1v
                              (Z_to_bv 64 L) (Z_to_bv 64 R) (Z_to_bv 64 72) a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 (Z_to_bv 64 r) s8 s9 s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x8235c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r L R -> -> Hr HLb HRb -> H200 H208 R200 R208.
  pose proof (f14_rd8 m (A + 200) (le8 (Z_to_bv 64 L)) H200 ltac:(apply length_le8)) as RD200.
  pose proof (f14_rd8 m (A + 208) (le8 (Z_to_bv 64 R)) H208 ltac:(apply length_le8)) as RD208.
  assert (Hbltz : bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = false).
  { unfold bv_lts. rewrite (signed_lit r) by lia. rewrite (signed_lit 0) by lia. apply Z.ltb_ge. lia. }
  step.
  replace (bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0)) with false by (symmetry; exact Hbltz). cbv iota.
  step. step.
  replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.
