(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 1327 of its 1387 lines of code are new or changed and 951 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/YTail.v, with its module paths and module names changed; 176 of its 306 lines of code are new or changed and 1257 lines of the source are left out. *)
(* rule 24: no function proved.
   Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
     image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
       sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
     source runs: lib/B/Prog/Seg/YTail.v y3_evt (:66), y2_evt (:457), y2_evt_r (:521), y1_evt (:743),
       jrel_evt_real (:1102), jrel_evt_side (:1133) at a working branch 3803efccea0
       (blob d015d45646020bf0fd03664b1ffe0a31aabe6bbd);
     tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
           lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
     compare: y3_evt_of_F, jrel_evt_real_of_F, jrel_evt_side_of_F (evtF_evt + rng_all) re-derive the source
       statements verbatim.  The three runs with a call are split at the call and carry no callee contract:
       y1_pre_F re-runs YTail.v:783 (the `jal 3dd30 <frame_release_6>` at 0x82f48, up to the callee entry
       0x3dd30) and y1_post_F re-runs YTail.v:836 (the `j 0x82f5c` at 0x82f4c, from the return pc to the run's
       end); y2_pre_F re-runs YTail.v:479 (the `jal 55024 <meta_fill_00>` at 0x82f58, up to the callee entry
       0x55024) and serves both y2_evt and y2_evt_r, whose only difference is the a0 / a1 binder form, which
       this stretch does not read.  y2 has no post stretch: the callee returns at 0x82f5c, which is the run's
       own Q.  No `_F` steps through a callee, and the MemNorm.evt_normalize of the source runs wraps the
       callee alone, so no stretch here crosses it. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require YTail.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.
(* As in YTail.v: every lia of this file gets the values of the v1.9 frame constants. *)
Local Ltac lia := pose proof FRAME_BYTES_val; pose proof FRAME_SHADOW_val; Lia.lia.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

Section YTailF.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.FPState}.

(* local copy of YTail.v's rd8 *)
Lemma ytf_rd8 : forall m A w, bytes_at rsegs m A (le8 w) -> ov_read_bytes rsegs m (wa A) 8 = Some (le8 w).
Proof.
  intros m A w H.
  pose proof (bytes_at_ov_read rsegs m A (le8 w) 0 8 H ltac:(rewrite length_le8; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH.
Qed.

(* ------------------------------------------------------------------ Y3 (no call)
   0x82f5c li a0,0; 0x82f60 addi sp,s0,-448; 0x82f64-0x82f94 ld ra / s0-s11 from [Sv - 8 .. Sv - 104];
   0x82f98 addi sp,sp,448; 0x82f9c ret.  Reads [Sv - 104, Sv); writes no memory. *)
Lemma y3_evt_F :
  forall (RNG : footprint)
         (ra0 sp0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sv Rv : Z)
         (w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : word),
    v0 = Z_to_bv 64 Sv -> 448 <= Sv < 2 ^ 64 -> Rv mod 2 = 0 -> 0 <= Rv < 2 ^ 64 ->
    w1 = Z_to_bv 64 Rv ->
    bytes_at rsegs m (Sv - 104) (le8 w27 ++ le8 w26 ++ le8 w25 ++ le8 w24 ++ le8 w23 ++ le8 w22 ++ le8 w21 ++
      le8 w20 ++ le8 w19 ++ le8 w18 ++ le8 w9 ++ le8 w8 ++ le8 w1) ->
    rng RNG (Sv - 104) 104 ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         ms' = MS (mkR w1 (Z_to_bv 64 Sv) gp tp t0' t1' t2' w8 w9
                       (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
                       t3' t4' t5' t6')
                  Fr (Z_to_bv 64 Rv) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82f5c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Fr fc m Sv Rv w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
    -> HS HRe HRb -> HSV RSAV.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 104) (le8 w27) _) HSV) as (B27 & Q1).
  rewrite length_le8 in Q1. replace (Sv - 104 + Z.of_nat 8) with (Sv - 96) in Q1 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 96) (le8 w26) _) Q1) as (B26 & Q2).
  rewrite length_le8 in Q2. replace (Sv - 96 + Z.of_nat 8) with (Sv - 88) in Q2 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 88) (le8 w25) _) Q2) as (B25 & Q3).
  rewrite length_le8 in Q3. replace (Sv - 88 + Z.of_nat 8) with (Sv - 80) in Q3 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 80) (le8 w24) _) Q3) as (B24 & Q4).
  rewrite length_le8 in Q4. replace (Sv - 80 + Z.of_nat 8) with (Sv - 72) in Q4 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 72) (le8 w23) _) Q4) as (B23 & Q5).
  rewrite length_le8 in Q5. replace (Sv - 72 + Z.of_nat 8) with (Sv - 64) in Q5 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 64) (le8 w22) _) Q5) as (B22 & Q6).
  rewrite length_le8 in Q6. replace (Sv - 64 + Z.of_nat 8) with (Sv - 56) in Q6 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 56) (le8 w21) _) Q6) as (B21 & Q7).
  rewrite length_le8 in Q7. replace (Sv - 56 + Z.of_nat 8) with (Sv - 48) in Q7 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 48) (le8 w20) _) Q7) as (B20 & Q8).
  rewrite length_le8 in Q8. replace (Sv - 48 + Z.of_nat 8) with (Sv - 40) in Q8 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 40) (le8 w19) _) Q8) as (B19 & Q9).
  rewrite length_le8 in Q9. replace (Sv - 40 + Z.of_nat 8) with (Sv - 32) in Q9 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 32) (le8 w18) _) Q9) as (B18 & Q10).
  rewrite length_le8 in Q10. replace (Sv - 32 + Z.of_nat 8) with (Sv - 24) in Q10 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 24) (le8 w9) _) Q10) as (B9 & Q11).
  rewrite length_le8 in Q11. replace (Sv - 24 + Z.of_nat 8) with (Sv - 16) in Q11 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 16) (le8 w8) _) Q11) as (B8 & Q12).
  rewrite length_le8 in Q12. replace (Sv - 16 + Z.of_nat 8) with (Sv - 8) in Q12 by lia.
  pose proof (ytf_rd8 m (Sv - 104) w27 B27) as L27.
  pose proof (ytf_rd8 m (Sv - 96) w26 B26) as L26.
  pose proof (ytf_rd8 m (Sv - 88) w25 B25) as L25.
  pose proof (ytf_rd8 m (Sv - 80) w24 B24) as L24.
  pose proof (ytf_rd8 m (Sv - 72) w23 B23) as L23.
  pose proof (ytf_rd8 m (Sv - 64) w22 B22) as L22.
  pose proof (ytf_rd8 m (Sv - 56) w21 B21) as L21.
  pose proof (ytf_rd8 m (Sv - 48) w20 B20) as L20.
  pose proof (ytf_rd8 m (Sv - 40) w19 B19) as L19.
  pose proof (ytf_rd8 m (Sv - 32) w18 B18) as L18.
  pose proof (ytf_rd8 m (Sv - 24) w9 B9) as L9.
  pose proof (ytf_rd8 m (Sv - 16) w8 B8) as L8.
  pose proof (ytf_rd8 m (Sv - 8) (Z_to_bv 64 Rv) Q12) as L1.
  clear B27 B26 B25 B24 B23 B22 B21 B20 B19 B18 B9 B8 Q12 HSV.
  step. step.
  do 13 step.
  step. step.
  rewrite ?Z.add_0_r.
  replace (Sv + -448 + 448) with Sv by lia.
  replace (ret_pc (Z_to_bv 64 Rv)) with (Z_to_bv 64 Rv)
    by (symmetry; apply ret_pc_even; [lia | exact HRe]).
  apply evtF_done. do 14 eexists. reflexivity.
Qed.

(* The auditor's compare lemma: YTail.v:66 y3_evt verbatim, from y3_evt_F at RNG_all. *)
Lemma y3_evt_of_F :
  forall (ra0 sp0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sv Rv : Z)
         (w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : word),
    v0 = Z_to_bv 64 Sv -> 448 <= Sv < 2 ^ 64 -> Rv mod 2 = 0 -> 0 <= Rv < 2 ^ 64 ->
    w1 = Z_to_bv 64 Rv ->
    bytes_at rsegs m (Sv - 104) (le8 w27 ++ le8 w26 ++ le8 w25 ++ le8 w24 ++ le8 w23 ++ le8 w22 ++ le8 w21 ++
      le8 w20 ++ le8 w19 ++ le8 w18 ++ le8 w9 ++ le8 w8 ++ le8 w1) ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         ms' = MS (mkR w1 (Z_to_bv 64 Sv) gp tp t0' t1' t2' w8 w9
                       (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
                       t3' t4' t5' t6')
                  Fr (Z_to_bv 64 Rv) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82f5c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Fr fc m Sv Rv w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
    E0 HS HRe HRb E1 HSV.
  apply (evtF_evt rsegs RNG_all).
  apply (y3_evt_F RNG_all ra0 sp0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
           v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Fr fc m Sv Rv w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
           E0 HS HRe HRb E1 HSV).
  apply rng_all; lia.
Qed.
Definition y3_evt_src_check : ltac:(let T := type of YTail.y3_evt in exact T) := y3_evt_of_F.

(* Resolve a branch condition c to b from H : c = b (YTail.v:1096 ytail_br).  StepF's if_true_by / if_false_by
   leave one goal too few here: `replace` closes its side goal by assumption when H is in context. *)
Ltac ytf_br b H :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (symmetry; exact H); cbv iota
  end.

(* ------------------------------------------------------------------ Jrel (no call)
   0x82f2c lui a0,0x45e03; 0x82f30 addiw a0,a0,1550; 0x82f34 sd a0,0(s9); 0x82f38 beqz s8,0x82f50.
   Real arm (s8 = 0): 0x82f50 li a1,FRAME_SHADOW; 0x82f54 mv a0,s3, to 0x82f58.
   Writes [fr, fr + 8); reads no memory. *)
Lemma jrel_evt_real_F :
  forall (RNG : footprint)
         (ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3w s4 s5 s6 s7 s8w s9w s10 s11
          t3 t4 t5 t6 : word) (mem : word -> option byte) (fr SHv lo hi : Z),
  s3w = Z_to_bv 64 SHv -> s8w = Z_to_bv 64 0 -> s9w = Z_to_bv 64 fr ->
  rw_cells rsegs mem fr [C8 (Z_to_bv 64 0x41b58ab3)] ->
  stk rsegs mem lo hi ->
  rng RNG fr 8 ->
  evtF rsegs RNG
    (fun ms => exists m' : word -> option byte,
       ms = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SHv) (Z_to_bv 64 FRAME_SHADOW) a2 a3 a4 a5 a6 a7
                   s2 s3w s4 s5 s6 s7 s8w s9w s10 s11 t3 t4 t5 t6)
                fp_regs (Z_to_bv 64 0x82f58) fp_csr None m' (seg_rom rsegs) /\
       munch [(fr, fr + 8)] mem m' /\ wmono rsegs mem m' /\
       bytes_at rsegs m' fr (le8 (Z_to_bv 64 0x45e0360e)) /\ stk rsegs m' lo hi)
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
            s2 s3w s4 s5 s6 s7 s8w s9w s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82f2c) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3w s4 s5 s6 s7 s8w s9w s10 s11
    t3 t4 t5 t6 mem fr SHv lo hi -> -> -> HRW HST RFR.
  pose proof (munch_refl [(fr, fr + 8)] mem) as MU.
  pose proof (wmono_refl rsegs mem) as WM.
  step. step. step.
  assert (HB : bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) = true) by apply bv_eqb_refl.
  step.
  ytf_br true HB.
  step. step.
  apply evtF_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [|exact HST].
  destruct HRW as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

(* The auditor's compare lemma: YTail.v:1102 jrel_evt_real verbatim, from jrel_evt_real_F at RNG_all. *)
Lemma jrel_evt_real_of_F :
  forall (ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3w s4 s5 s6 s7 s8w s9w s10 s11
          t3 t4 t5 t6 : word) (mem : word -> option byte) (fr SHv lo hi : Z),
  s3w = Z_to_bv 64 SHv -> s8w = Z_to_bv 64 0 -> s9w = Z_to_bv 64 fr ->
  rw_cells rsegs mem fr [C8 (Z_to_bv 64 0x41b58ab3)] ->
  stk rsegs mem lo hi ->
  LE.evt rsegs
    (fun ms => exists m' : word -> option byte,
       ms = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SHv) (Z_to_bv 64 FRAME_SHADOW) a2 a3 a4 a5 a6 a7
                   s2 s3w s4 s5 s6 s7 s8w s9w s10 s11 t3 t4 t5 t6)
                fp_regs (Z_to_bv 64 0x82f58) fp_csr None m' (seg_rom rsegs) /\
       munch [(fr, fr + 8)] mem m' /\ wmono rsegs mem m' /\
       bytes_at rsegs m' fr (le8 (Z_to_bv 64 0x45e0360e)) /\ stk rsegs m' lo hi)
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
            s2 s3w s4 s5 s6 s7 s8w s9w s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82f2c) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3w s4 s5 s6 s7 s8w s9w s10 s11
    t3 t4 t5 t6 mem fr SHv lo hi E3 E8 E9 HRW HST.
  assert (Hsz : Z.of_nat (cells_size [C8 (Z_to_bv 64 0x41b58ab3)]) = 8) by reflexivity.
  pose proof HRW as HRW2. destruct HRW2 as (_ & (Hf0 & Hf8 & _)). rewrite Hsz in Hf8.
  apply (evtF_evt rsegs RNG_all).
  apply (jrel_evt_real_F RNG_all ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3w s4 s5 s6 s7
           s8w s9w s10 s11 t3 t4 t5 t6 mem fr SHv lo hi E3 E8 E9 HRW HST).
  apply rng_all; [exact Hf0 | exact Hf8].
Qed.
Definition jrel_evt_real_src_check : ltac:(let T := type of YTail.jrel_evt_real in exact T) := jrel_evt_real_of_F.

(* Side arm (s8 = fr): 0x82f3c lui a0,0x1; 0x82f40 addiw a1,a0,-960 (a1 = FRAME_BYTES); 0x82f44 mv a0,s8,
   to 0x82f48.  Writes [fr, fr + 8); reads no memory. *)
Lemma jrel_evt_side_F :
  forall (RNG : footprint)
         (ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8w s9w s10 s11
          t3 t4 t5 t6 : word) (mem : word -> option byte) (fr lo hi : Z),
  s8w = Z_to_bv 64 fr -> s9w = Z_to_bv 64 fr -> 0 < fr < 2 ^ 64 ->
  rw_cells rsegs mem fr [C8 (Z_to_bv 64 0x41b58ab3)] ->
  stk rsegs mem lo hi ->
  rng RNG fr 8 ->
  evtF rsegs RNG
    (fun ms => exists m' : word -> option byte,
       ms = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 FRAME_BYTES) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8w s9w s10 s11 t3 t4 t5 t6)
                fp_regs (Z_to_bv 64 0x82f48) fp_csr None m' (seg_rom rsegs) /\
       munch [(fr, fr + 8)] mem m' /\ wmono rsegs mem m' /\
       bytes_at rsegs m' fr (le8 (Z_to_bv 64 0x45e0360e)) /\ stk rsegs m' lo hi)
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
            s2 s3 s4 s5 s6 s7 s8w s9w s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82f2c) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8w s9w s10 s11
    t3 t4 t5 t6 mem fr lo hi -> -> Hfr HRW HST RFR.
  pose proof (munch_refl [(fr, fr + 8)] mem) as MU.
  pose proof (wmono_refl rsegs mem) as WM.
  step. step. step.
  assert (HB : bv_eqb (Z_to_bv 64 fr) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intro E. apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite !LMS.unsigned_lit in E by lia. lia. }
  step.
  ytf_br false HB.
  step. step. step.
  apply evtF_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [|exact HST].
  destruct HRW as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

(* The auditor's compare lemma: YTail.v:1133 jrel_evt_side verbatim, from jrel_evt_side_F at RNG_all. *)
Lemma jrel_evt_side_of_F :
  forall (ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8w s9w s10 s11
          t3 t4 t5 t6 : word) (mem : word -> option byte) (fr lo hi : Z),
  s8w = Z_to_bv 64 fr -> s9w = Z_to_bv 64 fr -> 0 < fr < 2 ^ 64 ->
  rw_cells rsegs mem fr [C8 (Z_to_bv 64 0x41b58ab3)] ->
  stk rsegs mem lo hi ->
  LE.evt rsegs
    (fun ms => exists m' : word -> option byte,
       ms = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 FRAME_BYTES) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8w s9w s10 s11 t3 t4 t5 t6)
                fp_regs (Z_to_bv 64 0x82f48) fp_csr None m' (seg_rom rsegs) /\
       munch [(fr, fr + 8)] mem m' /\ wmono rsegs mem m' /\
       bytes_at rsegs m' fr (le8 (Z_to_bv 64 0x45e0360e)) /\ stk rsegs m' lo hi)
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
            s2 s3 s4 s5 s6 s7 s8w s9w s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82f2c) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8w s9w s10 s11
    t3 t4 t5 t6 mem fr lo hi E8 E9 Hfr HRW HST.
  assert (Hsz : Z.of_nat (cells_size [C8 (Z_to_bv 64 0x41b58ab3)]) = 8) by reflexivity.
  pose proof HRW as HRW2. destruct HRW2 as (_ & (Hf0 & Hf8 & _)). rewrite Hsz in Hf8.
  apply (evtF_evt rsegs RNG_all).
  apply (jrel_evt_side_F RNG_all ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
           s8w s9w s10 s11 t3 t4 t5 t6 mem fr lo hi E8 E9 Hfr HRW HST).
  apply rng_all; [exact Hf0 | exact Hf8].
Qed.
Definition jrel_evt_side_src_check : ltac:(let T := type of YTail.jrel_evt_side in exact T) := jrel_evt_side_of_F.

(* ------------------------------------------------------------------ Y2, split at its one call
   0x82f58 `jal 55024 <meta_fill_00>`: the single instruction of y2_evt / y2_evt_r before the callee.  It stops
   AT the callee entry 0x55024 with ra = the return pc 0x82f5c, and touches no memory.  There is no post
   stretch: the callee returns at 0x82f5c, which is the run's own Q. *)
Lemma y2_pre_F :
  forall (RNG : footprint)
         (ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte),
  evtF rsegs RNG
    (fun ms => ms = MS (mkR (Z_to_bv 64 0x82f5c) sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       fp_regs (Z_to_bv 64 0x55024) fp_csr None mem (seg_rom rsegs))
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82f58) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem.
  step.
  apply evtF_done. reflexivity.
Qed.

(* ------------------------------------------------------------------ Y1, split at its one call
   0x82f48 `jal 3dd30 <frame_release_6>`: the single instruction of y1_evt before the callee.  It stops AT the
   callee entry 0x3dd30 with ra = the return pc 0x82f4c, and touches no memory. *)
Lemma y1_pre_F :
  forall (RNG : footprint)
         (ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte),
  evtF rsegs RNG
    (fun ms => ms = MS (mkR (Z_to_bv 64 0x82f4c) sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       fp_regs (Z_to_bv 64 0x3dd30) fp_csr None mem (seg_rom rsegs))
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82f48) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem.
  step.
  apply evtF_done. reflexivity.
Qed.

(* 0x82f4c `j 0x82f5c`: y1_evt's step after the callee returns, from the return pc to the run's end.  It
   touches no memory and writes no register (the link register is x0). *)
Lemma y1_post_F :
  forall (RNG : footprint)
         (ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte),
  evtF rsegs RNG
    (fun ms => ms = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       fp_regs (Z_to_bv 64 0x82f5c) fp_csr None mem (seg_rom rsegs))
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82f4c) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem.
  step.
  apply evtF_done. reflexivity.
Qed.

End YTailF.
