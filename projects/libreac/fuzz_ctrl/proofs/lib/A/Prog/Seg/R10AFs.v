(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2252 of its 2377 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R10A.v; 45 of its 108 lines of code are new or changed and 2314 lines of the source are left out. *)
(* PROVENANCE. Image A = fuzz_ctrl.asan, libreac v1.9.0 (pinned image and tools as in R10AF.v's header).
   Written by a Theorem Labs lane (a Theorem Labs lane's stage lane for seg_R10) under the NARROWED-STRETCH RULE (a Theorem Labs lane /
   a Theorem Labs lane, 04:23Z / 04:34Z, via a Theorem Labs lane): a stretch of a Theorem Labs lane's split carries the source run's whole premise
   list; this file states the stretch with only the premises its own steps use, and re-derives a Theorem Labs lane's stretch
   from it under a constr_eq pin, so it is provably the same stretch.  It Requires only a Theorem Labs lane's R10AF.v and the
   sources R10AF.v Requires; R10AF.v is unchanged apart from comment text.

   r10a_call34_pre_Fs: the six instructions 0x816ac mv a0,s8 ; 0x816b0 mv a1,s2 ; 0x816b4 ld a2,88(s1) ;
   0x816b8 ld a3,80(s1) ; 0x816bc ld a4,72(s1) ; 0x816c0 jal reac_ctrl_identity_reply, ending in the callee entry
   state (pc = REAC_CTRL_IDENTITY_REPLY, ra = 0x816c4), with the same post as R10AF.r10a_call34_pre_F
   (R10AF.v:357).  Its premises are the ones these steps read: s1 = A with the window bound A + 96 <= 2 ^ 64, the
   three spilled words q64 m (A + 88) pa / (A + 80) pp / (A + 72) pn, and the three rng premises of those loads.
   Dropped (the callee contract's premises, which a Theorem Labs lane's pre_F carries for its of_pre_post pin and which the
   steps never read): s8 / s2 / sp equations, the five value ranges, the stack alignment and window, mem_inv,
   the 50-byte message, the three reply cells, asan_cells / shadow_rw, HIGHMEM_BEG / APPMEM_END, the addressable
   facts, the five runtime cells, fp and the tls cells.
   r10a_call34_pre_F_of_Fs: R10AF.r10a_call34_pre_F's statement, proved from r10a_call34_pre_Fs;
   r10a_call34_pre_F_of_Fs_verbatim: its type is the type of R10AF.r10a_call34_pre_F (constr_eq). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memset asan_memcpy.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R10A.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* R10AF.v's mid-file Require block (R10AF.v:329-339), so the stretch is stated in the environment of
   R10AF.r10a_call34_pre_F (YK11's getr, SlotInv's q64; StepF's step last). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs B3Rtm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require R10AF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Lemma r10a_call34_pre_Fs :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pa pp pn A : Z),
    s1 = Z_to_bv 64 A -> 0 <= A -> A + 96 <= 2 ^ 64 ->
    q64 m (A + 88) pa -> q64 m (A + 80) pp -> q64 m (A + 72) pn ->
    ExecF.rng RNG (A + 88) 8 -> ExecF.rng RNG (A + 80) 8 -> ExecF.rng RNG (A + 72) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x816c4) sp gp tp t0 t1 t2 s0 s1
                               s8 s2 (Z_to_bv 64 pa) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x816ac) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pa pp pn A -> HA0 HAE Qa Qp Qn Ra88 Ra80 Ra72.
  pose proof (R10A.r10a_q64_ro m (A + 88) pa Qa) as Rpa.
  pose proof (R10A.r10a_q64_ro m (A + 80) pp Qp) as Rpp.
  pose proof (R10A.r10a_q64_ro m (A + 72) pn Qn) as Rpn.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  step. step. step. step. step. step.
  apply ExecF.evtF_done. reflexivity.
Qed.

(* a Theorem Labs lane's stretch, re-derived from the narrowed one. *)
Lemma r10a_call34_pre_F_of_Fs :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi nb pa pp pn A spv FS : Z) (g ja jp jn : list byte),
    s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 nb -> s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 spv ->
    0 <= A -> A + 96 <= 2 ^ 64 ->
    q64 m (A + 88) pa -> q64 m (A + 80) pp -> q64 m (A + 72) pn ->
    0 <= phi < 2 ^ 64 -> 0 <= nb < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    spv < 2 ^ 64 -> spv mod 16 = 0 ->
    REAC_CTRL_IDENTITY_REPLY_K <= spv -> stk rsegs m (spv - REAC_CTRL_IDENTITY_REPLY_K) spv ->
    mem_inv rsegs m ->
    length g = 50%nat ->
    (reply_args phi pa pp pn = true -> 50 <= nb ->
       phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi g /\
       (phi + 50 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= phi)) ->
    (reply_args phi pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       rw_cells rsegs m pa [CB 2 ja] /\ rw_cells rsegs m pp [CB 8 jp] /\ rw_cells rsegs m pn [CB 8 jn] /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= phi \/ phi + 50 <= pa) /\ (pp + 8 <= phi \/ phi + 50 <= pp) /\
       (pn + 8 <= phi \/ phi + 50 <= pn) /\
       (pa + 2 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pa) /\
       (pp + 8 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pp) /\
       (pn + 8 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pn)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= spv - REAC_CTRL_IDENTITY_REPLY_K -> spv <= APPMEM_END ->
    addressable m (spv - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    (reply_args phi pa pp pn = true -> 50 <= nb -> addressable m phi 50) ->
    (reply_args phi pa pp pn = true ->
       addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv
      (reac_ctrl_identity_reply_W phi pa pp pn spv) (reac_ctrl_identity_reply_D phi nb pa pp pn) ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv ->
    ExecF.rng RNG (A + 88) 8 -> ExecF.rng RNG (A + 80) 8 -> ExecF.rng RNG (A + 72) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x816c4) sp gp tp t0 t1 t2 s0 s1
                               s8 s2 (Z_to_bv 64 pa) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x816ac) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi nb pa pp pn A spv FS g ja jp jn E8 E2 E1 Esp HA0 HAE Qa Qp Qn
    Hphi Hnb Hpa Hpp Hpn Hsp Hsp16 HK ST HMI Hg50 Hgb Hcells HAC HSW HHM HAPP Awin Hga Haddr Abc BCM MCM GCF
    CF254 CF255 HFP HTLS Ra88 Ra80 Ra72.
  exact (r10a_call34_pre_Fs RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
           s11 t3 t4 t5 t6 F fc m pa pp pn A E1 HA0 HAE Qa Qp Qn Ra88 Ra80 Ra72).
Qed.

Example r10a_call34_pre_F_of_Fs_verbatim : True.
Proof.
  let a := type of R10AF.r10a_call34_pre_F in let b := type of r10a_call34_pre_F_of_Fs in constr_eq a b.
  exact I.
Qed.
