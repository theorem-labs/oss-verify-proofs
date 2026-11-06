(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 823 of its 864 lines of code are new or changed and 970 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F3F.v, with its module paths, module names, addresses and numbers changed; 312 of its 369 lines of code are new or changed and 807 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P6F.v; 30 of its 136 lines of code are new or changed and 263 lines of the source are left out. *)
(* lib/A/Prog/Seg/P6Fs.v -- segment P6 of fuzz_ctrl image A (libreac v1.9.0, ASan build): the pre stretch of the
   split runs p6_evt / p6_evt_ro of lib/A/Prog/Seg/P6F.v (a Theorem Labs lane's), restated with the MINIMAL premise list the
   walk's glue (lib/A/ACtlG/P6.v) consumes.  rule 24: no function proved (a segment stretch).  Written by a Theorem Labs
   lane; route (A) decided by a Theorem Labs lane 04:21Z, agreed by a Theorem Labs lane (via a Theorem Labs lane).

   WHY THE MINIMAL LIST IS CORRECT.  The eight instructions 0x81bd8 .. 0x81bf4 (li a0,0; li a1,0; ld s7,232(s1);
   mv a2,s7; ld s8,224(s1); mv a3,s8; mv a4,s4; jal reac_ctrl_identity_reply) read memory only at A + 232 and A + 224
   (s1 = A), so p6_evt_pre_Fs needs only s1 = A, the two spill bytes and their two rng rows; every other premise of
   P6F.p6_evt_pre_F / p6_evt_ro_pre_F (mem_inv / ro_agree, stk, asan_cells, shadow_rw, the window and PARSE_BC
   addressable bytes, the REAL / GOT_CF / CF cells, fp [1%nat] and reac_ctrl_identity_reply_tls) is a premise of the
   PLAIN callee contract, which the cgif-form walk does not use (it cites a Theorem Labs lane's treac_ctrl_identity_reply_spec at
   the callee entry instead).  p6_evt_pre_F_of_Fs and p6_evt_ro_pre_F_of_Fs prove that the minimal stretch IS
   a Theorem Labs lane's stretch: each re-derives P6F's lemma from p6_evt_pre_Fs, and its _verbatim pin checks by constr_eq
   that its type is the type of P6F.p6_evt_pre_F / P6F.p6_evt_ro_pre_F, term for term.

   WHAT EACH LEMMA RE-STATES
     p6_evt_pre_Fs            P6F.p6_evt_pre_F (= P6F.p6_evt_ro_pre_F up to the dropped premises): the same binders
                              minus S FS, the same start state and the same end state (the callee entry 0x83f8c with
                              ra = 0x81bf8), premises s1 = A, the spill bytes at A + 232 / A + 224, rng of both.
     p6_evt_pre_F_of_Fs       P6F.p6_evt_pre_F's text verbatim, proved from p6_evt_pre_Fs.
     p6_evt_ro_pre_F_of_Fs    P6F.p6_evt_ro_pre_F's text verbatim, proved from p6_evt_pre_Fs.
   No post stretch: the reply spec's continuation is the exit cut 0x81bf8 itself.  The rng rows are P6Fs.rng.tsv.

   PROVENANCE.  Source: Seg/P6F.v on the glue base (from a working branch eb89fed7fac) (its script at
   P6F.v (at head lib/A/Prog/Seg/P6F.v:65-88 and :252-268) is the script here, unchanged).  Image A = fuzz_ctrl.asan, pinned
   (internal path) sha256
   aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d.  The Require / Import block is P6F.v's own
   (P6F.v:11-27); the ro statement names image-A's YK11 seg_rom through a full-path alias instead of P6F.v:216's
   Import.  Built on a build machine (cb, packed fuzz_ctrl base 23b918fe0c2e, FACTS ed6b6b7b0ab). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP RcAsanFPLib reac_ctrl_parse_c reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import P6.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require P6F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- the minimal pre stretch: 0x81bd8 .. the entry of reac_ctrl_identity_reply (0x83f8c), ra = 0x81bf8 ---- *)

Lemma p6_evt_pre_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A pa pp : Z),
    s1 = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) ->
    bytes_at rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) ->
    ExecF.rng RNG (A + 232) 8 ->
    ExecF.rng RNG (A + 224) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81bf8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0)
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) s4 a5 a6 a7 s2 s3 s4 s5 s6
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81bd8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A pa pp -> H232 H224 R232 R224.
  assert (HL232 : ov_read_bytes rsegs m (wa (A + 232)) 8 = Some (le8 (Z_to_bv 64 pa))).
  { pose proof (bytes_at_ov_read rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) 0 8 H232
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL224 : ov_read_bytes rsegs m (wa (A + 224)) 8 = Some (le8 (Z_to_bv 64 pp))).
  { pose proof (bytes_at_ov_read rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) 0 8 H224
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step. (* 81bd8 li a0,0 *)
  step. (* 81bdc li a1,0 *)
  step. (* 81be0 ld s7,232(s1) *)
  step. (* 81be4 mv a2,s7 *)
  step. (* 81be8 ld s8,224(s1) *)
  step. (* 81bec mv a3,s8 *)
  step. (* 81bf0 mv a4,s4 *)
  step. (* 81bf4 jal reac_ctrl_identity_reply *)
  apply ExecF.evtF_done. reflexivity.
Qed.

(* ---- a Theorem Labs lane's p6_evt_pre_F (P6F.v:36-64), verbatim, from the minimal stretch ---- *)

Lemma p6_evt_pre_F_of_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S FS pa pp : Z),
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 S ->
    0 <= S < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 ->
    bytes_at rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) ->
    bytes_at rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) ->
    S mod 16 = 0 -> REAC_CTRL_IDENTITY_REPLY_K <= S ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S -> mem_inv rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
       [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    ExecF.rng RNG (A + 232) 8 ->
    ExecF.rng RNG (A + 224) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81bf8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0)
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) s4 a5 a6 a7 s2 s3 s4 s5 s6
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81bd8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S FS pa pp E1 _ _ _ _ H232 H224 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R232 R224.
  exact (p6_evt_pre_Fs RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A pa pp E1 H232 H224 R232 R224).
Qed.

(* The pin: p6_evt_pre_F_of_Fs states P6F.p6_evt_pre_F's text, term for term (constr_eq: syntactic). *)
Example p6_evt_pre_F_of_Fs_verbatim : True.
Proof.
  let a := type of P6F.p6_evt_pre_F in let b := type of p6_evt_pre_F_of_Fs in constr_eq a b.
  exact I.
Qed.

(* P6F.v imports image-A's YK11 before its ro stretches (P6F.v:214-217), so P6F.p6_evt_ro_pre_F's seg_rom is that
   YK11's.  This file names it through a full-path alias instead (no short name of the six twin modules), so the ro
   statement below is P6F.p6_evt_ro_pre_F's term; the constr_eq pin checks it. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

(* ---- a Theorem Labs lane's p6_evt_ro_pre_F (P6F.v:222-251), verbatim, from the minimal stretch ---- *)

Lemma p6_evt_ro_pre_F_of_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S FS pa pp : Z),
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 S ->
    0 <= S < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 ->
    bytes_at rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) ->
    bytes_at rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) ->
    S mod 16 = 0 -> REAC_CTRL_IDENTITY_REPLY_K <= S ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
       [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    ExecF.rng RNG (A + 232) 8 ->
    ExecF.rng RNG (A + 224) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81bf8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0)
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) s4 a5 a6 a7 s2 s3 s4 s5 s6
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (AYK.seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81bd8) fc None m (AYK.seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S FS pa pp E1 _ _ _ _ H232 H224 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R232 R224.
  exact (p6_evt_pre_Fs RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A pa pp E1 H232 H224 R232 R224).
Qed.

(* The pin: p6_evt_ro_pre_F_of_Fs states P6F.p6_evt_ro_pre_F's text, term for term. *)
Example p6_evt_ro_pre_F_of_Fs_verbatim : True.
Proof.
  let a := type of P6F.p6_evt_ro_pre_F in let b := type of p6_evt_ro_pre_F_of_Fs in constr_eq a b.
  exact I.
Qed.
