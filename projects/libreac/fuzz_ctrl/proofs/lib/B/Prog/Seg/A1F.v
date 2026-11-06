(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 1011 of its 1078 lines of code are new or changed and 944 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A1.v, with its module paths and module names changed; 39 of its 98 lines of code are new or changed and 1019 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/A1.v a1_pro (:397) at a working branch 3803efccea0
     (blob a5ac94f98c13e3eef47859eefeca4c1992c84221);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: a1_pro_of_F (evtF_evt + rng_all) re-derives the source statement verbatim. *)
(* rule 24: no function proved. *)
(* Segment A1 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B): the footprint twin of the prologue run
   0x81018 .. the frame-request entry 0x3db94.  a1_pro already stops AT the callee entry (pc = 0x3db94,
   ra = 0x81090), so it is a `_pre` stretch by itself and needs no further split; it steps through no callee.
   Its accesses are the 13 caller registers spilled into [sp - 104, sp) and the four runtime cells it reads
   (GOT_CELL_K -> CELL_K for the shadow offset ASAN_K, GOT_UAR -> UAR for the switch word D). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_fsfree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ClassConsDef.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require A1.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Lemma a1_pro_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo + 1048576 <= bv_unsigned sp -> mem_inv rsegs m ->
  bv_unsigned sp < 2 ^ 47 -> asan_cells m ->
  rng RNG (bv_unsigned sp - 448) 8 -> rng RNG (bv_unsigned sp - 104) 104 ->
  rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 -> rng RNG GOT_UAR 8 -> rng RNG UAR 4 ->
  evtF rsegs RNG
    (fun ms' => exists (ra' sp' a0' a1' a2' s10' : word) (m' : word -> option byte),
       ms' = MS (mkR ra' sp' gp tp t0 t1 t2 sp sp' a0' a1' a2' a3 a4 a5 a6 a7 a1 s3 s4 s5 a0 s7 s8 s9 s10' s11
                     t3 t4 t5 t6) F (Z_to_bv 64 0x3db94) fc None m' (seg_rom rsegs) /\
       ra' = Z_to_bv 64 0x81090 /\
       bv_unsigned sp' = (bv_unsigned sp - 448) - (bv_unsigned sp - 448) mod 32 /\
       bv_unsigned a0' = 3136 /\ s10' = Z_to_bv 64 ASAN_K /\
       munch [(bv_unsigned sp - 448, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       stk rsegs m' lo (bv_unsigned sp) /\
       bytes_at rsegs m' (bv_unsigned sp - 104)
         (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++
          le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81018) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST HLO LO MI HSP HAC RZ RSTK RGCK RCK RGUAR RUAR.
  destruct HAC as (HCK & HGCK & _ & _ & _ & HUAR & HGUAR & _).
  unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR, ASAN_K in *.
  apply A1.ro8l in HCK, HGCK, HGUAR. apply A1.ro4l in HUAR.
  pose proof (munch_refl [(bv_unsigned sp - 448, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  carve_frame 448%nat ST.
  do 27 step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false by (vm_compute; reflexivity) end.
  cbv iota.
  do 3 step.
  pose proof (A1.a1_tail2 _ _ _ _ _ _ FR) as SB.
  cbn [cells_bytes cbytes] in SB. rewrite app_nil_r in SB.
  replace (bv_unsigned sp + -448 + 8 + Z.of_nat 336) with (bv_unsigned sp - 104) in SB by lia.
  release_frame FR ST (bv_unsigned sp).
  finish.
  all: try reflexivity.
  all: try assumption.
  rewrite (unsigned_lit (bv_unsigned sp + -448)) by lia.
  rewrite A1.a1_land32 by lia.
  rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned sp + -448) 32 ltac:(lia)); lia).
  reflexivity.
Qed.

(* The compare lemma (the auditor's check): the source statement of a1_pro, verbatim, re-derived from the twin at
   RNG := RNG_all with evtF_evt and every rng premise by rng_all. *)
Lemma a1_pro_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo + 1048576 <= bv_unsigned sp -> mem_inv rsegs m ->
  bv_unsigned sp < 2 ^ 47 -> asan_cells m ->
  evt rsegs
    (fun ms' => exists (ra' sp' a0' a1' a2' s10' : word) (m' : word -> option byte),
       ms' = MS (mkR ra' sp' gp tp t0 t1 t2 sp sp' a0' a1' a2' a3 a4 a5 a6 a7 a1 s3 s4 s5 a0 s7 s8 s9 s10' s11
                     t3 t4 t5 t6) F (Z_to_bv 64 0x3db94) fc None m' (seg_rom rsegs) /\
       ra' = Z_to_bv 64 0x81090 /\
       bv_unsigned sp' = (bv_unsigned sp - 448) - (bv_unsigned sp - 448) mod 32 /\
       bv_unsigned a0' = 3136 /\ s10' = Z_to_bv 64 ASAN_K /\
       munch [(bv_unsigned sp - 448, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       stk rsegs m' lo (bv_unsigned sp) /\
       bytes_at rsegs m' (bv_unsigned sp - 104)
         (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++
          le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81018) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST HLO LO MI HSP HAC.
  apply (evtF_evt rsegs RNG_all).
  apply (a1_pro_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m lo ST HLO LO MI HSP HAC);
    apply rng_all; unfold GOT_CELL_K, CELL_K, GOT_UAR, UAR; lia.
Qed.
Definition a1_pro_src_check : ltac:(let T := type of A1.a1_pro in exact T) := a1_pro_of_F.
