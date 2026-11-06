(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 83 of its 123 lines of code are new or changed and 971 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/A2.v a2_side_evt (:112), a2_real_evt (:132) at a working branch
     3803efccea0 (blob 7b0b4a7cd96707f4045cd51f0ac27f6d5e681a3c);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: a2_side_evt_of_F / a2_real_evt_of_F (evtF_evt + rng_all) re-derive the source statements in the
     lib.Lib vocabulary; a2_side_evt_of_F_is_source / a2_real_evt_of_F_is_source (the types of A2.a2_side_evt
     and A2.a2_real_evt, re-derived from them through the UL engine bridge ul_evt_of_evt) are the source
     statements themselves.  The source states them on the UL engine (lib/B/Tk/UL/Exec.v) with the UL copies
     of MS / mkR / getr / seg_rom; every _F here is on the lib.Lib engine.  The two copies are the same
     definitions (UL's MS is the same record, UL's mkR the same tree through #[local] Abbreviations, UL's
     getr / seg_rom the same bodies), and the two [mstep]s are the same definition, so ul_evt_of_evt takes a
     lib.Lib evt to the UL evt the source states.  Neither run has a cell premise or a cell in its post, so
     the shared cell bridge lib/B/Tk/UL/CellBridge.v (Module CBR) is needed for neither. *)
(* rule 24: no function proved. *)
(* Segment A2 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B): the footprint twins of the frame-arm
   selection 0x81090 .. 0x810c4.  Neither run calls anything, so each gets one `_F` (no _pre/_post split).
   a2_side_evt touches no memory at all: it has no rng premise.
   a2_real_evt makes exactly one access, the probe store of 8 bytes at A - 4096. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require A2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Exec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

(* A2.v's a2_mkR_of over the lib.Lib mkR (the same tree): the start register map written so the engine reads it. *)
Lemma a2f_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* The side-stack arm 0x81090 .. 0x810a0 (bnez s8 taken): four register instructions, no memory access. *)
Lemma a2_side_evt_F : forall (RNG : footprint) (regs F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (r : Z),
  getr regs 10 = Z_to_bv 64 r -> r mod 2 ^ 64 <> 0 ->
  evtF rsegs RNG (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x810c4) fc None m (seg_rom rsegs) /\
      getr R 25 = Z_to_bv 64 r /\ getr R 24 = Z_to_bv 64 r /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
      getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 26 = getr regs 26 /\
      getr R 22 = getr regs 22 /\ getr R 18 = getr regs 18)
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x81090) fc None m (seg_rom rsegs)).
Proof.
  intros RNG regs F fc m r E10 Hr.
  rewrite a2f_mkR_of, E10.
  do 4 step.
  if_true_by (A2.a2_c1 r Hr).
  finish.
  all: reflexivity.
Qed.

(* The real-stack arm 0x81090 .. 0x810c0 (bnez s8 not taken): the one probe store of 8 bytes at A - 4096. *)
Lemma a2_real_evt_F : forall (RNG : footprint) (regs F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (r A : Z),
  getr regs 10 = Z_to_bv 64 r -> r mod 2 ^ 64 = 0 ->
  getr regs 2 = Z_to_bv 64 A -> 4096 <= A < 2 ^ 63 -> A mod 32 = 0 ->
  store_ok rsegs m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 A) - 4096)) 8 = true ->
  rng RNG (A - 4096) 8 ->
  evtF rsegs RNG (fun ms' => exists R bs, ms' = MS R F (Z_to_bv 64 0x810c4) fc None
         (write_to_mem m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 A) - 4096)) bs) (seg_rom rsegs) /\
      length bs = 8%nat /\
      getr R 25 = Z_to_bv 64 (A - 3136) /\ getr R 2 = Z_to_bv 64 (A - 3136) /\ getr R 24 = Z_to_bv 64 r /\
      getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
      getr R 26 = getr regs 26 /\ getr R 22 = getr regs 22 /\ getr R 18 = getr regs 18)
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x81090) fc None m (seg_rom rsegs)).
Proof.
  intros RNG regs F fc m r A E10 Hr E2 HA HAm HS RP.
  assert (RP' : rng RNG (bv_unsigned (Z_to_bv 64 A) - 4096) 8)
    by (rewrite MState.unsigned_lit by lia; exact RP).
  rewrite a2f_mkR_of, E10, E2.
  do 4 step.
  if_false_by (A2.a2_c0 r Hr).
  do 7 step.
  if_false_by (A2.a2_blt A HA HAm).
  step.
  finish.
  all: first [reflexivity | exact (A2.a2_s9 A HA HAm)].
Qed.

(* The compare lemmas (the auditor's check): the source statements, on the lib.Lib engine, re-derived from the
   twins at RNG := RNG_all with evtF_evt and rng_all. *)
Lemma a2_side_evt_of_F : forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
  getr regs 10 = Z_to_bv 64 r -> r mod 2 ^ 64 <> 0 ->
  evt rsegs (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x810c4) fc None m (seg_rom rsegs) /\
      getr R 25 = Z_to_bv 64 r /\ getr R 24 = Z_to_bv 64 r /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
      getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 26 = getr regs 26 /\
      getr R 22 = getr regs 22 /\ getr R 18 = getr regs 18)
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x81090) fc None m (seg_rom rsegs)).
Proof.
  intros regs F fc m r E10 Hr.
  exact (evtF_evt rsegs RNG_all _ _ (a2_side_evt_F RNG_all regs F fc m r E10 Hr)).
Qed.

Lemma a2_real_evt_of_F : forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r A : Z),
  getr regs 10 = Z_to_bv 64 r -> r mod 2 ^ 64 = 0 ->
  getr regs 2 = Z_to_bv 64 A -> 4096 <= A < 2 ^ 63 -> A mod 32 = 0 ->
  store_ok rsegs m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 A) - 4096)) 8 = true ->
  evt rsegs (fun ms' => exists R bs, ms' = MS R F (Z_to_bv 64 0x810c4) fc None
         (write_to_mem m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 A) - 4096)) bs) (seg_rom rsegs) /\
      length bs = 8%nat /\
      getr R 25 = Z_to_bv 64 (A - 3136) /\ getr R 2 = Z_to_bv 64 (A - 3136) /\ getr R 24 = Z_to_bv 64 r /\
      getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
      getr R 26 = getr regs 26 /\ getr R 22 = getr regs 22 /\ getr R 18 = getr regs 18)
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x81090) fc None m (seg_rom rsegs)).
Proof.
  intros regs F fc m r A E10 Hr E2 HA HAm HS.
  apply (evtF_evt rsegs RNG_all).
  apply (a2_real_evt_F RNG_all regs F fc m r A E10 Hr E2 HA HAm HS).
  apply rng_all; lia.
Qed.

(* ---- the UL bridge: the source statements A2.a2_side_evt / A2.a2_real_evt themselves ----
   Everything in the two source statements is the same definition in the two copies (MS, mkR, getr,
   seg_rom, write_to_mem, store_ok, mstep: identical bodies, so convertible); neither run names a cell,
   so the shared cell bridge lib/B/Tk/UL/CellBridge.v (Module CBR, Required above as A4F.v / R5F.v do)
   carries nothing here.  The engine bridge is the one A4F.v and R5F.v use, copied locally: the UL
   [mstep] and the lib.Lib [mstep] are the same definition. *)
Module ULE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.

Lemma ul_msteps_of_msteps : forall ms ms', msteps rsegs ms ms' -> ULE.msteps rsegs ms ms'.
Proof.
  intros ms ms' H.
  induction H as [ms0|ms0 ms1 ms2 Hst Hs IH]; [apply ULE.msteps_refl|].
  eapply ULE.msteps_cons; [|exact IH]. destruct Hst as [HA HB]. split; [exact HA | exact HB].
Qed.

Lemma ul_evt_of_evt : forall (Q : machine_state -> Prop) ms, evt rsegs Q ms -> ULE.evt rsegs Q ms.
Proof.
  intros Q ms (ms1 & H & HQ). exists ms1. split; [exact (ul_msteps_of_msteps _ _ H) | exact HQ].
Qed.

(* The source statement itself: the type is A2.a2_side_evt's, taken from A2.a2_side_evt. *)
Lemma a2_side_evt_of_F_is_source : ltac:(let T := type of A2.a2_side_evt in exact T).
Proof.
  intros regs F fc m r E10 Hr.
  apply ul_evt_of_evt.
  eapply evt_mono.
  - exact (a2_side_evt_of_F regs F fc m r E10 Hr).
  - intros ms' HQ. exact HQ.
Qed.

(* The source statement itself: the type is A2.a2_real_evt's, taken from A2.a2_real_evt. *)
Lemma a2_real_evt_of_F_is_source : ltac:(let T := type of A2.a2_real_evt in exact T).
Proof.
  intros regs F fc m r A E10 Hr E2 HA HAm HS.
  apply ul_evt_of_evt.
  eapply evt_mono.
  - exact (a2_real_evt_of_F regs F fc m r A E10 Hr E2 HA HAm HS).
  - intros ms' HQ. exact HQ.
Qed.
