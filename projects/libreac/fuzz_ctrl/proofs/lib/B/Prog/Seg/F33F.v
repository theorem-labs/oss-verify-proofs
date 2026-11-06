(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, module names and addresses changed; 105 of its 141 lines of code are new or changed and 360 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F33.v, with its numbers changed; 73 of its 116 lines of code are new or changed and 98 lines of the source are left out. *)
(* Footprint (ExecF.evtF) twin of the segment-F33 machine run of lib/B/Prog/Seg/F33.v (fuzz_ctrl
   LLVMFuzzerTestOneInput, asan-ubsan image B). Bridge input for the cgif-form walk only.
   rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F33.v f33_evt at a working branch 3803efccea0
     (blob 333b7b7d6414e90ea5d52104f814ff481f51d2a2);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f33_evt_of_F_bounded re-derives the source statement (the UL-engine `evt` of lib.B.Tk.UL.Exec) under
     two added address bounds on the count pointer c, through f33_evtF_ulevt (mstepF_step into the UL engine's
     mstep, the two step relations being the same RiscvSemantics.step) and rng_all; shape check
     f33_evt_of_F_bounded_shape (its hypothesis is F33.f33_evt's exact type). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro F33.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module ULE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Mem.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

(* The start register map of sl_run, written with lib.Lib's mkR so the lib.Lib StepF engine reads it
   (F33.v:56-64 writes the same identity with the UL engine's mkR). *)
Lemma f33F_mkR_of : forall regs, Regs6ss.mkR_of regs =
  LFrame.mkR (Sem.reg_get regs 1) (Sem.reg_get regs 2) (Sem.reg_get regs 3) (Sem.reg_get regs 4)
      (Sem.reg_get regs 5) (Sem.reg_get regs 6) (Sem.reg_get regs 7) (Sem.reg_get regs 8) (Sem.reg_get regs 9)
      (Sem.reg_get regs 10) (Sem.reg_get regs 11) (Sem.reg_get regs 12) (Sem.reg_get regs 13)
      (Sem.reg_get regs 14) (Sem.reg_get regs 15) (Sem.reg_get regs 16) (Sem.reg_get regs 17)
      (Sem.reg_get regs 18) (Sem.reg_get regs 19) (Sem.reg_get regs 20) (Sem.reg_get regs 21)
      (Sem.reg_get regs 22) (Sem.reg_get regs 23) (Sem.reg_get regs 24) (Sem.reg_get regs 25)
      (Sem.reg_get regs 26) (Sem.reg_get regs 27) (Sem.reg_get regs 28) (Sem.reg_get regs 29)
      (Sem.reg_get regs 30) (Sem.reg_get regs 31).
Proof. intros regs. reflexivity. Qed.

(* The UL engine's evt and lib.Lib's evtF run the same RiscvSemantics.step, so an evtF of this file gives the
   UL-engine evt that F33.seg_F33 feeds to sl_run. *)
Lemma f33_mstepsF_ul : forall (RNG : footprint) ms ms',
  mstepsF rsegs RNG ms ms' -> ULE.msteps rsegs ms ms'.
Proof.
  intros RNG ms ms' H. induction H as [ms0|ms0 ms1 ms2 ST _ IH].
  - apply ULE.msteps_refl.
  - eapply ULE.msteps_cons; [|exact IH].
    split; [exact (proj1 ST) | exact (mstepF_step rsegs RNG ms0 ms1 ST)].
Qed.

Lemma f33_evtF_ulevt : forall (RNG : footprint) (Q : machine_state -> Prop) ms,
  evtF rsegs RNG Q ms -> ULE.evt rsegs Q ms.
Proof.
  intros RNG Q ms (ms' & H & HQ). exists ms'.
  split; [exact (f33_mstepsF_ul RNG ms ms' H) | exact HQ].
Qed.

(* 0x82bcc -> 0x82bf4 with a0 = 0x9f620 and the 8 bytes at s7 = c holding 11 (F33.v:69-98): both branches to
   0x82c84 fall through. The run reads the 8 bytes [c, c + 8) and writes no memory. *)
Lemma f33_evt_F : forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z)
    (RNG : footprint),
  getr regs 10 = Z_to_bv 64 0x9f620 -> getr regs 23 = Z_to_bv 64 c ->
  ov_read_bytes rsegs m (Z_to_bv 64 c) 8 = Some (ULMem.le8 (Z_to_bv 64 11)) ->
  rng RNG c 8 ->
  evtF rsegs RNG (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x82bf4) fc None m (seg_rom rsegs) /\
      getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
      getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
      getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
      getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
      getr R 10 = Z_to_bv 64 0 /\ getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 0 /\
      getr R 21 = Z_to_bv 64 0x9f620 /\ getr R 23 = Z_to_bv 64 0x9f620 /\ getr R 25 = Z_to_bv 64 0)
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x82bcc) fc None m (seg_rom rsegs)).
Proof.
  intros regs F fc m c RNG E10 E23 RD Rc.
  rewrite f33F_mkR_of.
  assert (E : Sem.reg_get regs 10 = Z_to_bv 64 0x9f620) by exact E10.
  assert (E' : Sem.reg_get regs 23 = Z_to_bv 64 c) by exact E23.
  rewrite E, E'.
  (* 0x82bcc beqz a0,82c84: a0 = 0x9f620, not taken *)
  step. if_false.
  (* 0x82bd0 mv s5,a0 *)
  step.
  (* 0x82bd4 ld a0,0(s7): the count 11 *)
  step.
  (* 0x82bd8 beqz a0,82c84: a0 = 11, not taken *)
  step. if_false.
  (* 0x82bdc li s9,0; 0x82be0 mv s7,s5; 0x82be4 li a0,296; 0x82be8 mulh; 0x82bec mul; 0x82bf0 srai *)
  do 6 step.
  finish.
  all: reflexivity.
Qed.

(* The source statement of F33.v:69-98 under the two address-range side conditions that rng_all needs: the source
   does not bound the count pointer c, read by `ld a0,0(s7)` at pc 0x82bd4. NOT the source statement verbatim:
   hence the `_bounded` name. *)
Lemma f33_evt_of_F_bounded : forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z),
  0 <= c -> c + 8 <= 2 ^ 64 ->
  getr regs 10 = Z_to_bv 64 0x9f620 -> getr regs 23 = Z_to_bv 64 c ->
  ov_read_bytes rsegs m (Z_to_bv 64 c) 8 = Some (ULMem.le8 (Z_to_bv 64 11)) ->
  ULE.evt rsegs (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x82bf4) fc None m (seg_rom rsegs) /\
      getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
      getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
      getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
      getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
      getr R 10 = Z_to_bv 64 0 /\ getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 0 /\
      getr R 21 = Z_to_bv 64 0x9f620 /\ getr R 23 = Z_to_bv 64 0x9f620 /\ getr R 25 = Z_to_bv 64 0)
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x82bcc) fc None m (seg_rom rsegs)).
Proof.
  intros regs F fc m c B1 B2 E10 E23 RD.
  apply (f33_evtF_ulevt RNG_all).
  apply (f33_evt_F regs F fc m c RNG_all E10 E23 RD).
  apply rng_all; lia.
Qed.

(* The auditor's shape check: the hypothesis is the statement of F33.f33_evt (feed the source lemma to it to
   discharge the hypothesis), so the added bounds are the only difference and the shape is machine-checked. *)
Lemma f33_evt_of_F_bounded_shape :
  (forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z),
     getr regs 10 = Z_to_bv 64 0x9f620 -> getr regs 23 = Z_to_bv 64 c ->
     ov_read_bytes rsegs m (Z_to_bv 64 c) 8 = Some (ULMem.le8 (Z_to_bv 64 11)) ->
     ULE.evt rsegs (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x82bf4) fc None m (seg_rom rsegs) /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
         getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
         getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
         getr R 10 = Z_to_bv 64 0 /\ getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 0 /\
         getr R 21 = Z_to_bv 64 0x9f620 /\ getr R 23 = Z_to_bv 64 0x9f620 /\ getr R 25 = Z_to_bv 64 0)
       (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x82bcc) fc None m (seg_rom rsegs))) ->
  (forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z),
     0 <= c -> c + 8 <= 2 ^ 64 ->
     getr regs 10 = Z_to_bv 64 0x9f620 -> getr regs 23 = Z_to_bv 64 c ->
     ov_read_bytes rsegs m (Z_to_bv 64 c) 8 = Some (ULMem.le8 (Z_to_bv 64 11)) ->
     ULE.evt rsegs (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x82bf4) fc None m (seg_rom rsegs) /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
         getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
         getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
         getr R 10 = Z_to_bv 64 0 /\ getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 0 /\
         getr R 21 = Z_to_bv 64 0x9f620 /\ getr R 23 = Z_to_bv 64 0x9f620 /\ getr R 25 = Z_to_bv 64 0)
       (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x82bcc) fc None m (seg_rom rsegs))).
Proof. intros H regs F fc m c B1 B2 E10 E23 RD. eapply H; eassumption. Qed.
