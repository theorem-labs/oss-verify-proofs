(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 17 of its 34 lines of code are new or changed and 994 lines of the source are left out. *)
(* Segment R1 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the our[] loop body from
   the body cut 0x81550 (the head 0x81548 fell through on left <> 0 and 0x8154c bumped the cursor), Inv_B81550 ->
   Inv_B815fc (R2) / Inv_B81cb0 (P3), all three SlotInv.v's official cuts.
   rule 24: no function proved (a slot segment).  One turn from 0x81550 is lib/B/Prog/Seg/A5.v's b_turn_gen at
   pc0 = 0x81550: T01 at 0x81554 (trap 0x82fa0 not taken), the cursor's shadow check 0x81560 (error call 0x8159c
   not reached), the byte copy our[t] = in[t] and the latch 0x8158c back to the head of turn t + 1, or after turn 5
   the loop exit 0x815a0 and its tail to P3 or, through the catalogue call 0x815f8, to R2.  The back edge is closed
   by A5.v's b_loop (the loop's head turns, proved by induction in that file), so R1 does not assume the head
   cut. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import A5.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Import ListNotations.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module RBC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_box_catalogue_c.

Section R1.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CATC : RBC.reac_box_catalogue_contract.

(* S_R1 (forms-asan-ubsan.md), on SlotInv.v's official cuts. *)
Lemma seg_R1 : Hcut B APIf ra (Inv_B815fc B APIf ra) -> Hcut B APIf ra (Inv_B81cb0 B APIf ra) -> Hcut B APIf ra (Inv_B81550 B APIf ra).
Proof.
  intros HR2 HP3 g c (t & regs & mem & md & fr & sel & Ec & HF & HE & HB & HP & Hlt & H13).
  eapply b_turn_gen; [exact FF | exact CATC | | exact HP3 | exact HR2 |].
  - intros _. eapply b_loop; [exact FF | exact CATC | exact HP3 | exact HR2].
  - exists regs, mem, md, fr, sel. split; [exact Ec|]. split; [exact HF|]. split; [exact HE|].
    split; [exact HB|].
    split; [exact HP | right; split; [reflexivity | split; [exact Hlt | exact H13]]].
Qed.

End R1.
