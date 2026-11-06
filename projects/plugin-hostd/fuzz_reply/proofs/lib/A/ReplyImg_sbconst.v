(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs (for the cf layer at plugin-hostd/fuzz_reply; row img-sbconst-A).
   rule 24: no function proved (kind: image row; a closed computation over reply image A's constant-cell table,
   fuzz_reply.asan, pin 42c58610e125).

   SB_CONST at image A.  The cf layer's Definition SB_CONST (proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainQ.v:45
   @ 1c81ef042c9; the premise SBC at :154) is stated over the image class's im_const under [Context {IM : AImg}].  The
   reply tree does not carry that layer file, so the Lemma below states SB_CONST's body VERBATIM at reply's instance
   IM := AImg_reply (proofs/plugin-hostd/fuzz_reply/lib/A/AGif2reply.v:23 @ d2bd679271c, im_const := lib/A/AF0m.v:817
   Tfib_const).  The cell c8 (AInst o_space) (ASp 0) is found by a scan of that table (ImgBase.cell_lookup, vm_compute).
   cgif's discharge pattern: YFhl.sb_cell (at reply: proofs/plugin-hostd/fuzz_reply/lib/A/AFhl.v:122-126 @ d2bd679271c). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
Open Scope Z_scope.

(* SB_CONST at image A: YGcfInstDrainQ.v:45, commit 1c81ef042c9. *)
Lemma SB_CONST_A : forall ly, In (ACell (AInst o_space) 8 (AV (ASp 0))) (@im_const AImg_reply ly).
Proof.
intros ly. apply (cell_lookup_In _ (AInst o_space)). vm_compute. reflexivity.
Qed.
