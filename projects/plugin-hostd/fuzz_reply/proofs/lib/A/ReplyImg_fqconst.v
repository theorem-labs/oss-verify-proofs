(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs (for the cf layer at plugin-hostd/fuzz_reply; row img-fqconst-A).
   rule 24: no function proved (kind: image row; a closed computation over reply image A's constant-cell table,
   fuzz_reply.asan, pin 42c58610e125).

   FQ_CONST at image A.  The cf layer's Definition FQ_CONST
   (proofs/cgif/cgif_file_fuzzer/lib/YGcfInstFreeView.v:56-58 @ 587da63d252) is stated with const_at (the same file,
   :54-55):
     const_at ly a w v := exists e, In (ACell e w (AV (ANum v))) (as_const B ly) /\ aeval B ly e = a.
   The reply tree does not carry that layer file, so the Lemma below states FQ_CONST's body with const_at UNFOLDED, at
   any B with the image's symbol facts (ImgBase.im_syms at AImg_reply, proofs/plugin-hostd/fuzz_reply/lib/A/AGif2reply.v:27
   @ d2bd679271c, = lib/A/AF0m.v's TfibSyms).  The four cells are found by a scan of the table Tfib_const
   (proofs/plugin-hostd/fuzz_reply/lib/A/AF0m.v:817 @ d2bd679271c; ImgBase.cell_lookup, vm_compute) at the instance
   TFIB_INST = 0xa2a58 (lib/A/AF0m.v:17) plus o_q_max / o_q_maxcache / o_q_min / o_q_cmutex + 2
   (proofs/plugin-hostd/fuzz_reply/lib/Reusable/YG0f.v:209-212 @ d2bd679271c); the values are kQuarantineMax /
   kQuarantineCacheMax / kQuarantineMin (lib/Reusable/YG00.v:28-30, same commit).  cgif's discharge pattern:
   tfib_const_lookup (proofs/cgif/cgif_file_fuzzer/lib/YF0x.v:206); FQ_CONST_cgif
   (proofs/cgif/cgif_file_fuzzer/lib/YGcfInstFreeImgcgif.v:87 @ 672df6005e4). *)
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

(* FQ_CONST at image A: YGcfInstFreeView.v:56-58 with const_at (:54-55) unfolded, commit 587da63d252. *)
Lemma FQ_CONST_A : forall B, @im_syms AImg_reply B ->
  forall ly,
  (exists e, In (ACell e 8 (AV (ANum kQuarantineMax))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_max) /\
  (exists e, In (ACell e 8 (AV (ANum kQuarantineCacheMax))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_maxcache) /\
  (exists e, In (ACell e 8 (AV (ANum kQuarantineMin))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_min) /\
  (exists e, In (ACell e 2 (AV (ANum 0))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_cmutex + 2).
Proof.
intros B TS ly. change (TfibSyms B) in TS. rewrite (ts_const B TS ly), (ts_inst B TS).
split; [|split; [|split]].
- exists (ANum (TFIB_INST + o_q_max)). split; [|reflexivity].
  apply (cell_lookup_In _ (ANum (TFIB_INST + o_q_max))). vm_compute. reflexivity.
- exists (ANum (TFIB_INST + o_q_maxcache)). split; [|reflexivity].
  apply (cell_lookup_In _ (ANum (TFIB_INST + o_q_maxcache))). vm_compute. reflexivity.
- exists (ANum (TFIB_INST + o_q_min)). split; [|reflexivity].
  apply (cell_lookup_In _ (ANum (TFIB_INST + o_q_min))). vm_compute. reflexivity.
- exists (ANum (TFIB_INST + o_q_cmutex + 2)). split; [|reflexivity].
  apply (cell_lookup_In _ (ANum (TFIB_INST + o_q_cmutex + 2))). vm_compute. reflexivity.
Qed.
