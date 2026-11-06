(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs (for the cf layer at plugin-hostd/fuzz_reply; row img-oomowned-A).
   rule 24: no function proved (kind: image row; a closed computation over reply image A's symbol table, fuzz_reply.asan,
   pin 42c58610e125).

   oom_owned_img at image A.  The cf layer states the fact as `Hypothesis oom_owned_img : oom_areas_t`
   (proofs/cgif/cgif_file_fuzzer/lib/YGcfInstMiss.v:300 @ 692f71ce28c), with oom_areas_t the Definition at
   YGcfInstMiss.v:291-296 (same commit) over the Section variable B.  The reply tree does not carry that layer file, so
   the Lemma below states oom_areas_t's body VERBATIM, at any B with the image's symbol facts (ImgBase.im_syms at
   AImg_reply, proofs/plugin-hostd/fuzz_reply/lib/A/AGif2reply.v:27 @ d2bd679271c, = lib/A/AF0m.v's TfibSyms).
   The addresses (proofs/plugin-hostd/fuzz_reply/lib/A/AF0m.v:17-20 @ d2bd679271c): the OOM byte TFIB_OOM = 0x128320;
   the instance object [0xa2a58, 0xa3888); the depot from 0x187f98; the store [0x177f88, 0x177fa8); the internal
   allocator [0xa72c0, 0x1282f0); its flag [0x135b48, 0x135b4a).  cgif's discharge pattern: YFi5's Z_inst / Z_depot /
   Z_store / Z_ial / Z_flag (proofs/cgif/cgif_file_fuzzer/lib/YFi5.v). *)
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

(* oom_owned_img at image A: YGcfInstMiss.v:291-296 (oom_areas_t's body), commit 692f71ce28c. *)
Lemma oom_owned_img_A : forall B, @im_syms AImg_reply B ->
  ~ (as_inst B <= as_oom_byte B < as_inst B + 3632) /\
  ~ (as_depot B <= as_oom_byte B < as_depot B + (4 * 2 ^ 20 + 32)) /\
  ~ (as_store B <= as_oom_byte B < as_store B + 32) /\
  ~ (as_ialloc_lo B <= as_oom_byte B < as_ialloc_hi B) /\
  ~ (as_ialloc_flag B <= as_oom_byte B < as_ialloc_flag B + 2).
Proof.
intros B TS. change (TfibSyms B) in TS.
rewrite (ts_oom B TS), (ts_inst B TS), (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS), (ts_ial_hi B TS),
  (ts_ial_flag B TS).
replace (2 ^ 20) with 1048576 by reflexivity.
unfold TFIB_OOM, TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
Qed.
