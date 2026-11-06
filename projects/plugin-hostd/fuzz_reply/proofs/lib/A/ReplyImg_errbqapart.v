(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs (for the cf layer at plugin-hostd/fuzz_reply; row img-errbqapart-A).
   rule 24: no function proved (kind: image row; a closed computation over reply image A's symbol table and image
   constants, fuzz_reply.asan, pin 42c58610e125).

   ERRB_QAPART at image A.  The cf layer's Definition ERRB_QAPART
   (proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainX.v:77-78 @ 8b12df2b772) is stated over the image class and the image
   constants under [Context {ci : CfImg} {IM : AImg}].  The reply tree does not carry that layer file, so the Lemma below
   states ERRB_QAPART's body VERBATIM at reply's instances IM := AImg_reply
   (proofs/plugin-hostd/fuzz_reply/lib/A/AGif2reply.v:23 @ d2bd679271c, im_syms := lib/A/AF0m.v's TfibSyms) and
   ci := CfImg_A (proofs/plugin-hostd/fuzz_reply/lib/A/CfImgA.v:9 @ d2bd679271c).
   cf_errbuf_obj is the CfImg field (proofs/plugin-hostd/fuzz_reply/lib/Reusable/YGcfNames.v:52 @ d2bd679271c); at
   CfImg_A it is 0xa5928 (lib/A/CfImgA.v:34, same commit), the symtab value of _ZN6__asanL20error_message_bufferE in the
   unstripped ELF (sha256 d751b179ea49), whose 56 bytes are error_message_buffer 0xa5928 (8), error_report_callback
   0xa5930 (8), error_message_buf_mutex 0xa5938 (16), error_message_buffer_placeholder 0xa5948 (24).
   The object [0xa5928, 0xa5960) lies above the instance object [TFIB_INST, TFIB_INST + 3632) = [0xa2a58, 0xa3888)
   (proofs/plugin-hostd/fuzz_reply/lib/A/AF0m.v:17 @ d2bd679271c). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA.
Open Scope Z_scope.

(* ERRB_QAPART at image A: proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainX.v:77-78 @ 8b12df2b772. *)
Lemma ERRB_QAPART_A : forall B, @im_syms AImg_reply B ->
  forall a, @cf_errbuf_obj CfImg_A <= a < @cf_errbuf_obj CfImg_A + 56 -> ~ (as_inst B <= a < as_inst B + 3632).
Proof.
intros B TS a Ha. change (TfibSyms B) in TS. rewrite (ts_inst B TS).
unfold CfImg_A in Ha. cbn [cf_errbuf_obj] in Ha. unfold TFIB_INST. lia.
Qed.
