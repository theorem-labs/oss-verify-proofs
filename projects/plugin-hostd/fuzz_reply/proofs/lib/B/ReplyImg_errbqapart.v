(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs: reply image row ERRB_QAPART at image B of the cf layer at plugin-hostd/fuzz_reply.
   rule 24: no function proved (kind: closed image fact over the symbol table and the CfImg constants of reply's
   image B, fuzz_reply.asan-ubsan, pin 10ffb5f9202a).

   ERRB_QAPART, proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainX.v:77-78 @ 8b12df2b772, over the image classes
   (Context {ci : CfImg} {IM : AImg}, YGcfInstDrainX.v:57 @ 8b12df2b772).  Reply does not carry YGcfInstDrainX.v, so the
   Lemma states ERRB_QAPART's body VERBATIM at reply's instances IM := AImg_reply (B/AGif2reply.v:24,
   im_syms := YF0m.TfibSyms) and ci := CfImg_B (B/CfImgB.v:12).
   At image B: cf_errbuf_obj = 0xa5ea8 (B/CfImgB.v:34), the symtab value of _ZN6__asanL20error_message_bufferE in the
   unstripped twin (sha256 3389287e1d61), so the buffer's object is [0xa5ea8, 0xa5ee0); the instance object is
   [TFIB_INST, TFIB_INST + 3632) = [0xa2fd8, 0xa3e08) (B/YF0m.v:16, ts_inst): the object lies above the instance. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply CfImgB.
Open Scope Z_scope.

(* ERRB_QAPART at image B: YGcfInstDrainX.v:77-78 @ 8b12df2b772, at IM := AImg_reply, ci := CfImg_B. *)
Lemma ERRB_QAPART_B : forall B, @im_syms AImg_reply B -> forall a,
  @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 -> ~ (as_inst B <= a < as_inst B + 3632).
Proof.
intros B TS a Ha. change (TfibSyms B) in TS.
rewrite (ts_inst B TS).
change (@cf_errbuf_obj CfImg_B) with 0xa5ea8 in Ha.
unfold TFIB_INST. lia.
Qed.
