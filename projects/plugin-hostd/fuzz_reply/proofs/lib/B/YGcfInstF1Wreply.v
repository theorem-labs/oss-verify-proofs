(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstF1Wreply.v at commit f303438be5b, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane W, ReallocPrimary.CfW.ReplyEnqReloc): reply's own twin, at image B
   (fuzz_reply.asan-ubsan), of CfF1's cgif instance file proofs/cgif/cgif_file_fuzzer/lib/YGcfInstF1Wcgif.v (commit
   a8ad57cefdcd, sha256 e299071e9ebb; internal record), CUT to the one image fact the relocated Enqueue room arm (B/YFg4cf.v) reads:
   [IMG_COVER_reply], the kit's image premise YGcfDIface.IMG_COVER.  The cgif file's other witnesses (errno_img_cf,
   the depot premises, depot_spec, enq_pre_state_init_cf) are not taken: no file here uses them, and reply's image rows
   for them are other hands' (REPLY-IMG-ROWS.md sha256 a33a582e3ffd; internal record).
   The proof is the cgif lemma's own script (YGcfInstF1Wcgif.v:67-74 at a8ad57cefdcd), which is reply's
   B/YF0x.v:55-62 img_cover_of_ledger over ALedger_cf: image B's first and last loaded segments (AsanUbsan_segment_000,
   AsanUbsan_segment_003) give TFIB_IMG_LO (0x10000, B/YF0x.v:37) and TFIB_IMG_END (0x5fc000, B/YF0x.v:25).
   rule 24: no function proved (kind: instance discharge of an image premise at reply's image B). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* The reply image instances first, as the cgif file takes cgif's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseAG ImgBaseDG DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfDIface.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* B/YF0x.img_cover_of_ledger's script over ALedger_cf. *)
Theorem IMG_COVER_reply : YGcfDIface.IMG_COVER.
Proof.
intros ly S md L. change (img_cover ly). split.
- destruct (alc_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _].
  cbn in H. unfold TFIB_IMG_LO. lia.
- destruct (alc_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
  cbn in H. unfold TFIB_IMG_END. lia.
Qed.

End a.
