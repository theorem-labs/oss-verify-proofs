(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-herr-B of a Theorem Labs lane's reply image rows, for the cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row; a closed fact of the symbol table at reply's image B,
   fuzz_reply.asan-ubsan, pin 10ffb5f9202a).

   HERR: the cf layer's unit premise `Hypothesis HERR : as_errno B = im_errno.` (YGcfInstMiss.v:242, commit
   1ad1106e381), stated here at reply's image instance: the image class ImgBase.AImg at AImg_reply (B/AGif2reply.v:24),
   for every B with the image's symbol facts (im_syms = TfibSyms, B/AGif2reply.v:28).  Both names are reply's own
   (as_errno: Reusable/YG0f.v:165; im_errno: B/ImgBase.v:32), so the text is the layer's verbatim; a consumer closes
   HERR with `exact (herr_B B TS)` (the name is the A twin herr_A's, lib/A/ReplyImg_herr.v, lane W 7cb9ea48d19).
   Discharge (cgif's pattern, AGif2cgif.v:26 + YF0m.v:297): im_errno := TFIB_ERRNO at AImg_reply (B/AGif2reply.v:26),
   and the symbol table's errno field is TFIB_ERRNO (TfibSyms's ts_errno, B/YF0m.v:874; TFIB_ERRNO, B/YF0m.v:21). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply.
Local Open Scope Z_scope.

(* HERR at image B: errno of the symbol table is the image class's errno cell. *)
Lemma herr_B : forall B, @im_syms AImg_reply B -> as_errno B = @im_errno AImg_reply.
Proof.
intros B TS. change (TfibSyms B) in TS.
rewrite (ts_errno B TS). reflexivity.
Qed.
