(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-errnoword-B of a Theorem Labs lane's reply image rows, for the cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row; a closed fact of the symbol table at reply's image B,
   fuzz_reply.asan-ubsan, pin 10ffb5f9202a).

   errno_word_cf: the cf layer's unit premise `Hypothesis errno_word : YGcfReallocCompose.errno_word_cf B.`
   (YGcfInstRealloc.v:90 and YGcfInstReallocK.v:474, commit bbe791f0bb0): errno's four bytes are a 64-bit address
   range.  Reply does not carry YGcfReallocCompose yet, so the lemma states its body UNFOLDED: the statement below is
   the text of `Definition errno_word_cf : Prop := 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.`
   (YGcfReallocCompose.v:420, commit bbe791f0bb0, Section variable B), at every B with the image's symbol facts
   (im_syms of reply's image instance AImg_reply = TfibSyms, B/AGif2reply.v:28).  A consumer closes the premise with
   `exact (errno_word_cf_B B TS)`, the Definition unfolding by delta.
   Discharge (cgif's pattern): the symbol table's errno field is TFIB_ERRNO (TfibSyms's ts_errno, B/YF0m.v:874), and
   TFIB_ERRNO (B/YF0m.v:21) is a word address with four bytes below 2 ^ 64; then lia. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

(* errno_word_cf at image B (YGcfReallocCompose.errno_word_cf, unfolded). *)
Lemma errno_word_cf_B : forall B, @im_syms AImg_reply B -> 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
Proof.
intros B TS. change (TfibSyms B) in TS.
rewrite (ts_errno B TS). unfold TFIB_ERRNO.
replace (2 ^ 64) with 18446744073709551616 by (vm_compute; reflexivity).
lia.
Qed.
