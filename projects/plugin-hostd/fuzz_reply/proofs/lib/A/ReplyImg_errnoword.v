(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, lane RimgA, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row img-errnoword-A; a closed fact of reply's image A, fuzz_reply.asan,
   pin 42c58610e125, read from its symbol table TfibSyms, A/AF0m.v).

   Row errno_word_cf (frame CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) row 38): the cf layer names it as the premise `errno_word` of
   YGcfInstRealloc.v:90 and YGcfInstReallocK.v:474 (lane R, commit bbe791f0bb0), at the layer's Definition
   YGcfReallocCompose.errno_word_cf (YGcfReallocCompose.v:420 at bbe791f0bb0):
     Definition errno_word_cf : Prop := 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
   The reply tree does not carry that Definition yet, so the lemmas below state its body UNFOLDED, verbatim, at
   reply's image A; a consumer closes the layer's premise with `exact` once the layer is on reply.  The layer's B is
   a Section Variable (asyms) with no symbol premise; the unit's B carries the image's symbol premise
   @im_syms AImg_reply B (the image class ImgBase.AImg at AImg_reply, A/AGif2reply.v:23; im_syms := TfibSyms, :27), so:
   - errno_word_cf_A: every B with that premise, through ts_errno (A/AF0m.v:875) and TFIB_ERRNO (A/AF0m.v:22);
   - errno_word_cf_A_TfibB: image A's closed record TfibB (A/AD2l.v:16) through TfibB_syms (A/AD2l.v:76).
   cgif's discharge pattern: YF0m.ts_errno + YF0m.TFIB_ERRNO, then lia (the idiom of cgif's A/AE6i.v:39); the
   preset twin is fuzz_preset's A/ErrnoWordA.v errno_word_cf_A (commit c8da7ddae85f). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AD2l.
Local Open Scope Z_scope.

(* errno_word_cf (YGcfReallocCompose.v:420, unfolded) at every B with image A's symbol facts. *)
Lemma errno_word_cf_A : forall B, @im_syms AImg_reply B -> 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
Proof.
intros B TS. change (TfibSyms B) in TS. rewrite (ts_errno B TS).
replace (2 ^ 64) with 18446744073709551616 by reflexivity.
unfold TFIB_ERRNO. lia.
Qed.

(* errno_word_cf (unfolded) at image A's closed record TfibB, through its TfibSyms witness. *)
Lemma errno_word_cf_A_TfibB : 0 <= as_errno AD2l.TfibB /\ as_errno AD2l.TfibB + 4 <= 2 ^ 64.
Proof. exact (errno_word_cf_A AD2l.TfibB AD2l.TfibB_syms). Qed.
