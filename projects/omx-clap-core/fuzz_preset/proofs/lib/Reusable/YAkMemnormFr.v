(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (c-omx-alloc, engine owner): memnorm (YAkMemnorm.v) across two run frames. rule 24: proves
   no function (kind: segment lemma). Image-free: no address, no image number.

   memnorm_frame_two: a walk whose memory moves m -> m1 under frame_of E rs1 and m1 -> m2 under frame_of E rs2
   (YP09.v), with every write window of rs1 and rs2 inside [lo, hi) below TASK_SIZE and no segment in [lo, hi), keeps
   memnorm. The proof is YAkMemnorm.memnorm_frame_off_segs: a byte off [lo, hi) is in neither window, so both frames
   keep it.
   SOURCE: h-hreply-k1's row N10-CBAA, origin/cold/h-hreply-k1-p102-N10-CBAA 8419a0f82cf, lib/A/Prog/CheckBoundedAllocA.v
   :252-256, where the same argument is inlined at the walk's 16-byte stack frame. This file states it once, generic.
   WHY A SEPARATE FILE: frame_of and in_wrange are in YP09.v, which YAkMemnorm.v's Requires do not load. This leaf
   Requires YAkMemnorm and YP09, so YAkMemnorm's closure does not grow.
   Numerals: 1 (LENGTH: find_segment's one-byte query, as in YAkMemnorm.v). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09.
Open Scope Z_scope.

Section S.
Variable segs : list Segment.

Lemma memnorm_frame_two : forall E rs1 rs2 (m m1 m2 : word -> option byte) (lo hi : Z),
  frame_of E rs1 m m1 -> frame_of E rs2 m1 m2 ->
  (forall a, in_wrange E rs1 a \/ in_wrange E rs2 a -> lo <= a < hi) ->
  hi <= TASK_SIZE ->
  (forall x : word, lo <= bv_unsigned x < hi -> find_segment segs (bv_unsigned x) 1 = None) ->
  YAkMemnorm.memnorm segs m -> YAkMemnorm.memnorm segs m2.
Proof.
intros E rs1 rs2 m m1 m2 lo hi HF1 HF2 Hwin Hhi Hseg Hm.
apply (YAkMemnorm.memnorm_frame_off_segs segs m m2 lo hi Hm); [| exact Hhi | exact Hseg].
intros x Hx.
assert (Hn1 : ~ in_wrange E rs1 (bv_unsigned x)) by (intros Hc; specialize (Hwin _ (or_introl Hc)); lia).
assert (Hn2 : ~ in_wrange E rs2 (bv_unsigned x)) by (intros Hc; specialize (Hwin _ (or_intror Hc)); lia).
rewrite (HF2 x Hn2). exact (HF1 x Hn1).
Qed.
End S.
