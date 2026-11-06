(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, lane RimgA, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row img-hshb-A; a closed fact of reply's image class instance at image A,
   fuzz_reply.asan, pin 42c58610e125).

   Row HSHB (frame CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) row 39): the cf layer's premise
     Hypothesis HSHB : ag_shadow = SHADOW_OFF.
   of YGcfInstHit.v:140 (commit d2e17f315ba; also YGcfInstHitCore.v:368), stated over the layer's image class
   ImgBaseAG.AGImg.  Both names are on reply (ImgBaseAG.ag_shadow, A/ImgBaseAG.v:45; SHADOW_OFF, Reusable/YG0f.v:12),
   so the lemma below states the premise's text at reply's instances: the image class ImgBase.AImg at AImg_reply
   (A/AGif2reply.v:23) and ImgBaseAG.AGImg at AGImg_reply (A/AGif0reply.v:116), whose shadow offset is
   ag_shadow := AGis.SHBv (A/AGif0reply.v:120; AGis.SHBv := 0x7fff8000, A/AGis.v:165), the model's
   SHADOW_OFF := 0x7fff8000.  cgif's discharge: YGcfInstHitcgif.v:60 HSHB_cgif (commit cc4fb1f2a13), by eq_refl. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply ImgBaseAG AGif0reply.
Local Open Scope Z_scope.

(* HSHB (YGcfInstHit.v:140) at reply's image A: the interface's shadow offset is the model's. *)
Lemma HSHB_A : @ImgBaseAG.ag_shadow AImg_reply AGImg_reply = SHADOW_OFF.
Proof. reflexivity. Qed.
