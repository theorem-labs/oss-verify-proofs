(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-hshb-B of a Theorem Labs lane's reply image rows, for the cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row; a closed fact of the image class constants at reply's image B,
   fuzz_reply.asan-ubsan, pin 10ffb5f9202a).

   HSHB: the cf layer's unit premise `Hypothesis HSHB : ag_shadow = SHADOW_OFF.` (YGcfInstHit.v:140, commit
   d2e17f315ba; also YGcfInstHitCore.v:368), stated here at reply's image instances: the image class ImgBaseAG.AGImg at
   AGImg_reply (B/AGif0reply.v:117) over ImgBase.AImg at AImg_reply (B/AGif2reply.v:24).  Both names are reply's own
   (ImgBaseAG.v:46, Reusable/YG0f.v:12), so the text is the layer's verbatim; the instances are written out only so
   that the statement names reply's image B whatever instance search would pick.  It reads no symbol table, so the
   lemma takes no B (as cgif's packaged twin HSHB_cgif, YGcfInstHitcgif.v:60, commit cc4fb1f2a13).
   Discharge (cgif's pattern, by eq_refl): ag_shadow := AGis.SHBv at AGImg_reply (B/AGif0reply.v:121), and AGis.SHBv
   (B/AGis.v:166) and SHADOW_OFF (Reusable/YG0f.v:12) are the same shadow offset. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseAG AGif0reply.
Local Open Scope Z_scope.

(* HSHB at image B: the interface's shadow offset is the model's. *)
Lemma HSHB_B : @ImgBaseAG.ag_shadow AImg_reply AGImg_reply = SHADOW_OFF.
Proof. reflexivity. Qed.
