(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_hshb.v (commit 4d286b2e618d, file sha256 256bbdc8bacf) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, row img-hshb-B of a Theorem Labs lane's reply image rows, for the cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row; a closed fact of the image class constants at reply's image B,
   fuzz_reply.asan-ubsan, pin 10ffb5f9202a).

   HSHB: the cf layer's unit premise `Hypothesis HSHB : ag_shadow = SHADOW_OFF.` (YGcfInstHit.v:140, commit
   d2e17f315ba; also YGcfInstHitCore.v:368), stated here at reply's image instances: the image class ImgBaseAG.AGImg at
   AGImg_cgif (B/AGif0cgif.v:116) over ImgBase.AImg at AImg_cgif (B/AGif2cgif.v:24).  Both names are reply's own
   (ImgBaseAG.v:45, Reusable/YG0f.v:12), so the text is the layer's verbatim; the instances are written out only so
   that the statement names reply's image B whatever instance search would pick.  It reads no symbol table, so the
   lemma takes no B (as cgif's packaged twin HSHB_cgif, YGcfInstHitcgif.v:60, commit cc4fb1f2a13).
   Discharge (cgif's pattern, by eq_refl): ag_shadow := AGis.SHBv at AGImg_cgif (B/AGif0cgif.v:120), and AGis.SHBv
   (B/AGis.v:166) and SHADOW_OFF (Reusable/YG0f.v:12) are the same shadow offset. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif0cgif.
Local Open Scope Z_scope.

(* HSHB at image B: the interface's shadow offset is the model's. *)
Lemma HSHB_B : @ImgBaseAG.ag_shadow AImg_cgif AGImg_cgif = SHADOW_OFF.
Proof. reflexivity. Qed.
